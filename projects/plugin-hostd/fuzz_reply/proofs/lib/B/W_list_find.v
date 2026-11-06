(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proves function list_find (image B) - ported structure from
   a working branch's lib/B/Prog/list_find.v (list_find_holds, Qed) and
   a working branch's lib/A/W_list_find.v (pb_list_find); not transported: different framework (SR/a_call_pre
   over AsanAllocAPI vs SRr/afn_pre over a world W; bytes_at/addressable vs aview/alist_at/range_addressable/
   shadow_hull_vis; SR over a config vs SRr SEGS W with ajournal_gx), no bridge lemma exists. *)
(* The ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's list_find at 0x86374, a NEW walk over
   lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), in the form of
   lib/A/W_list_find.v (the cgif walks proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v and lib/A/ACbk.v, the loop as
   lib/A/AC8b.v tcbb_loopX), with the B code's structure from the h-lane proof above: one loop lemma (lf_loopX) from a
   fresh symbolic state at the loop head 0x86410, by induction on the records left, exiting at 0x86488 (mv a0,s2).
   list_find(l, s, n) reads l->n and, when it is positive, l->v; then for each record i it compares the record's
   length with n and, when they agree, the record's text with the n bytes at s through the bcmp interceptor,
   returning the first i that matches, or -1.  The bcmp call is the Section hypothesis ABCMP (Reusable/YG0d.v
   abcmp_realizes; in the generic walk, its twin W_sites_x.abcmp_realizes_x).
   Loop registers (B): s0 = n, s1 = s, s2 = -1, s3 = v + 16 i, s4 = the shadow base, s5 = i, s6 = v, s7 = l->n - i,
   s8 = v + 16 i + 8, s9 = (v != 0).  UBSan is trap mode: five branches to `unimp` 0x864c0 (lib/B/W_traps.v census):
     0x863ac andi a2,a0,7; bnez   the list head's alignment: decided by the runner (atom 10 carries al2 3);
     0x86410 bltu s3,s6            pointer overflow: cited, trap_ptr_wrap_atom (s3 = v + 16 i does not wrap);
     0x8641c seqz/xor/beqz         null consistency of s3 against s9: cited, trap_null_xor_folded (the runner folds
                                   seqz s3 to 0 from s3 >= 4096; s9 = 1);
     0x86420 beqz s6               the base's null check: decided by the runner (atom 22 >= 4096);
     0x86428 andi a0,s3,7; bnez   alignment of s3: decided by the runner (atom 19 carries al2 3).
   No Section hypothesis beyond these: the generic walk pb_list_find_x takes LAWS, HP0, TL, ABCMP over ARx, as
   lib/A/W_list_find.v's does; the AR statement pb_list_find keeps B's earlier LAWS, TL, ABCMP, where A's takes LX0
   in place of LAWS (a Theorem Labs lane's ruling 03:30Z, as lib/B/W_list_drop.v Section dAR). No placement fact is needed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YN2e YO0c YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
(* route R: the leaf contract twins (a Theorem Labs lane's W_contract_leaf_xR.v, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_leaf_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* awr_ok_tac is in Reusable.YCbq and in lib/B.YCbq: name it in full *)
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ------------------------------------------------------------------ the list's cells as val_mem.
   W_rep's alist_at holds the vector's bytes as one garr8; a walk reads them eight at a time. *)
Lemma garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Section c.
Variable B : asyms.
(* Record j of a list: the text's address at v + 16 j and its length at v + 16 j + 8, as 8-byte cells. *)
Lemma alist_rec_fields : forall ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64) /\
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) 8
  (Z.of_nat (length (snd (nth j (HarnessRep.hl_recs l) (0, [])))) mod 2 ^ 64).
Proof.
intros ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply garr8_val_mem8 in H1. apply garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|]. replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.
(* a byte string held as garr8, read back through the ASan view *)
Lemma garr8_aview : forall H (m : word -> option byte) a (t : list byte) j,
garr8 SEGS (mrestrict H m) a (HarnessRep.bzs t) -> (j < length t)%nat ->
aview SEGS H m (a + Z.of_nat j) = Some (bv_unsigned (nth j t (Z_to_bv 8 0))).
Proof.
intros H m a t j Hg Hj.
assert (Hl : (j < length (HarnessRep.bzs t))%nat) by (unfold HarnessRep.bzs; rewrite length_map; exact Hj).
unfold aview. rewrite (garr8_mbyte SEGS _ a _ j Hg Hl). cbn [option_map]. f_equal.
unfold HarnessRep.bzs.
rewrite (nth_indep (map HarnessRep.bz t) 0 (HarnessRep.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. unfold HarnessRep.bz. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* bcmp's verdict on two byte strings read through one reader *)
Lemma bytes_eq_iff : forall (rd : reader) p s (t sb : list byte),
length t = length sb ->
(forall j, (j < length t)%nat -> rd (p + Z.of_nat j) = Some (bv_unsigned (nth j t (Z_to_bv 8 0)))) ->
(forall j, (j < length sb)%nat -> rd (s + Z.of_nat j) = Some (bv_unsigned (nth j sb (Z_to_bv 8 0)))) ->
((forall i, 0 <= i < Z.of_nat (length sb) -> rd (p + i) = rd (s + i)) <-> t = sb).
Proof.
intros rd p s t sb Hl Ht Hs. split.
- intros Heq. apply (nth_ext t sb (Z_to_bv 8 0) (Z_to_bv 8 0) Hl). intros j Hj.
  specialize (Heq (Z.of_nat j) ltac:(lia)). rewrite (Ht j Hj), (Hs j ltac:(lia)) in Heq.
  injection Heq as Heq. apply bv_eq. exact Heq.
- intros -> i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Ht (Z.to_nat i) ltac:(lia)), (Hs (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma req_size_ge : forall n, 0 <= n -> n <= req_size n /\ 0 < req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma st_ok_pi_sub : forall E ss ms rs,
st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hwf. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms rs HS Hs Hwf). Qed.
End c.

(* ------------------------------------------------------------------ the walk *)
Definition A_list_find : Z := AF_fr_list_find.
Definition A_list_findP : Z := BASE + AF_fr_list_find.
Definition A_lf_head : Z := AF_fr_list_find + 0x4c.   (* 0x863c0: the shadow base is in s4 *)
Definition A_lf_loop : Z := AF_fr_list_find + 0x9c.   (* 0x86410: the loop head *)
Definition A_lf_next : Z := AF_fr_list_find + 0xf8.   (* 0x8646c: the loop latch *)
Definition A_lf_exit : Z := AF_fr_list_find + 0x114.  (* 0x86488: a0 := s2, the epilogue *)
(* ---- THE GENERIC WALK (route (b), step 3; lib/A/W_list_find.v's form, commit 36b7310e084): list_find over any
   allocator relation ARx with its laws, stated as W_contract_x.lfind_spec_x.  The Section hypotheses beyond the AR
   walk's: PST / ARx / hl / LAWS (the generic relation) and HP0 (the unit's hidden-head set is empty in every ARx
   state, so the records' / vector's / text's shadow comes from W_journal_x's range_addressable_of_block_hp0_x and
   shadow_hull_vis_of_block_hp0_x).  ABCMP is bcmp's site contract over ARx (W_sites_x.abcmp_realizes_x).  The run is
   over the G-journal at G = [] (AJG); the post's journal at the caller's G is ajournal_gx_of_x. ---- *)
Section w.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* gx_ok_nil is inlined, not a Let: the walks' runs name their presence facts HG, HG0, HG1, .. with `fresh` *)
Let RUN := paj_run_x_x B PST ARx LAWS [] (gx_ok_nil SEGS B) 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS [] (gx_ok_nil SEGS B) 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the donor's journal is the G-journal of a function that writes no global and has no out cell *)
Lemma ajournal_gx_of_x : forall G STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
0 <= STK ->
AJG STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros G STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HK HJ. apply ajournal_gx_nil_x in HJ.
eapply ajournal_gx_pack_x; [exact HK | lia | rewrite !Z.add_0_r; exact HJ | apply gagree_refl | intros a Ha _; lia].
Qed.

(* the entry 0x86374.  The list head at a0 is a global that this walk cannot place apart from the GOT slot and
   the shadow cell, so the entry state holds only those two and the frame; once the shadow base is in s4 (0x863c0)
   the two image regions are dropped and the list head's region is added. *)
Definition Bx : sv := SOff 34 0.
Definition lf_regions : smem := [ stack_region LFIND_FRAME; got_regionP; bcell_regionP 34 ].
Definition lf_head_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 12 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
(* no run of this walk writes outside its own frame: every region's writable window is empty but the frame's *)
Ltac lf_nowr :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
   try change LFIND_FRAME with 96 in *; try change LFIND_STK with 8288 in *; lia | ]);
destruct Hin.

(* ------------------------------------------------------------------ the loop (0x86410 .. 0x86480).
   One record per trip: the three UBSan checks of s3 against s6 and s9, the shadow check and the load of the length
   at v + 16 i + 8, the comparison with s0, and, when they agree, the shadow check and the load of the text pointer
   at v + 16 i and the bcmp call. *)
Definition LF_PHI : Z := 140737479966720.
(* the registers the loop may change, and the ones it keeps *)
Definition LF_CLOB : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 23; 24; 28; 29; 30; 31]%bv.
Definition LF_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 20; 22; 25; 26; 27]%bv.
Lemma lf_clob_kept : forall r : bv 5, reg_in r LF_CLOB = false -> r = 0%bv \/ In r LF_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
(* the registers a run inside one trip leaves alone (it writes only a0..a2, ra and the caller-saved ones) *)
Definition LF_LKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* what the walk knows about record q: its two cells in the vector, its block, and its bytes *)
Definition lf_rec_ok (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(V : Z) (recs : list (Z * list byte)) (q : nat) : Prop :=
val_mem SEGS (mrestrict (w_H W) memc) (V + 16 * Z.of_nat q) 8 (fst (nth q recs (0, []))) /\
val_mem SEGS (mrestrict (w_H W) memc) (V + 16 * Z.of_nat q + 8) 8
  (Z.of_nat (length (snd (nth q recs (0, []))))) /\
In (fst (nth q recs (0, [])), Z.of_nat (length (snd (nth q recs (0, [])))) + 1) (ablocks B lyc Sc) /\
garr8 SEGS (mrestrict (w_H W) memc) (fst (nth q recs (0, [])))
  (HarnessRep.bzs (snd (nth q recs (0, [])) ++ [Z_to_bv 8 0])).
(* the loop head's seat (W_traps.v recipe R1-R4): pointers s3, s6, s8 with mkAF 4096 LF_PHI 3, the one-time flag
   s9 = 1, the shadow base s4 = SB, the counters' int32 ranges, and the record's two cells as atoms 32 (text
   pointer) and 33 (length) of one region at s8 *)
Definition BxL : sv := SOff 20 0.
Definition lfl_regions : smem :=
[ YP09.mkRegion (Some 24%nat) (-8) 8 0 0
  [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition lfl_facts : facts :=
mkFacts [ (8%nat, mkAF 0 (2 ^ 32 - 1) 0); (19%nat, mkAF 4096 LF_PHI 3); (20%nat, mkAF SB SB 0);
(21%nat, mkAF 0 (2 ^ 31) 0); (22%nat, mkAF 4096 LF_PHI 3); (23%nat, mkAF 1 (2 ^ 31) 0);
(24%nat, mkAF 4096 LF_PHI 3); (25%nat, mkAF 1 1 0);
(32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 47) 0) ] [] [].
Definition ss_lfl : sstate := mkSS A_lf_loop sr_atoms lfl_regions None lfl_facts.
Definition lfl_SH : list shent := [ mkSHE 19 8 16; mkSHE 19 0 8 ].
Definition lfl_extra (p L : Z) : list word := map (Z_to_bv 64) [p; L].
Lemma lf_loop_entry : forall W lyc Sc Hpc (regs : bvmap 5 word) memc mdc V cap i nn p L lsb,
ARx lyc Sc Hpc W memc mdc ->
In (V, cap) (ablocks B lyc Sc) -> 16 * nn <= req_size cap ->
0 <= i < nn -> nn < 2 ^ 30 ->
getr regs 8 = w64 lsb -> 0 <= lsb < 2 ^ 32 ->
getr regs 19 = w64 (V + 16 * i) -> getr regs 20 = w64 SB -> getr regs 21 = w64 i -> getr regs 22 = w64 V ->
getr regs 23 = w64 (nn - i) -> getr regs 24 = w64 (V + 16 * i + 8) -> getr regs 25 = w64 1 ->
val_mem SEGS (mrestrict (w_H W) memc) (V + 16 * i) 8 p -> 0 <= p < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) memc) (V + 16 * i + 8) 8 L -> 0 <= L < 2 ^ 47 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lfl_extra p L))) ss_lfl
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) memc (seg_rom SEGS)))
/\ sh_ok SEGS BxL lfl_SH (Eimg (Ereg regs (lfl_extra p L))) (mrestrict (w_H W) memc).
Proof.
intros W lyc Sc Hpc regs memc mdc V cap i nn p L lsb HAR HVin HVn Hi Hnn H8 Hlsb H19 H20 H21 H22 H23 H24 H25
Mp Rp ML RL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc V cap HAR HVin) as (HV16 & HV4096 & HVceil & HVia & _ & _).
assert (V8 : V = 8 * (V / 8)).
{ pose proof (Z.div_mod V 16 ltac:(lia)) as D. rewrite HV16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (V / 16)) with ((2 * (V / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (M0 : V mod 8 = 0) by (rewrite V8 at 1; rewrite Z.mul_comm; apply Z_mod_mult).
assert (M1 : (V + 16 * i) mod 8 = 0).
{ rewrite V8 at 1. replace (8 * (V / 8) + 16 * i) with ((V / 8 + 2 * i) * 8) by ring. apply Z_mod_mult. }
assert (M2 : (V + 16 * i + 8) mod 8 = 0).
{ rewrite V8 at 1. replace (8 * (V / 8) + 16 * i + 8) with ((V / 8 + 2 * i + 1) * 8) by ring. apply Z_mod_mult. }
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lfl_extra p L))). pose proof pa_B_ok as HBASE.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E8 : ew E 8 = Z_to_bv 64 lsb) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E19 : ew E 19 = Z_to_bv 64 (V + 16 * i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 V) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 (nn - i)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 (V + 16 * i + 8)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 1) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 p)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 L)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HBx : U E BxL = SHADOW_OFF)
by (unfold BxL; rewrite (U_atom E 20 SB E20) by (unfold SB; lia); reflexivity).
split.
- unfold ss_lfl. apply pa_entry_st_ok_full.
+ subst E. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lfl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E24, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  * apply (chunk_ok_val SEGS E _ (V + 16 * i + 8) (-8) 8 (SOff 32 0) p);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (V + 16 * i + 8 + -8) with (V + 16 * i) by lia. exact Mp.
  * apply (chunk_ok_val SEGS E _ (V + 16 * i + 8) 0 8 (SOff 33 0) L);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact ML.
+ cbn [pairwise_disjoint all_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
  cbn [lfl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E19, E20, E21, E22, E23, E24, E25, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert M0 M1 M2 HV4096 HVceil HVn Hi Hnn Hlsb Rp RL C1. clear. unfold LF_PHI, SB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
- unfold sh_ok, lfl_SH. constructor; [|constructor; [|constructor]].
+ eapply shent_ok_of_range.
  * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc V cap (V + 16 * i + 8) 8 HAR HVin); lia.
  * exact HBx.
  * rewrite (U_atom E 19 _ E19) by lia. reflexivity.
  * lia.
  * lia.
  * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
+ eapply shent_ok_of_range.
  * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc V cap (V + 16 * i) 8 HAR HVin); lia.
  * exact HBx.
  * rewrite (U_atom E 19 _ E19) by lia. reflexivity.
  * lia.
  * lia.
  * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* what the loop leaves at 0x86488: the journal, the callee-saved registers it keeps, every byte outside the frame,
   presence, and s2 = the first matching index, or -1 when no record matches. *)
Definition lf_exit_post (sp0 : Z) (FP : list (Z * Z)) ly S Hp (W0 : world SEGS) mem0 md0 own lyc Sc Hpc (kk : Z)
(W : world SEGS) (regs0 : bvmap 5 word) (memc : word -> option byte) (l : HarnessRep.hlist) (sb : list byte)
: world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_lf_exit)) mem' (seg_rom SEGS)) md' /\
AJG LFIND_STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' kk /\
(forall r, In r LF_KEPT -> getr regs' r = getr regs0 r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - LFIND_STK <= a < sp0 - 96) ->
 aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
((exists j, lfind_match l sb j /\ getr regs' 18 = w64 (Z.of_nat j)) \/
 ((forall q, (q < length (HarnessRep.hl_recs l))%nat -> snd (nth q (HarnessRep.hl_recs l) (0, [])) <> sb) /\
  getr regs' 18 = Z_to_bv 64 (-1))).
(* the model the loop reads: the vector's block, its records, and the bytes bcmp compares them with *)
Definition lf_model (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(V cap : Z) (l : HarnessRep.hlist) (sb : list byte) (src : Z) : Prop :=
In (V, cap) (ablocks B lyc Sc) /\ 16 * Z.of_nat (length (HarnessRep.hl_recs l)) <= req_size cap /\
(forall q, (q < length (HarnessRep.hl_recs l))%nat -> lf_rec_ok lyc Sc W memc V (HarnessRep.hl_recs l) q) /\
(forall j, 0 <= j < Z.of_nat (length sb) ->
 aview SEGS (w_H W) memc (src + j) = Some (bv_unsigned (nth (Z.to_nat j) sb (Z_to_bv 8 0)))) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF src (Z.of_nat (length sb)) /\
(0 < Z.of_nat (length sb) -> shadow_hull_vis (aview SEGS (w_H W) memc) src (Z.of_nat (length sb))).
(* every fact the loop reads lives below alloc_ceiling, so a step that keeps those bytes keeps the model *)
Lemma lf_model_kept : forall lyc Sc Hpc W mdc memc memc' V cap l sb src sp0,
ARx lyc Sc Hpc W memc mdc ->
0 <= src -> src + Z.of_nat (length sb) <= 2 ^ 63 -> amem_range src (Z.of_nat (length sb)) ->
(forall a, src <= a < src + Z.of_nat (length sb) -> ~ (sp0 - LFIND_STK <= a < sp0)) ->
alloc_ceiling + LFIND_STK <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - LFIND_STK <= a < sp0) ->
 aview SEGS (w_H W) memc' a = aview SEGS (w_H W) memc a) ->
lf_model lyc Sc W memc V cap l sb src -> lf_model lyc Sc W memc' V cap l sb src.
Proof.
intros lyc Sc Hpc W mdc memc memc' V cap l sb src sp0 HAR Hsrc0 Hsrc63 Hmr Hoff HLOsp HEQ
(HVin & HVn & HRECS & HSB & HRA & HHV).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs47 : src + Z.of_nat (length sb) <= 2 ^ 47)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc V cap HAR HVin) as (_ & HV4096 & HVceil & _ & _ & _).
split; [exact HVin|]. split; [exact HVn|]. split.
- intros q Hq. destruct (HRECS q Hq) as (M1 & M2 & Hin & Hg).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (req_size_ge (Z.of_nat (length (snd (nth q (HarnessRep.hl_recs l) (0, [])))) + 1) ltac:(lia)) as Hrq.
  assert (Hql : 16 * Z.of_nat q + 16 <= 16 * Z.of_nat (length (HarnessRep.hl_recs l))) by lia.
  split; [|split; [|split; [exact Hin|]]].
  + apply (val_mem_kept SEGS (w_H W) (w_H W) memc memc'); [intros kk Hk; apply HEQ; lia | exact M1].
  + apply (val_mem_kept SEGS (w_H W) (w_H W) memc memc'); [intros kk Hk; apply HEQ; lia | exact M2].
  + apply (garr8_frame SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) memc')); [exact Hg|].
    intros a Ha. apply (mbyte_of_aview SEGS).
    unfold HarnessRep.bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply HEQ; lia.
- split; [intros j Hj; rewrite HEQ by (first [lia | apply Hoff; lia]); apply HSB; lia|]. split.
  + intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite HEQ; [exact Hs| |]; unfold shadow_of_addr, SHADOW_OFF in *;
    assert (0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]); lia.
  + intros Hpos s Hs. rewrite HEQ; [apply (HHV Hpos); exact Hs| |];
    unfold shadow_addr, SHADOW_OFF in Hs;
    assert (H1 : 0 <= src / 8) by (apply Z.div_pos; lia);
    assert (H2 : 0 <= (src + Z.of_nat (length sb) - 1) / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]);
    assert (H3 : 0 <= (2147450880 + src / 8) / 8) by (apply Z.div_pos; lia);
    pose proof (Z.mul_div_le (2147450880 + (src + Z.of_nat (length sb) - 1) / 8) 8 ltac:(lia)) as H4;
    lia.
Qed.
(* the loop's claim at pc, with record i the next one to look at *)
Definition lf_claim (pc i V cap : Z) (l : HarnessRep.hlist) (sb : list byte) (src sp0 : Z)
(FP : list (Z * Z)) ly S Hp (W0 : world SEGS) mem0 md0 own lyc Sc Hpc (W : world SEGS) (kk : Z) : Prop :=
forall (regs : bvmap 5 word) memc mdc,
AJG LFIND_STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc kk ->
lf_model lyc Sc W memc V cap l sb src ->
(forall q, (q < Z.to_nat i)%nat -> snd (nth q (HarnessRep.hl_recs l) (0, [])) <> sb) ->
spZ regs = sp0 - 96 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 (Z.of_nat (length sb)) -> getr regs 9 = w64 src ->
getr regs 18 = Z_to_bv 64 (-1) ->
getr regs 19 = w64 (V + 16 * i) -> getr regs 20 = w64 SB -> getr regs 21 = w64 i -> getr regs 22 = w64 V ->
getr regs 23 = w64 (Z.of_nat (length (HarnessRep.hl_recs l)) - i) ->
getr regs 24 = w64 (V + 16 * i + 8) -> getr regs 25 = w64 1 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc)
(lf_exit_post sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc kk W regs memc l sb).

(* the latch 0x8646c: step to the next record, or leave the loop *)
Definition lfn_facts : facts := mkFacts [ (20%nat, mkAF SB SB 0); (23%nat, mkAF 1 (2 ^ 31) 0) ] [] [].
Definition ss_lfn : sstate := mkSS A_lf_next sr_atoms [] None lfn_facts.
Definition lfn_extra : list word := [].
(* the registers the latch leaves alone and the loop's claims read *)
Definition LF_TKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 22; 25; 26; 27]%bv.
(* sgtz a0,a1; neg a0,a0; and s7,a0,a1 (0x863f8 .. 0x86400): s7 = l->n when l->n > 0 *)
Lemma lf_sgtz_and : forall n, 0 < n < 2 ^ 31 ->
alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (w64 n))) (w64 n) = w64 n.
Proof.
intros n Hn. unfold w64.
rewrite (zalu64_sound ALU_SLT).
assert (H1 : zalu64 ALU_SLT 0 n = 1).
{ unfold zalu64, zcanon, M64. cbn [zalu_raw]. change (0 mod 2 ^ 64) with 0.
  rewrite (Z.mod_small n (2 ^ 64)) by lia.
  rewrite (swrap64_id 0), (swrap64_id n) by (unfold half64; lia).
  destruct (Z.ltb_spec 0 n); [reflexivity | lia]. }
rewrite H1, zalu64_sound.
assert (H2 : zalu64 ALU_SUB 0 1 = 2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite H2, zalu64_sound. f_equal.
unfold zalu64, zcanon, M64. cbn [zalu_raw].
rewrite (Z.mod_small (2 ^ 64 - 1) (2 ^ 64)) by lia. rewrite (Z.mod_small n (2 ^ 64)) by lia.
change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite !(Z.mod_small n (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma addiw_one : forall i, 0 <= i -> i + 1 < 2 ^ 31 ->
sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (i + 1).
Proof.
intros i H0 H1. apply bv_eq. rewrite YO0c.sext64_32_unsigned, YO0c.alu32_add_unsigned, !low32_unsigned_mod.
rewrite !unsigned_lit_small by lia. change M32 with (2 ^ 32).
rewrite (Z.mod_small i), (Z.mod_small 1), (Z.mod_small (i + 1)) by lia.
unfold sx32. rewrite Z.mod_small by lia. destruct (Z.ltb_spec (i + 1) (2 ^ 31)); [reflexivity | lia].
Qed.
Lemma lf_tailX : forall i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk,
0 <= i < Z.of_nat (length (HarnessRep.hl_recs l)) -> Z.of_nat (length (HarnessRep.hl_recs l)) < 2 ^ 30 ->
V = HarnessRep.hl_v l -> 0 <= src -> src + Z.of_nat (length sb) <= 2 ^ 63 ->
amem_range src (Z.of_nat (length sb)) ->
(forall a, src <= a < src + Z.of_nat (length sb) -> ~ (sp0 - LFIND_STK <= a < sp0)) ->
snd (nth (Z.to_nat i) (HarnessRep.hl_recs l) (0, [])) <> sb ->
(i + 1 < Z.of_nat (length (HarnessRep.hl_recs l)) ->
 lf_claim A_lf_loop (i + 1) V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk) ->
lf_claim A_lf_next i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk.
Proof.
intros i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk Hi Hn HV Hsrc0 Hsrc63 Hmr Hoff Hnm IH
regs memc mdc HJ HM HPREV Hsp H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HVin & HVn & HRECS & HSRCb & HSRCra & HSRChv).
assert (HAR : ARx lyc Sc Hpc W memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof HJ as HJn. apply ajournal_gx_nil_x in HJn.
destruct HJn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLOsp : alloc_ceiling + LFIND_STK <= sp0) by (unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc V cap HAR HVin) as (HV16 & HV4096 & HVceil & _ & _ & _).
set (E := Eimg (Ereg regs lfn_extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E19 : ew E 19 = Z_to_bv 64 (V + 16 * i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat (length (HarnessRep.hl_recs l)) - i))
by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 (V + 16 * i + 8)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (HS : st_ok_pi SEGS VAL E ss_lfn (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_lf_next)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lfn. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [lfn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E23, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. revert Hi Hn. clear. unfold SB. intros. repeat split; lia. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs lfn_extra) E)
by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold A_lf_next.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. }
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
by (intros a Ha; apply (aview_kept_out E _ (w_H W) memc (ms_mem ms) HFr a Ha); lf_nowr).
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* another record left *)
rewrite branch_ne_U, (U_atom_off E 23 _ (-1) E23), U_lit in Hc by lia.
assert (Hlt : i + 1 < Z.of_nat (length (HarnessRep.hl_recs l)))
by (destruct (Z.eqb_spec (Z.of_nat (length (HarnessRep.hl_recs l)) - i + -1) 0); [discriminate | lia]).
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan A_lf_loop. { apply awr_ok_x_of0; awr_any. }
prreg HS (19%bv : bv 5) N19. prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(lf_nowr)).
  apply MEQ; exact Ha. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LF_TKEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
rewrite E19, unsigned_lit_small in N19 by lia. rewrite E21, (addiw_one i) in N21 by lia.
rewrite E23, unsigned_lit_small in N23 by lia. rewrite E24, unsigned_lit_small in N24 by lia.
pmkst HS.
unfold lf_claim, A_lf_loop in IH.
eapply SRr_mono.
{ eapply (IH Hlt (ms_regs ms0) (ms_mem ms0) _).
  - exact HJ.
  - exact (lf_model_kept lyc Sc Hpc W mdc memc (ms_mem ms0) V cap l sb src sp0 HAR Hsrc0 Hsrc63 Hmr Hoff HLOsp
      (fun a Ha _ => MEQ2 a Ha) HM).
  - intros q Hq. destruct (Nat.lt_ge_cases q (Z.to_nat i)) as [Hqi | Hqi]; [exact (HPREV q Hqi)|].
    assert (q = Z.to_nat i) by lia. subst q. exact Hnm.
  - unfold spZ in *. rewrite (HK 2%bv ltac:(cbv; tauto)). exact Hsp.
  - rewrite (HK 3%bv ltac:(cbv; tauto)). exact H3.
  - rewrite (HK 4%bv ltac:(cbv; tauto)). exact H4.
  - rewrite (HK 8%bv ltac:(cbv; tauto)). exact H8.
  - rewrite (HK 9%bv ltac:(cbv; tauto)). exact H9.
  - rewrite (HK 18%bv ltac:(cbv; tauto)). exact H18.
  - rewrite N19. unfold w64. f_equal. lia.
  - rewrite (HK 20%bv ltac:(cbv; tauto)). exact H20.
  - rewrite N21. reflexivity.
  - rewrite (HK 22%bv ltac:(cbv; tauto)). exact H22.
  - rewrite N23. unfold w64. f_equal. lia.
  - rewrite N24. unfold w64. f_equal. lia.
  - rewrite (HK 25%bv ltac:(cbv; tauto)). exact H25. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & HKEEP3 & HPRES3 & HRES3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split.
{ intros r Hr. rewrite (HK3 r Hr). apply HK. revert Hr. cbv [LF_KEPT LF_TKEPT In]. tauto. }
split.
{ intros a Ha Hno. rewrite (HKEEP3 a Ha Hno). apply MEQ2; exact Ha. }
split.
{ intros a Hap. apply HPRES3. apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). exact Hap. }
exact HRES3.
-
(* the last record: leave the loop *)
rewrite branch_ne_U, (U_atom_off E 23 _ (-1) E23), U_lit in Hc by lia.
assert (Hend : i + 1 = Z.of_nat (length (HarnessRep.hl_recs l)))
by (destruct (Z.eqb_spec (Z.of_nat (length (HarnessRep.hl_recs l)) - i + -1) 0); [lia | discriminate]).
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan A_lf_exit. { apply awr_ok_x_of0; awr_any. }
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(lf_nowr)).
  apply MEQ; exact Ha. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LF_TKEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|]. split.
{ intros r Hr. apply HK. revert Hr. cbv [LF_KEPT LF_TKEPT In]. tauto. }
split; [intros a Ha Hno; apply MEQ2; exact Ha|]. split.
{ intros a Hap. apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). exact Hap. }
right. split.
{ intros q Hq. destruct (Nat.lt_ge_cases q (Z.to_nat i)) as [Hqi | Hqi]; [exact (HPREV q Hqi)|].
  assert (q = Z.to_nat i) by lia. subst q. exact Hnm. }
rewrite (HK 18%bv ltac:(cbv; tauto)). exact H18.
Qed.

(* the loop head 0x86410, by induction on the records left *)
Lemma lf_loopX : forall (k : nat) i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk,
Z.of_nat k = Z.of_nat (length (HarnessRep.hl_recs l)) - i ->
0 <= i < Z.of_nat (length (HarnessRep.hl_recs l)) ->
Z.of_nat (length (HarnessRep.hl_recs l)) < 2 ^ 30 ->
V = HarnessRep.hl_v l ->
0 <= src -> src + Z.of_nat (length sb) <= 2 ^ 63 -> Z.of_nat (length sb) < 2 ^ 32 ->
amem_range src (Z.of_nat (length sb)) ->
(forall a, src <= a < src + Z.of_nat (length sb) -> ~ (sp0 - LFIND_STK <= a < sp0)) ->
lf_claim A_lf_loop i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk.
Proof.
induction k as [|k IHk];
intros i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk Hk Hi Hn HV Hsrc0 Hsrc63 Hsb32 Hmr Hoff;
[intros; exfalso; lia|].
intros regs memc mdc HJ HM HPREV Hsp H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HVin & HVn & HRECS & HSB & HRA & HHV).
assert (HAR : ARx lyc Sc Hpc W memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof HJ as HJn. apply ajournal_gx_nil_x in HJn.
destruct HJn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLO : alloc_ceiling + LFIND_STK <= sp0) by (unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc V cap HAR HVin) as (HV16 & HV4096 & HVceil & _ & _ & _).
destruct (HRECS (Z.to_nat i) ltac:(lia)) as (Mp & ML & Hpin & Hg).
rewrite Z2Nat.id in Mp, ML by lia.
set (RC := nth (Z.to_nat i) (HarnessRep.hl_recs l) (0, [])) in *.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hpin) as (_ & Hp4096 & Hpceil & _ & _ & _).
pose proof (req_size_ge (Z.of_nat (length (snd RC)) + 1) ltac:(lia)) as Hrq.
destruct (lf_loop_entry W lyc Sc Hpc regs memc mdc V cap i (Z.of_nat (length (HarnessRep.hl_recs l)))
  (fst RC) (Z.of_nat (length (snd RC))) (Z.of_nat (length sb))
  HAR HVin HVn Hi Hn H8 ltac:(lia) H19 H20 H21 H22 H23 H24 H25 Mp ltac:(lia) ML ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lfl_extra (fst RC) (Z.of_nat (length (snd RC)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; rewrite HE; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (exact (EEo 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EEo 3%nat 3%bv eq_refl); exact H3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EEo 4%nat 4%bv eq_refl); exact H4).
assert (E8 : ew E 8 = Z_to_bv 64 (Z.of_nat (length sb))) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 src) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 (-1)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (V + 16 * i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 V) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat (length (HarnessRep.hl_recs l)) - i))
by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 (V + 16 * i + 8)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 1) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 (fst RC))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (snd RC))))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (lfl_extra (fst RC) (Z.of_nat (length (snd RC))))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold A_lf_loop.
(* 0x86410 bltu s3,s6 -> unimp: UBSan's pointer-overflow trap; s3 = v + 16 i does not wrap (R5: cited) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ rewrite (trap_ptr_wrap_atom E 19 22 V (16 * i) E19 E22 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc. discriminate. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. }
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
by (intros a Ha; apply (aview_kept_out E _ (w_H W) memc (ms_mem ms) HFr a Ha); lf_nowr).
(* 0x8641c beqz (s9 xor seqz s3) -> unimp: UBSan's null-consistency trap; the runner folded seqz s3 to 0 (s3 >= 4096),
   s9 = 1.  The next two traps (0x86420 beqz s6, 0x86428 andi s3,7; bnez) and the shadow check of v + 16 i + 8 the
   runner decides from the seat's facts and lfl_SH. *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ rewrite (trap_null_xor_folded E 25 E25) in Hc0. discriminate. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. }
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(lf_nowr)).
  apply MEQ; exact Ha. }
(* 0x86444 bne a0,s0: the record's length against n *)
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* the lengths differ: record i cannot be the one *)
assert (Hnm : snd RC <> sb).
{ rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 8 _ E8) in Hc1 by lia.
  apply (proj1 (Bool.negb_true_iff _)) in Hc1. apply Z.eqb_neq in Hc1.
  intros Heq. apply Hc1. rewrite Heq. reflexivity. }
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan A_lf_next. { apply awr_ok_x_of0; awr_any. }
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha ltac:(lf_nowr)).
  apply MEQ1; exact Ha. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LF_LKEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
pmkst HS.
eapply SRr_mono.
{ assert (IHc : i + 1 < Z.of_nat (length (HarnessRep.hl_recs l)) ->
    lf_claim A_lf_loop (i + 1) V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk).
  { intros Hlt. apply (IHk (i + 1) V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk);
    [lia | lia | exact Hn | exact HV | exact Hsrc0 | exact Hsrc63 | exact Hsb32 | exact Hmr | exact Hoff]. }
  eapply (lf_tailX i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk Hi Hn HV Hsrc0 Hsrc63
    Hmr Hoff Hnm IHc (ms_regs ms1) (ms_mem ms1) _).
  - exact HJ.
  - exact (lf_model_kept lyc Sc Hpc W mdc memc (ms_mem ms1) V cap l sb src sp0 HAR Hsrc0 Hsrc63 Hmr Hoff HLO
      (fun a Ha _ => MEQ2 a Ha) HM).
  - exact HPREV.
  - unfold spZ in *. rewrite (HK 2%bv ltac:(cbv; tauto)). exact Hsp.
  - rewrite (HK 3%bv ltac:(cbv; tauto)). exact H3.
  - rewrite (HK 4%bv ltac:(cbv; tauto)). exact H4.
  - rewrite (HK 8%bv ltac:(cbv; tauto)). exact H8.
  - rewrite (HK 9%bv ltac:(cbv; tauto)). exact H9.
  - rewrite (HK 18%bv ltac:(cbv; tauto)). exact H18.
  - rewrite (HK 19%bv ltac:(cbv; tauto)). exact H19.
  - rewrite (HK 20%bv ltac:(cbv; tauto)). exact H20.
  - rewrite (HK 21%bv ltac:(cbv; tauto)). exact H21.
  - rewrite (HK 22%bv ltac:(cbv; tauto)). exact H22.
  - rewrite (HK 23%bv ltac:(cbv; tauto)). exact H23.
  - rewrite (HK 24%bv ltac:(cbv; tauto)). exact H24.
  - rewrite (HK 25%bv ltac:(cbv; tauto)). exact H25. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & HKEEP3 & HPRES3 & HRES3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split.
{ intros r Hr. rewrite (HK3 r Hr). apply HK. revert Hr. cbv [LF_KEPT LF_LKEPT In]. tauto. }
split.
{ intros a Ha Hno. rewrite (HKEEP3 a Ha Hno). apply MEQ2; exact Ha. }
split.
{ intros a Hap. apply HPRES3. apply (apresent_grows (w_H W) (ms_mem ms0) (ms_mem ms1) a HG1).
  apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). exact Hap. }
exact HRES3.
-
(* the lengths agree: compare the bytes with bcmp *)
assert (Hlen : Z.of_nat (length (snd RC)) = Z.of_nat (length sb)).
{ rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 8 _ E8) in Hc1 by lia.
  apply (proj1 (Bool.negb_false_iff _)) in Hc1. apply Z.eqb_eq in Hc1. exact Hc1. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. }
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha ltac:(lf_nowr)).
  apply MEQ1; exact Ha. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (Usp0 : spZ (ms_regs ms1) = sp0 - 96) by (unfold spZ; rewrite P2, E2; exact Hsp).
pose proof HJ as HAR0. apply ajournal_gx_AR_x in HAR0.
pose proof (lf_model_kept lyc Sc Hpc W mdc memc (ms_mem ms1) V cap l sb src sp0 HAR Hsrc0 Hsrc63 Hmr Hoff HLO
  (fun a Ha _ => MEQ2 a Ha) HM) as HM0.
pose proof HM0 as (_ & _ & HRECS0 & HSB0 & HRA0 & HHV0).
destruct (HRECS0 (Z.to_nat i) ltac:(lia)) as (Mp0 & ML0 & Hpin0 & Hg0).
rewrite Z2Nat.id in Mp0, ML0 by lia.
(* 0x86464 jal __interceptor_trampoline_bcmp, returning to 0x86468 = BASE + 0x4124 *)
eapply SRr_bind.
{ eapply (aj_bcmp_gx_at_x B PST ARx LAWS (SIGMA WS_bcmp) ABCMP [] 0 [] W (ms_regs ms1) (ms_mem ms1) LFIND_STK sp0
    FP ly S Hp W0 mem0 md0 own lyc Sc Hpc _ kk (fst RC) src (Z.of_nat (length sb)) (-96)
    (Z_to_bv 64 (BASE + 16676)) (gx_ok_nil SEGS B) ltac:(reflexivity) HJ).
  - rewrite P10, E32. reflexivity.
  - rewrite P11, E9. reflexivity.
  - rewrite P12, E8. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Usp0.
  - reflexivity.
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite P3, E3. reflexivity.
  - rewrite P4, E4. reflexivity.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + replace a with (fst RC + Z.of_nat (Z.to_nat (a - fst RC))) by lia.
      rewrite (garr8_aview (w_H W) (ms_mem ms1) (fst RC) (snd RC ++ [Z_to_bv 8 0])
        (Z.to_nat (a - fst RC)) Hg0 ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + rewrite Usp0. unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia.
  - intros a Ha. split.
    + replace a with (src + (a - src)) by lia. rewrite HSB0 by lia. discriminate.
    + rewrite Usp0. intros [HA HB]. apply (Hoff a ltac:(lia)).
      unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia.
  - intros a Ha. unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia.
  - intros a Ha. intros [HA HB]. apply (Hoff a ltac:(lia)).
    unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia.
  - apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS lyc Sc Hpc W (ms_mem ms1) _ (fst RC)
      (Z.of_nat (length (snd RC)) + 1) (fst RC) (Z.of_nat (length sb)) HAR0 Hpin0); lia.
  - exact Hmr.
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W (ms_mem ms1) _ (fst RC)
      (Z.of_nat (length (snd RC)) + 1) (fst RC) (Z.of_nat (length sb)) HAR0 Hpin0); lia.
  - intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W (ms_mem ms1) _ (fst RC)
      (Z.of_nat (length (snd RC)) + 1) (fst RC) (Z.of_nat (length sb)) HAR0 Hpin0); lia.
  - exact HRA0.
  - exact HHV0. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfrc & Hpresc).
jafter_call_keep_pi HS 35%nat regs3 (mrestrict (w_H W) mem3) HP3 ([] : list nat) HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m)
by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (lfl_extra (fst RC) (Z.of_nat (length (snd RC))))) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOK2 : sh_ok SEGS BxL [] Ea (mrestrict (w_H W) mem3)) by constructor.
prreg HS (10%bv : bv 5) R10v. rewrite Hv in R10v.
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - LFIND_STK <= a < sp0 - 96) ->
aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hno. rewrite (Hfrc a Ha ltac:(unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia)).
  apply MEQ2; exact Ha. }
assert (PRESC : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem3 a).
{ intros a Hap. apply Hpresc. apply (apresent_grows (w_H W) (ms_mem ms0) (ms_mem ms1) a HG1).
  apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). exact Hap. }
paj_run_tok_x RUN HS HJ3 SHOK2 Bspan. { apply awr_ok_x_of0; awr_any. }
assert (E39 : ew Ea 39 = Z_to_bv 64 (bv_unsigned v))
by (rewrite <- R10v, Z_to_bv_bv_unsigned; reflexivity).
pose proof (bv_unsigned_in_range 64 v) as RV. change (bv_modulus 64) with (2 ^ 64) in RV.
assert (HBYT : forall jn, (jn < length (snd RC))%nat ->
aview SEGS (w_H W) (ms_mem ms1) (fst RC + Z.of_nat jn) =
Some (bv_unsigned (nth jn (snd RC) (Z_to_bv 8 0)))).
{ intros jn Hjn.
  rewrite (garr8_aview (w_H W) (ms_mem ms1) (fst RC) (snd RC ++ [Z_to_bv 8 0]) jn Hg0
    ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth1 by lia. reflexivity. }
assert (HBYS : forall jn, (jn < length sb)%nat ->
aview SEGS (w_H W) (ms_mem ms1) (src + Z.of_nat jn) = Some (bv_unsigned (nth jn sb (Z_to_bv 8 0)))).
{ intros jn Hjn. rewrite (HSB0 (Z.of_nat jn) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
assert (HLN : length (snd RC) = length sb) by lia.
(* 0x86468 beqz a0: bcmp's verdict *)
psrr_branch_tok RUN BR HS SHOK2 Bspan.
+
(* bcmp said equal: record i is the answer *)
assert (Hvz : v = w64 0).
{ rewrite branch_eq_U, (U_atom Ea 39 _ E39), U_lit in Hc2 by lia.
  apply Z.eqb_eq in Hc2. apply bv_eq. rewrite Hc2. reflexivity. }
assert (Hmatch : snd RC = sb).
{ apply (proj1 (bytes_eq_iff (aview SEGS (w_H W) (ms_mem ms1)) (fst RC) src (snd RC) sb HLN HBYT HBYS)).
  intros j Hj. exact (proj1 Hcmp Hvz j ltac:(lia)). }
paj_run_to_tok_x RUNTO HS HJ3 SHOK2 Bspan A_lf_exit. { apply awr_ok_x_of0; awr_any. }
assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. rewrite (aview_kept_out Ea _ (w_H W) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(lf_nowr)).
  apply (aview_kept_out Ea _ (w_H W) mem3 (ms_mem ms2) HFr2 a Ha); lf_nowr. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LF_KEPT HS HAEa ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (18%bv : bv 5) R18. rewrite OLDa, E21 in R18 by (cbv; lia).
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HK|]. split.
{ intros a Ha Hno. rewrite MEQ4 by exact Ha. apply KEEPC; [exact Ha | exact Hno]. }
split.
{ intros a Hap. apply (apresent_grows (w_H W) (ms_mem ms2) (ms_mem ms3) a HG3).
  apply (apresent_grows (w_H W) mem3 (ms_mem ms2) a HG2). apply PRESC. exact Hap. }
left. exists (Z.to_nat i). split.
{ unfold lfind_match. split; [lia|]. split; [exact Hmatch|].
  intros q Hq. exact (HPREV q Hq). }
rewrite R18. unfold w64. f_equal. lia.
+
(* bcmp said different: record i is not the answer *)
assert (Hnm : snd RC <> sb).
{ intros Heq. rewrite branch_eq_U, (U_atom Ea 39 _ E39), U_lit in Hc2 by lia.
  apply Z.eqb_neq in Hc2. apply Hc2.
  assert (Hvz : v = w64 0).
  { apply (proj2 Hcmp). intros j Hj. rewrite <- Heq in HBYS.
    replace j with (Z.of_nat (Z.to_nat j)) by lia.
    rewrite (HBYT (Z.to_nat j) ltac:(lia)), (HBYS (Z.to_nat j) ltac:(lia)). reflexivity. }
  rewrite Hvz. reflexivity. }
paj_run_to_tok_x RUNTO HS HJ3 SHOK2 Bspan A_lf_next. { apply awr_ok_x_of0; awr_any. }
assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. rewrite (aview_kept_out Ea _ (w_H W) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(lf_nowr)).
  apply (aview_kept_out Ea _ (w_H W) mem3 (ms_mem ms2) HFr2 a Ha); lf_nowr. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LF_LKEPT HS HAEa ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (MEQ5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - LFIND_STK <= a < sp0 - 96) ->
aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) memc a)
by (intros a Ha Hno; rewrite MEQ4 by exact Ha; apply KEEPC; [exact Ha | exact Hno]).
pmkst HS.
assert (IHc : i + 1 < Z.of_nat (length (HarnessRep.hl_recs l)) ->
  lf_claim A_lf_loop (i + 1) V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk).
{ intros Hlt. apply (IHk (i + 1) V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk);
  [lia | lia | exact Hn | exact HV | exact Hsrc0 | exact Hsrc63 | exact Hsb32 | exact Hmr | exact Hoff]. }
eapply SRr_mono.
{ eapply (lf_tailX i V cap l sb src sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W kk Hi Hn HV Hsrc0 Hsrc63
    Hmr Hoff Hnm IHc (ms_regs ms3) (ms_mem ms3) _).
  - exact HJ3.
  - apply (lf_model_kept lyc Sc Hpc W mdc memc (ms_mem ms3) V cap l sb src sp0 HAR Hsrc0 Hsrc63 Hmr Hoff HLO);
    [intros a Ha Hno; apply MEQ5; [exact Ha | unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia] | exact HM].
  - exact HPREV.
  - unfold spZ in *. rewrite (HK 2%bv ltac:(cbv; tauto)). exact Hsp.
  - rewrite (HK 3%bv ltac:(cbv; tauto)). exact H3.
  - rewrite (HK 4%bv ltac:(cbv; tauto)). exact H4.
  - rewrite (HK 8%bv ltac:(cbv; tauto)). exact H8.
  - rewrite (HK 9%bv ltac:(cbv; tauto)). exact H9.
  - rewrite (HK 18%bv ltac:(cbv; tauto)). exact H18.
  - rewrite (HK 19%bv ltac:(cbv; tauto)). exact H19.
  - rewrite (HK 20%bv ltac:(cbv; tauto)). exact H20.
  - rewrite (HK 21%bv ltac:(cbv; tauto)). exact H21.
  - rewrite (HK 22%bv ltac:(cbv; tauto)). exact H22.
  - rewrite (HK 23%bv ltac:(cbv; tauto)). exact H23.
  - rewrite (HK 24%bv ltac:(cbv; tauto)). exact H24.
  - rewrite (HK 25%bv ltac:(cbv; tauto)). exact H25. }
cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & HK4 & HKEEP4 & HPRES4 & HRES4).
split; [reflexivity|]. exists regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split.
{ intros r Hr. rewrite (HK4 r Hr). apply HK. revert Hr. cbv [LF_KEPT LF_LKEPT In]. tauto. }
split.
{ intros a Ha Hno. rewrite (HKEEP4 a Ha Hno). apply MEQ5; [exact Ha | exact Hno]. }
split.
{ intros a Hap. apply HPRES4. apply (apresent_grows (w_H W) (ms_mem ms2) (ms_mem ms3) a HG3).
  apply (apresent_grows (w_H W) mem3 (ms_mem ms2) a HG2). apply PRESC. exact Hap. }
exact HRES4.
Qed.

Definition lf_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 kLowMemEnd 3); (32%nat, mkAF 0 (2 ^ 64 - 1) 0);
(33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF SB SB 0) ] [] [].
Definition ss_lf : sstate := mkSS A_list_find sr_atoms lf_regions None lf_facts.
Definition lf_SH : list shent := [ mkSHE 10 0 16 ].
Definition lf_extra (V n : Z) : list word := map (Z_to_bv 64) [V; n; SB].
Lemma lf_entry : forall W ly S Hp regs mem md ch LA V n,
afn_pre_x SEGS B ARx LFIND_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA -> LA mod 8 = 0 -> 4096 <= LA -> LA + 16 <= kLowMemEnd ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF LA 16 ->
0 <= V < 2 ^ 64 -> 0 <= n < 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_extra V n))) ss_lf
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_findP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx lf_SH (Eimg (Ereg regs (lf_extra V n))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA V n HPRE H10 HLA8 HLA4 HLAk HLAra RV Rn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LFIND_STK = 8288) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_extra V n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_lf, A_list_findP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lf_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [unfold LFIND_FRAME; lia|]. split; [unfold LFIND_FRAME; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LFIND_FRAME in Ho. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold lf_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, LFIND_FRAME. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SB, kLowMemEnd in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HLA8 HLA4 HLAk RV Rn. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lf_SH. constructor; [|constructor].
eapply shent_ok_of_range.
+ exact HLAra.
+ unfold U, Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold kLowMemEnd in *; lia). reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

Theorem pb_list_find_x : forall G, lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Proof.
intros G W ly S Hp regs mem md ch LA l lines src sb HPRE H10 H11 H12 HLA HLA8 HLA4 HLAk HLAra HLAoff
Hsrc0 Hsrc63 Hsb32 HSRC HSRCoff HSRCmr HSRCra HSRChv.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : LFIND_STK = 8288) by reflexivity.
pose proof HLA as (HMv & HMn & _ & _ & Hncap & Hvcap & _).
set (V := HarnessRep.hl_v l) in *. set (n := Z.of_nat (length (HarnessRep.hl_recs l))).
assert (Hn : 0 <= n < 2 ^ 30) by (unfold HarnessRep.hl_n in Hncap; subst n; lia).
assert (RV : 0 <= V < 2 ^ 64).
{ destruct Hvcap as [(_ & ->) | (Hc0 & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_ge (AREC * HarnessRep.hl_cap l) ltac:(unfold AREC; lia)) as Hrq. unfold AREC in *. lia. }
change (HarnessRep.hl_n l) with n in HMn.
destruct (lf_entry W ly S Hp regs mem md ch LA V n HPRE H10 HLA8 HLA4 HLAk HLAra RV ltac:(lia)) as [HS SHOK].
unfold A_list_findP in HS.
assert (HJ : AJG LFIND_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx LFIND_STK [] ly S Hp W regs mem md ch HPRE)).
remember (Eimg (Ereg regs (lf_extra V n))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 src) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat (length sb))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (lf_extra V n)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_fr_list_find)) with (Z_to_bv 64 (BASE + AF_fr_list_find)).
(* the prologue, the list head's alignment trap 0x863ac (decided: atom 10 carries al2 3) and the load of the
   shadow base *)
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_list_find + 0x4c). { apply awr_ok_x_of0; awr_any. exact Usp. }
(* the run wrote only the frame *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LFIND_FRAME <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem ss_lf lf_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; unfold stack_region, got_regionP, bcell_regionP in Hr;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
(* swap the GOT slot and the shadow cell for the list head *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss _ =>
  let r0 := eval vm_compute in (firstn 1 (ss_mem ss)) in
  pose proof (st_ok_pi_sub Ev ss _ r0 HS ltac:(cbn [ss_mem]; submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS1. clear HS. rename HS1 into HS.
(* the list head's own region, over the memory the prologue left *)
assert (MLA : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP0; [unfold kLowMemEnd in *; lia|].
  intros Hin. apply (HLAoff a Ha). unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia. }
unfold arm in HMv, HMn.
assert (MV2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) LA 8 V)
by (apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [intros k Hk; apply MLA; lia | exact HMv]).
assert (MN2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (LA + 8) 4 n)
by (apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [intros k Hk; apply MLA; lia | exact HMn]).
assert (HLAb : base_val E (Some 10%nat) = LA)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; unfold kLowMemEnd in *; lia).
pose proof (st_ok_pi_add_region E _ _ lf_head_region HS ltac:(vm_compute; reflexivity)) as HS2.
cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS2.
match type of HS2 with ?P1 -> ?P2 -> _ =>
assert (HP1 : P1); [|assert (HP2 : P2); [|specialize (HS2 HP1 HP2); clear HP1 HP2]] end.
{ unfold lf_head_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite HLAb. split; [unfold kLowMemEnd in *; lia|]. split; [unfold kLowMemEnd in *; lia|].
  split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ LA 0 8 (SOff 32 0) V);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact MV2.
  - apply (chunk_ok_val SEGS E _ LA 8 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN2]. }
{ apply all_disjoint_of_extents. unfold lf_head_region, stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite HLAb. cbn [base_val]. rewrite Usp.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HLA4 HLAk. clear.
  unfold kLowMemEnd, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. split; [lia | exact I]. }
clear HS. rename HS2 into HS.
assert (HSX : bv_signed (sv_denot E (SExt true 32 (SOff 33 0))) = n).
{ assert (HU : bv_unsigned (sv_denot E (SExt true 32 (SOff 33 0))) = n).
  { rewrite U_sext32', (den_atom0 E 33 n E33 ltac:(lia)), unsigned_lit_small by lia.
    unfold sx32. rewrite (Z.mod_small n (2 ^ 32)) by lia. destruct (Z.ltb_spec n (2 ^ 31)); lia. }
  rewrite bv_signed_small by (rewrite HU; lia). exact HU. }
assert (HS0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
(* to the blez on l->n (0x863dc), past the shadow check of l->n (decided from lf_SH) *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* l->n <= 0: no record, the answer is -1 *)
assert (Hn0 : n = 0).
{ cbn [branch_taken] in Hc. rewrite bv_lts_signed, HSX, HS0 in Hc.
  apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc. lia. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
assert (Hlen0 : length (HarnessRep.hl_recs l) = 0%nat) by (unfold n in Hn0; lia).
assert (HM1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LFIND_FRAME <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
    rewrite (aview_kept_out E rs (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha ltac:(lf_nowr)) end.
  lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
    rewrite (aview_kept_out E rs (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(lf_nowr)) end.
  exact (KEEP0 a Ha Hno). }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold lfind_post_x.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply ajournal_gx_of_x; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (lf_extra V n) HS); [exact HAE | vm_compute; reflexivity] end.
+ intros a Hap. cbn [ms_mem].
  apply (apresent_grows (w_H W) (ms_mem ms0) (ms_mem ms1) a HG1).
  apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) mem (ms_mem ms) a HG). exact Hap.
+ intros a Ha Hno. cbn [ms_mem]. apply KEEP1; [exact Ha|].
  unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia.
+ right. split; [intros k Hk; exfalso; lia | cbn [ms_regs]; rewrite R10; exact HM1].

-
(* 0 < l->n: the vector is a live block and the loop runs *)
assert (Hnpos : 0 < n).
{ cbn [branch_taken] in Hc. rewrite bv_lts_signed, HSX, HS0 in Hc.
  apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc. exact Hc. }
destruct Hvcap as [(Hc0 & _) | (Hcpos & HVin & Hjlen & HVb)]; [unfold HarnessRep.hl_n in Hncap; lia|].
(* 0x863e0 .. 0x8640c: the shadow check of l->v (decided), s5 = 0, s6 = l->v, s7 = (l->n > 0 ? l->n : 0),
   s8 = v + 8, s9 = (v != 0), s3 = v *)
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan A_lf_loop. { apply awr_ok_x_of0; awr_any. exact Usp. }
prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
(* the register values at the loop head, for i = 0 *)
assert (SXn : sext 64 (bv_extract 0 32 (ew E 33)) = w64 n).
{ assert (Hd : sext 64 (bv_extract 0 32 (ew E 33)) = sv_denot E (SExt true 32 (SOff 33 0)))
  by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  rewrite Hd. apply bv_eq. rewrite U_sext32'.
  change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)).
  rewrite (U_atom E 33 _ E33) by lia. unfold sx32. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec n (2 ^ 31)); [|lia]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HVbnd : 4096 <= V /\ V + 16 * n <= alloc_ceiling).
{ destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md V (AREC * HarnessRep.hl_cap l) HAR HVin)
    as (_ & H4 & Hc' & _ & _ & _).
  pose proof (req_size_ge (AREC * HarnessRep.hl_cap l) ltac:(unfold AREC; lia)) as Hrq.
  unfold HarnessRep.hl_n in Hncap. unfold AREC in *. lia. }
destruct HVbnd as (HV0 & HVc).
rewrite Usp in T2. rewrite E12 in T8. rewrite E11 in T9. rewrite E32 in T19, T22.
rewrite E34 in T20. rewrite E32, unsigned_lit_small in T24 by lia.
rewrite SXn, (lf_sgtz_and n) in T23 by lia.
rewrite E32, (trap_w_snez V) in T25 by lia.
assert (HM1x : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity).
rewrite HM1x in T18.
(* the loop's model, at the memory the entry left *)
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LFIND_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  rewrite (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha ltac:(lf_nowr)).
  rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(lf_nowr)).
  apply KEEP0; [exact Ha | unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia]. }
assert (HLO : alloc_ceiling + LFIND_STK <= spZ regs) by (unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia).
assert (HMmem : lf_model ly S W mem V (AREC * HarnessRep.hl_cap l) l sb src).
{ split; [exact HVin|]. split; [unfold AREC in *; unfold HarnessRep.hl_n in Hncap;
    pose proof (req_size_ge (16 * HarnessRep.hl_cap l) ltac:(lia)); lia|]. split.
  - intros q Hq. destruct (alist_rec_fields B ly S W mem LA l lines q HLA Hq) as (Mq1 & Mq2).
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HLA)))))))) as HFall.
    pose proof (proj1 (Forall_forall _ _) HFall (nth q (HarnessRep.hl_recs l) (0, []))
      (nth_In _ (0, []) Hq)) as (Hin & Hgq & _ & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & Hq4 & Hqc & _ & _ & _).
    pose proof (req_size_ge (Z.of_nat (length (snd (nth q (HarnessRep.hl_recs l) (0, [])))) + 1)
      ltac:(lia)) as Hrq.
    unfold lf_rec_ok. unfold arm in Mq1, Mq2, Hgq.
    rewrite (Z.mod_small (fst (nth q (HarnessRep.hl_recs l) (0, [])))) in Mq1 by lia.
    rewrite (Z.mod_small (Z.of_nat (length (snd (nth q (HarnessRep.hl_recs l) (0, [])))))) in Mq2 by lia.
    split; [exact Mq1|]. split; [exact Mq2|]. split; [exact Hin | exact Hgq].
  - split; [intros j Hj; apply HSRC; exact Hj|]. split; [exact HSRCra | exact HSRChv]. }
assert (HM1 : lf_model ly S W (ms_mem ms1) V (AREC * HarnessRep.hl_cap l) l sb src).
{ apply (lf_model_kept ly S Hp W md mem (ms_mem ms1) V (AREC * HarnessRep.hl_cap l) l sb src (spZ regs)
    HAR Hsrc0 Hsrc63 HSRCmr HSRCoff HLO KEEPL HMmem). }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ([3; 4]%bv) HS HAE ltac:(vm_compute; reflexivity)) as HKT.
cbn [ms_regs restrict] in HKT.
pmkst HS.
eapply SRr_bind.
{
  eapply (lf_loopX (Z.to_nat n) 0 V (AREC * HarnessRep.hl_cap l) l sb src (spZ regs) ([] : list (Z * Z))
    ly S Hp W mem md ([] : list (Z * Z)) ly S Hp W 0 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl
    Hsrc0 Hsrc63 Hsb32 HSRCmr HSRCoff (ms_regs ms1) (ms_mem ms1) _).
  - exact HJ.
  - exact HM1.
  - intros q Hq. exfalso. lia.
  - unfold spZ in *. rewrite T2. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite (HKT 3%bv ltac:(cbv; tauto)). exact Hgp.
  - rewrite (HKT 4%bv ltac:(cbv; tauto)). exact Htp.
  - exact T8.
  - exact T9.
  - exact T18.
  - rewrite T19. unfold w64. f_equal. lia.
  - exact T20.
  - rewrite T21. reflexivity.
  - exact T22.
  - rewrite T23. unfold w64. f_equal. lia.
  - rewrite T24. unfold w64. f_equal. lia.
  - exact T25. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & MEQ3 & HPRES3 & HRES3).
(* back at 0x86488 with s2 holding the answer: splice the loop's result and run the epilogue *)
jafter_stretch_pi HS 35%nat regs3 (mrestrict (w_H W) mem3) LF_CLOB A_lf_exit HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. destruct (lf_clob_kept r0 Hr0) as [-> | Hin];
  [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; unfold lf_head_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E10, unsigned_lit_small
    by (unfold kLowMemEnd in *; lia).
    + intros a Ha. apply (mbyte_of_aview SEGS). apply MEQ3;
      unfold LFIND_STK, LFIND_FRAME, ESTACK, kLowMemEnd in *; lia.
    + intros a Ha. lia.
  - split; unfold stack_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply MEQ3;
      unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia.
    + intros a Ha _. apply (apresent_writable SEGS).
      pose proof HJ3 as HJn. apply ajournal_gx_nil_x in HJn.
      destruct HJn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
      apply HPR3. unfold LFIND_STK, LFIND_FRAME, ESTACK in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs3) LF_CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDb : forall m, (m < 35)%nat -> ew Eb m = ew E m)
by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs (lf_extra V n)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEb.
assert (Usp3 : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by (cbv; lia); exact Usp).
assert (SHOK3 : sh_ok SEGS Bx [] Eb (mrestrict (w_H W) mem3)) by constructor.
prreg HS (18%bv : bv 5) S18.
paj_run_tok_x RUN HS HJ3 SHOK3 Bspan. { apply awr_ok_x_of0; awr_any. exact Usp3. }
prreg HS (10%bv : bv 5) R10f. prreg HS (1%bv : bv 5) R1f.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold lfind_post_x. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1f; rewrite OLDb by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply ajournal_gx_of_x; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ3.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (lf_extra V n) HS); [exact HAEb | vm_compute; reflexivity] end.
+ intros a Hap. cbn [ms_mem].
  apply (apresent_grows (w_H W) mem3 (ms_mem ms2) a HG2). apply HPRES3.
  apply (apresent_grows (w_H W) (ms_mem ms0) (ms_mem ms1) a HG1).
  apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG0).
  apply (apresent_grows (w_H W) mem (ms_mem ms) a HG). exact Hap.
+ intros a Ha Hno. cbn [ms_mem].
  rewrite (aview_kept_out Eb _ (w_H W) mem3 (ms_mem ms2) HFr2 a Ha ltac:(lf_nowr)).
  rewrite (MEQ3 a Ha ltac:(unfold LFIND_STK, LFIND_FRAME, ESTACK in *; lia)).
  apply KEEPL; [exact Ha | exact Hno].
+ cbn [ms_regs]. rewrite R10f, <- S18.
  destruct HRES3 as [(j & Hmj & Hj) | (Hno & Hm1)]; [left; exists j; split; [exact Hmj | exact Hj] |].
  right. split; [exact Hno | exact Hm1].
Qed.

(* ---- route R (group G7-leaf-AB, for a Theorem Labs lane's top_x at R): pb_list_find_x at a world relation R, a LIFT with no
   re-proof.  The strict SRr run becomes SRrG SEGS R by SRr_SRrG (WLE_R), and the post's G-journal
   (lfind_post_x -> lfind_post_xR) goes to R by W_journal_x.ajournal_gx_xR_mono; W_contract_leaf_xR.v
   lfind_spec_xR_of_x is those two steps.  The callee bcmp stays at its strict contract (ABCMP). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Theorem pb_list_find_xR : forall G, lfind_spec_xR B PST ARx R G (BASE + AF_fr_list_find).
Proof. intros G. apply (lfind_spec_xR_of_x B PST ARx R WLE_R). exact (pb_list_find_x G). Qed.
End wR.
End w.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3): pb_list_find's Theorem line and Section hypotheses are the
   AR walk's (LAWS : AR_laws stays; a Theorem Labs lane's ruling 03:30Z: the plain names keep their B-old statements, as
   lib/B/W_list_drop.v's Section dAR does), now a corollary of pb_list_find_x at ARx := ARi0 (cgif's AR with the head
   set empty), PST := [].  The proof derives LX0 (the laws at ARi0) from LAWS by lib/B/YLX0.v lx_AR_laws_x_ARi0_of;
   ABCMP becomes the generic one at ARi0 through W_sites_x.abcmp_realizes_x_of_AR0; HP0 at ARi0 is ARi0_hp0; the
   bridge is W_contract_x.lfind_spec_x_AR0. ---- *)
Section wAR.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Theorem pb_list_find : forall G, lfind_spec B G (BASE + AF_fr_list_find).
Proof.
intros G. apply lfind_spec_x_AR0.
pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (abcmp_realizes_x_of_AR0 SEGS B (SIGMA WS_bcmp) ABCMP) as ABCMPx.
eapply pb_list_find_x; eassumption.
Qed.
End wAR.
End b.
End a.
