(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the second segment of the ASan walk of fuzz_reply's list_push (lane W2), the
   statement A/W_list_push_tail.v (lp_tail_stmt), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (return). *)
(* From the malloc call at 0x8515c to the return, in three runs:
   R1 the jal to malloc; malloc(n + 1) through AMA (amalloc_cf_rule, forced success through the meter);
   R2 0x85160 .. 0x851a4: the new block d into the vector slot v + 16 n, the jal to __asan_memcpy;
      __asan_memcpy(d, SRC, n) through AMEMCPY (aintrin_realizes OCpy);
   R3 0x851a8 .. 0x85258: the NUL at d + n, the length into the slot, l->n = n + 1, the epilogue and the ret.
   The two addresses computed from two atoms (v + 16 n and d + n) are named by alias facts (YP0e.v aliased2):
   the engine rewrites v + (n << 4) to atom 47 and d + n to atom 80, so no run stops on them.
   pb_lp_tail_x (Section c) is the walk over any allocator relation ARx with its laws (a Theorem Labs lane's route (b),
   step 3; CONVERSION.md (sha256 1015972e02a9; internal record)), stated as W_list_push_tail.lp_tail_stmt_x. Its Section hypotheses: PST / ARx /
   hl / LAWS (the generic relation), HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: YCbqG.ARx_shadow_law's
   premise at every state), TL (PALib), MLAW, MMAX/HMMAX, HG (gx_ok), HGR (gx_rt), IMGC / BLKN (W_kit_x.v Section g,
   for blk_off_imgP_x), CTX with HCTX_lp_malloc (the malloc call hands the rule the chain [], so its trace is the
   singleton [list_push + 0xd0]), AMA (amalloc_cf_rule_c_x) and AMEMCPY (W_sites_x.aintrin_realizes_x OCpy).
   pb_lp_tail (Section cAR) is its corollary at ARx := ARi0, PST := [].
   The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): Section c takes the room record RP; the tail pre's rp_RM RP Sc (1 + kr)
   and cnt_ok at Sc are the malloc rule's own premises, its stack room comes from the call's journal
   (W_journal_x.aj_stack_room_x), and its post's rp_RM RP S2 kr is lp_post_x's at the return. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_frame W_list_push_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- the symbolic state at the call (lane W2's walk of the segment) ----
   Atoms: 0 .. 31 the registers at the call; 32 .. 43 the caller's ra, s0 .. s10 as list_push saved them (the
   frame's slots 88 .. 0); 44 / 45 / 46 the list's v / n / cap; 47 the slot address v + 16 n.  The engine reads
   v + (n << 4) as atom 47 through the alias of lpt_facts, so the slot needs no fresh atom. *)
Definition lpt_Bx : sv := SOff 21 0.
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
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0 (2 ^ 16) 0); (18%nat, mkAF 0x10000 0x5fb000 0);
(21%nat, mkAF SB SB 0); (45%nat, mkAF 0 (2 ^ 30 - 1) 0); (47%nat, HEAPF) ] [] [lpt_alias].
Definition lpt_regs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 18 8)) 20%bv (SOff 18 12))
22%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 21 0)))
23%bv (SAlu ALU_SRL (SOff 18 0) (SLit 3)))
24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 12) (SLit 3)) (SOff 21 0)).
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
Lemma lpt_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.
(* ---- THE GENERIC WALK (route (b), step 3): the segment over any allocator relation ARx with its laws ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the room invariant and the live counts, as W_list_push_tail.v Section cx *)
Variable RP : roomp.
Variable G : list (Z * Z).
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the allocator rules' caller-context table (W_journal.v Section hc); the malloc call hands the rule the chain []
   (s0 holds LA + 8, an image address), so its trace is the singleton [its return address 0x85160 = list_push + 0xd0] *)
Variable CTX : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xd0] CTX.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Lemma lpt_inG_img : forall a, inG G a -> 0x10000 <= a < 0x5fb000.
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
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the entry at a world relation R.  The tail pre's journal is ajournal_gx_xR R
   (W_list_push_tail.lp_tail_pre_xR); the entry reads only its ARx state (ajournal_gx_AR_xR), so the proof is the
   strict one.  lpt_entry below is this lemma at R := wle (lp_tail_pre_x_wle). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Lemma lpt_entry_xR : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
lp_tail_pre_xR B PST ARx MT RP G R W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) ss_lpt
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)))
/\ sh_ok SEGS lpt_Bx lpt_SH (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) (mrestrict (w_H Wc) memc).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfr & Hmle & Hmok & _ & _ & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R10 & Hsaved & Hapk).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc HJ) as HAR.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc' & Hvec & _).
assert (Rn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
destruct Hvec as [[Hc0 _] | (Hc0 & Hin & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as (Hv16 & Hv4096 & Hvceil & Hvapp & Hvpres & _).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as Hoff.
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
assert (E21 : ew E 21 = w64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl); exact R21).
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
    all: cbn [sv_denot]; rewrite ?E18, ?E21; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite R8 | rewrite R20 | rewrite R22 | rewrite R23 | rewrite R24]; reflexivity.
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
    unfold spZ, off_img in *. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [lpt_facts f_atoms atoms_ok]. unfold afact_ok, HEAPF. cbn [af_lo af_hi af_al2].
      rewrite Usp, E9, E18, E21, E45, E47. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hsp16.
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
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E lpt_Bx 47 (hl_v lc + 16 * hl_n lc) 16 (hl_v lc + 16 * hl_n lc) 0 16).
    * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc Wc memc mdc (hl_v lc) (AREC * hl_cap lc)); [exact HAR | exact Hin | lia |].
      rewrite Hreq. lia.
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hvapp. unfold SHADOW_OFF. lia.
Qed.
End wR.
(* the strict texts are the R section's at R := wle: each R premise at wle is the strict one, and the three laws hold
   for wle *)
#[local] Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Lemma lpt_entry : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
lp_tail_pre_x B PST ARx MT RP G W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) ss_lpt
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)))
/\ sh_ok SEGS lpt_Bx lpt_SH (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) (mrestrict (w_H Wc) memc).
Proof. eapply (lpt_entry_xR (@wle SEGS)); wle_inst. Qed.
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
ARx ly2 S2 Hp2 W2 mem2 md2 -> azs B LA 16 -> 0x10000 <= LA -> LA + 16 <= 0x5fb000 ->
In (v, AREC * cap) (ablocks B ly2 S2) -> 0 <= N < cap ->
ew Ex 18 = w64 LA -> ew Ex 21 = w64 SB -> ew Ex 47 = Z_to_bv 64 (v + 16 * N) ->
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
(* YCbq.v:1946 shadow_hull_vis_of_block over ARx: ARx_shadow_law's no-hidden-head premise is HP0 *)
Lemma lpt_shvis : forall ly S Hp W mem md p m d n,
ARx ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p <= d -> d + n <= p + req_size m -> 0 < n ->
shadow_hull_vis (aview SEGS (w_H W) mem) d n.
Proof.
intros ly S Hp W mem md p m d n HAR Hin Hpd Hdn Hn s Hs.
assert (Hh0 : forall h, In h Hp -> ~ (p <= h < p + req_size m))
  by (intros h Hh; rewrite (HP0 ly S Hp W mem md HAR) in Hh; destruct Hh).
destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md p m HAR Hin Hh0) as [_ Hh]. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + req_size m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, 3, 4): the walk at a world relation R, stated as
   W_list_push_tail.lp_tail_stmt_xR (journal ajournal_gx_xR R, step relation SRrG SEGS R, post W_contract_xR.lp_post_xR R).
   The runs are the G runs (W_journal_x.paj_run_x_xG); the malloc call goes through the malloc rule at R
   (amalloc_cf_rule_c_xR at CTX), whose call-boundary premise RO at the call memory comes from the call state's ARx
   (RO_ARx; part 3c removed its memnorm premise); __asan_memcpy stays the strict AMEMCPY (W_sites_x.aj_intrin_at_xR);
   the ret is a strict step lifted by SRr_SRrG (WLE_R).  pb_lp_tail_x below is this walk at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AMA_R : amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
(* :457 pb_lp_tail_x *)
Theorem pb_lp_tail_xR : lp_tail_stmt_xR B PST ARx MT RP G R.
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr Hq Hqv HqS HqE HPRE.
destruct (lpt_entry_xR R W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE) as [HS SHOK].
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfrm & Hmle & Hmok & HRM & Hcnt & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R10 & Hsaved & Hapk & Herrc).
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
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as Hoff. rewrite Hreq in Hoff. unfold off_img in Hoff.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _).
assert (Hn0 : 0 <= Z.of_nat (length x)) by lia.
assert (Hsp : alloc_ceiling + 16384 <= spZ regs - 96 /\ spZ regs <= 2 ^ 47) by (unfold spZ in *; lia).
(* errno's four bytes: image bytes, outside the list struct (gx_rt) *)
pose proof (pal_env B TL) as (_ & HeImg & _).
assert (HER : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i) /\ 0x10000 <= as_errno B + i < 0x5fb000 /\
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
assert (E21 : ew E 21 = w64 SB) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
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
  - cbn [spine]. replace (raZ (ms_regs ms1)) with (BASE + AF_fr_list_push + 0xd0); [exact HCTX_lp_malloc|].
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
  rewrite OLDa by lia; [exact E18 | exact E21 | exact E47]. }
(* R2: the slot store, the jal to __asan_memcpy *)
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18a in Ha;
    right; left; apply HGL; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U47a in Ha. left. split; [apply HSLOT; [exact Hvin2 | lia] | lia]. }
rename HFr into HFr2, HG0 into HGr2. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem ms2) HFr2 a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18a, ?U47a; lia. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (Usp2 : spZ (ms_regs ms2) = spZ regs - 96).
{ unfold spZ. rewrite P2. rewrite OLDa by lia. rewrite E2. apply unsigned_lit_small. unfold spZ in *. lia. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2m.
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hdn) as Hdoff. rewrite Hreqd in Hdoff. unfold off_img in Hdoff.
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
  - intros Hpos. eapply (lpt_shvis ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia | exact Hpos].
  - split; [lia|]. split; [lia|]. split; [|split; [lia|]].
    + intros a Ha. split; [|rewrite Usp2; lia].
      replace a with (SRC + Z.of_nat (Z.to_nat (a - SRC))) by lia. rewrite KS by lia.
      unfold aview. rewrite (garr8_mbyte SEGS _ SRC _ (Z.to_nat (a - SRC)) Hx) by (unfold bzs; rewrite length_map; lia).
      discriminate.
    + split; [eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      intros Hpos. eapply (lpt_shvis ly2 S2 Hp2 W2 (ms_mem ms2) _ q k);
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
    rewrite OLDc, OLDb, OLDa by lia; [exact E18 | exact E21 | exact E47].
  - constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W2) mem3 Ec lpt_Bx 80 (d + Z.of_nat (length x)) 1 (d + Z.of_nat (length x)) 0 1).
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 mem3 md3 d (Z.of_nat (length x) + 1)); [exact HAR3 | exact Hdn | lia |].
      rewrite Hreqd. lia.
    + unfold U, lpt_Bx. cbn [sv_denot]. rewrite OLDc, OLDb, OLDa by lia. rewrite E21, Z.add_0_r. unfold w64.
      rewrite Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Ec80, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hdapp. unfold SHADOW_OFF. lia. }
(* R3: the NUL, the length, l->n = n + 1, the epilogue, the ret *)
paj_run_tok_xR RUNG HS HJ3 SHOK3 lpt_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U80 in Ha;
    left; split; [|lia]|].
  { replace a with (d + (a - d)) by lia.
    eapply (awr_new_block_any_xR SEGS B PST ARx LAWS (R := R) LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc Wc (ms_mem ms1) _ kc
      ly2 S2 Hp2 W2 mem2 md2 d (Z.of_nat (length x) + 1) (ablocks B ly2 S2) (a - d) ly2 [] HJi HAR2 Hbl2);
    [lia | exact Hdn | rewrite Hreqd; lia]. }
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18c in Ha;
    right; left; apply HGL; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U47c in Ha. left. split; [apply HSLOT; [exact Hvin2 | lia] | lia]. }
rename HFr into HFr3, HG0 into HGr3. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
(* ---- at the ret ---- *)
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
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
{ intros a Ha H1 H2 H3. apply (aview_kept_out _ _ (w_H W2) mem3 (ms_mem msf) HFr3 a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U80, ?U18c, ?U47c; lia. }
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
End wR.
(* ---- the walk: pb_lp_tail_xR at R := wle (wle_inst), with RO := True and the malloc rule at R from the strict AMA by
   W_journal_x.v amalloc_cf_rule_c_xR_of_x ---- *)
Theorem pb_lp_tail_x : lp_tail_stmt_x B PST ARx MT RP G.
Proof.
eapply (pb_lp_tail_xR (@wle SEGS)) with (RO := fun _ => True);
  first [ wle_inst | exact (fun _ _ _ _ _ _ _ => I) | (apply amalloc_cf_rule_c_xR_of_x; exact AMA) ].
Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_lp_tail's statement is the AR walk's,
   byte-identical, now a corollary of pb_lp_tail_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].
   Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS, and the malloc rule in
   its caller-context form (W_journal.v Section hc, amalloc_cf_rule_c at CTX) with the closed trace fact
   HCTX_lp_malloc in place of amalloc_cf_rule.  The bridges: W_list_push_tail.lp_tail_stmt_x_AR0,
   W_journal_x.amalloc_cf_rule_c_x_of_AR0 / ARi0_hp0, W_sites_x.aintrin_realizes_x_of_AR0, W_kit_x.AR_imgc / AR_blkn. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Variable CTX : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c SEGS B MT MMAX CTX.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xd0] CTX.
Theorem pb_lp_tail : lp_tail_stmt B MT G.
Proof.
apply lp_tail_stmt_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (amalloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX AMA) as AMAx.
pose proof (aintrin_realizes_x_of_AR0 SEGS B OCpy (SIGMA WS_asan_memcpy) AMEMCPY) as AMEMCPYx.
eapply pb_lp_tail_x; eassumption.
Qed.
End cAR.
End b.
End a.
