(* check_round_trip (fs.asan 0x81a9c, build A), WALK LANE D2: segments 34-39, from the boundary crt_INV_822ac (the
   return of fuzz_free (file), 0x822ac) to crt_INV_T (the return of free (same), 0x82354, the tail's entry; the tail
   crt_tail is PROVED from crt_INV_T in lib/A/FSH_crt_segD.v).

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_stdefs.v:549-611 (the stage cuts St19..St24,
   the same six calls at the same pcs), check_round_trip_sd19.v / sd20.v (the two pj_free steps),
   check_round_trip_sd21.v / sd22.v (the two fuzz_free steps), check_round_trip_sd23.v / sd24.v (the two free thunks),
   and check_round_trip_sdglue.v:612 crt_keep_blk / :659 crt_spared_blk (what a freeing call keeps)). The checker's
   CONFIRM on that hit is quoted in the lane head (internal path); the
   function-level rule-24 line it names is the one carried by lib/A/FSH_crt_base.v.
   The port RESTATES those stages in S0's form: d25a984c903 states a stage as `crt_tail ... -> SR ... (POST ...)` over
   its own heap record (AsanAllocAPI, a_call_pre / a_call_post, ledgers Lam), S0 states the walk as
   `crt_from ss_next INV_next -> crt_from ss_cur INV_cur` over ajournal / ARU / U (FSH_crt_base.v). No bridge between
   the two forms is built: each stage's CONTENT (which block each call frees, which bytes it keeps, why the fake
   frame and the real stack survive it) is re-derived here against S0's contracts.

   The six calls, MEASURED (capstone over fuzz_state.asan, sha256 64b53ff86172...):
     0x822b0  jal pj_free     (a0 = s2  = F + 0x140, &back)   returns 0x822b4   d25a984c903 St19
     0x822b8  jal pj_free     (a0 = s10 = F + 0x20,  &doc)    returns 0x822bc   d25a984c903 St20
     0x82338  jal fuzz_free   (a0 = s9  = back)               returns 0x8233c   d25a984c903 St21
     0x82340  jal fuzz_free   (a0 = [s1 + 0x30] = text)       returns 0x82344   d25a984c903 St22
     0x82348  jal __wrap_free (a0 = [s1 + 0x38] = want)       returns 0x8234c   d25a984c903 St23
     0x82350  jal __wrap_free (a0 = s8  = same)               returns 0x82354   d25a984c903 St24
   The boundary states crt_ss34 .. crt_ssT, the two pj_free runs (crt_seg34_run / crt_seg35_run) and segment 36's run
   (crt_seg36_run, the 31 shadow stores) are already in lib/A/FSH_crt_segD.v; this file adds segments 37, 38 and 39's
   runs and the CALL-SITE PRECONDITION of each of the six calls.

   U AT EACH FREE (the point of the lane). fs's two allocators poison a 16-byte head per block and the matching free
   disowns it, so the walk's poison set U shrinks at a free; the plain interceptor blocks (want, same: __wrap_malloc
   at 0x81ca4 / 0x81cb8) never had a head. afree_realizesU's range premise - every range of U lies OUTSIDE the freed
   block - is therefore discharged at a crt free site by FSupoisonU.ARU_free_outside once the freed block's own head
   is not in U, which is crtD2_free_outside below. The two pj_free and two fuzz_free calls take that premise inside
   their own statements (fuzz_free_spec names the split U = U1 ++ (p - HEAD, HEAD) :: U2); the two __wrap_free thunks
   take it here, at want and same, where it holds because those two blocks carry NO head at all.

   SK is an EXPLICIT Section variable (as FSH_crt_base.v and FSH_crt_segD.v): build A's instance
   AE2k.tfib_sink_head is passed by whoever instantiates the lane; this file never Imports AE2k. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame
FSW_frame3 FSW_K3 FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site FSH_crt_segD.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the three runs this lane adds (MEASURED by the engine over crt_tbl) ================= *)
(* segment 37: 0x8233c `ld a0, 0x30(s1)` (the s1 slot that holds text, crt_cs1's chunk 0x30 = atom 48) and the
   `jal fuzz_free` at 0x82340, returning to 0x82344 *)
Definition crt_ss37_ff : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 8%N A_fuzz_free crt_ss37).
Lemma crtD2_seg37_run_eq : sym_run_toN tfibsegs crt_tbl 8%N A_fuzz_free crt_ss37 = (crt_ss37_ff, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss37_ff_regs :
  ss_pc crt_ss37_ff = A_fuzz_free /\ ss_resv crt_ss37_ff = None /\
  ss_mem crt_ss37_ff = ss_mem crt_ss37 /\
  sr_get (ss_regs crt_ss37_ff) 10%bv = SOff 48 0 /\ sr_get (ss_regs crt_ss37_ff) 1%bv = SLit 0x82344 /\
  sr_get (ss_regs crt_ss37_ff) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss37_ff) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss37_ff) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss37_ff) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss37_ff) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss37_ff) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* segment 38: 0x82344 `ld a0, 0x38(s1)` (the slot that holds want, atom 49) and the `jal __wrap_free` at 0x82348,
   returning to 0x8234c *)
Definition crt_ss38_fr : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 8%N PC_free crt_ss38).
Lemma crtD2_seg38_run_eq : sym_run_toN tfibsegs crt_tbl 8%N PC_free crt_ss38 = (crt_ss38_fr, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss38_fr_regs :
  ss_pc crt_ss38_fr = PC_free /\ ss_resv crt_ss38_fr = None /\
  ss_mem crt_ss38_fr = ss_mem crt_ss38 /\
  sr_get (ss_regs crt_ss38_fr) 10%bv = SOff 49 0 /\ sr_get (ss_regs crt_ss38_fr) 1%bv = SLit 0x8234c /\
  sr_get (ss_regs crt_ss38_fr) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss38_fr) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss38_fr) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss38_fr) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss38_fr) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss38_fr) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* segment 39: 0x8234c `mv a0, s8` (same, atom 24) and the `jal __wrap_free` at 0x82350, returning to 0x82354 = the
   tail's entry crt_ssT *)
Definition crt_ss39_fr : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 8%N PC_free crt_ss39).
Lemma crtD2_seg39_run_eq : sym_run_toN tfibsegs crt_tbl 8%N PC_free crt_ss39 = (crt_ss39_fr, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss39_fr_regs :
  ss_pc crt_ss39_fr = PC_free /\ ss_resv crt_ss39_fr = None /\
  ss_mem crt_ss39_fr = ss_mem crt_ss39 /\
  sr_get (ss_regs crt_ss39_fr) 10%bv = SOff 24 0 /\ sr_get (ss_regs crt_ss39_fr) 1%bv = SLit 0x82354 /\
  sr_get (ss_regs crt_ss39_fr) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss39_fr) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss39_fr) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss39_fr) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss39_fr) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss39_fr) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* the two pj_free call sites, from FSH_crt_segD.v's runs: a0 = s2 (atom 18 = &back) at 0x822b0 and a0 = s10
   (atom 26 = &doc) at 0x822b8; here with the register facts crt_after_call also needs *)
Lemma crtD2_ss34_pf_regs :
  ss_pc crt_ss34_pf = A_pj_free /\ ss_resv crt_ss34_pf = None /\ ss_mem crt_ss34_pf = ss_mem crt_ss34 /\
  sr_get (ss_regs crt_ss34_pf) 10%bv = SOff 18 0 /\ sr_get (ss_regs crt_ss34_pf) 1%bv = SLit 0x822b4 /\
  sr_get (ss_regs crt_ss34_pf) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss34_pf) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss34_pf) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss34_pf) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss34_pf) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss34_pf) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ss35_pf_regs :
  ss_pc crt_ss35_pf = A_pj_free /\ ss_resv crt_ss35_pf = None /\ ss_mem crt_ss35_pf = ss_mem crt_ss35 /\
  sr_get (ss_regs crt_ss35_pf) 10%bv = SOff 26 0 /\ sr_get (ss_regs crt_ss35_pf) 1%bv = SLit 0x822bc /\
  sr_get (ss_regs crt_ss35_pf) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss35_pf) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss35_pf) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss35_pf) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss35_pf) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss35_pf) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
(* segment 36's call site (0x82338, a0 = s9 = atom 25 = back); its run WRITES (the 31 shadow stores), so its memory
   is not crt_ss36's *)
Lemma crtD2_ss36_ff_regs :
  ss_pc crt_ss36_ff = A_fuzz_free /\ ss_resv crt_ss36_ff = None /\
  sr_get (ss_regs crt_ss36_ff) 10%bv = SOff 25 0 /\ sr_get (ss_regs crt_ss36_ff) 1%bv = SLit 0x8233c /\
  sr_get (ss_regs crt_ss36_ff) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss36_ff) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss36_ff) 4%bv = SOff 4 0 /\ sr_get (ss_regs crt_ss36_ff) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crt_ss36_ff) 9%bv = SOff 9 0 /\ sr_get (ss_regs crt_ss36_ff) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================= the lane's stack room ================= *)
(* every callee of this lane fits under crt's own window with the 208 bytes of crt's realigned frame to spare
   (crt_sp1 >= spZ (c_regs cx) - 208, FSW_K.fsw_realign_facts) *)
Lemma crtD2_stk_pj_free : STK_pj_free 2 + 208 <= STK_check_round_trip.
Proof. vm_compute. discriminate. Qed.
Lemma crtD2_stk_fuzz_free : STK_fuzz_free + 208 <= STK_check_round_trip.
Proof. vm_compute. discriminate. Qed.
Lemma crtD2_stk_free : ASTACK + 208 <= STK_check_round_trip.
Proof. vm_compute. discriminate. Qed.
Lemma crtD2_stk_pos : 0 <= STK_pj_free 2 /\ 0 <= STK_fuzz_free /\ 0 <= ASTACK.
Proof. repeat split; vm_compute; discriminate. Qed.

(* ================= U and the blocks at a free ================= *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- an entry of a pairwise-disjoint list of ranges occurs ONCE ----
   Both lists the lane reasons about are pairwise disjoint: U (FSupoison.upoison_ok's second conjunct) and the live
   blocks mapped to their ranges (AR_blocks_law's pairwise clause). So a range that occurs in one part of a
   decomposition does not occur in the other - which is what turns a boundary invariant's `Permutation X (L1 ++ L2)`
   into the two `~ In` facts a free site needs. ---- *)
Lemma crtD2_disj_once : forall (l : list (Z * Z)) x,
  pairwise zdisjoint l -> 0 < snd x -> ~ (exists l1 l2, l = l1 ++ x :: l2 /\ In x (l1 ++ l2)).
Proof.
intros l x PW Hx (l1 & l2 & -> & Hin).
apply in_app_or in Hin as [Hin|Hin]; apply in_split in Hin as (a & c & E).
- subst l1. pose proof (YCbq.pairwise_In2 zdisjoint _ x x a c l2 PW ltac:(rewrite <- app_assoc; reflexivity)) as D.
  unfold zdisjoint in D. lia.
- subst l2. pose proof (YCbq.pairwise_In2 zdisjoint _ x x l1 a c PW eq_refl) as D.
  unfold zdisjoint in D. lia.
Qed.
Lemma crtD2_perm_not_in : forall (l l1 l2 : list (Z * Z)) x,
  pairwise zdisjoint l -> Permutation l (l1 ++ l2) -> 0 < snd x -> In x l2 -> ~ In x l1.
Proof.
intros l l1 l2 x PW HP Hx Hin2 Hin1.
pose proof (FSupoisonU.pairwise_zdisjoint_perm l (l1 ++ l2) HP PW) as PW'.
apply in_split in Hin2 as (a & c & ->).
rewrite app_assoc in PW'.
apply (crtD2_disj_once ((l1 ++ a) ++ x :: c) x); [exact PW' | exact Hx|].
exists (l1 ++ a), c. split; [reflexivity|].
apply in_or_app. left. apply in_or_app. left. exact Hin1.
Qed.

(* ---- the head of a block the walk is about to free is not in U, so every range of U lies outside that block ----
   the second half is FSupoisonU.ARU_free_outside; this is the shape the lane uses it in. ---- *)
Lemma crtD2_free_outside : forall ly S U (W : world tfibsegs) mem md p n,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (p, n) (ablocks B ly S) -> ~ In (p, 16) U ->
  forall r, In r U -> fst r + snd r <= p \/ p + req_size n <= fst r.
Proof.
intros ly S U W mem md p n HARU FH Hin Hnot.
exact (FSupoisonU.ARU_free_outside tfibsegs B LAWS ly S U W mem md p n HARU FH Hin Hnot).
Qed.
(* a head of U names a live block of 16 bytes or more at its address; so if the block at p is shorter than a head,
   or if (p, 16) is not one of the invariant's listed heads, (p, 16) is not in U *)
Lemma crtD2_head_of_U : forall ly S U p, FSupoisonU.fs_heads B ly S U -> In (p, 16) U ->
  exists m, In (p, m) (ablocks B ly S) /\ 16 <= req_size m.
Proof.
intros ly S U p FH Hin. destruct (FH (p, 16) Hin) as (_ & m & Hm & Hreq). exists m. split; [exact Hm | exact Hreq].
Qed.
(* two live blocks at the same address are the same block (AR's pairwise disjointness), so a block that is NOT in a
   sublist of the live blocks has no head of that sublist's shape at its address *)
Lemma crtD2_block_at : forall ly S (W : world tfibsegs) mem md p m n,
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) ->
  0 <= m -> 0 <= n -> m = n.
Proof.
intros ly S W mem md p m n HAR Hm Hn Hm0 Hn0.
destruct (Z.eq_dec m n) as [E|NE]; [exact E|exfalso].
assert (Hne : (p, m) <> (p, n)) by (intros E; injection E; exact NE).
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md p m p n HAR Hm Hn Hne) as D.
pose proof (YCbq.req_size_pos m Hm0) as Hrm. pose proof (YCbq.req_size_pos n Hn0) as Hrn.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* a live block's requested size is non-negative (AR_blocks_law's last clause), so its range is non-empty *)
Lemma crtD2_blk_nonneg : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn & _). lia.
Qed.
(* ---- a live block occurs ONCE in the live list: its mapped range would otherwise be disjoint from itself ---- *)
Lemma crtD2_once : forall ly S (W : world tfibsegs) mem md l1 l2 x,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2) -> ~ In x (l1 ++ l2).
Proof.
intros ly S W mem md l1 l2 x HAR HP Hin.
assert (HinA : In x (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity).
destruct x as [p n]. cbn [fst snd] in *.
pose proof (YCbq.req_size_pos n (crtD2_blk_nonneg ly S W mem md p n HAR HinA)) as Hrn.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR HinA) as (_ & _ & _ & _ & _ & PW & _).
apply (crtD2_perm_not_in (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))
  (map (fun b => (fst b, req_size (snd b))) (l1 ++ l2))
  (map (fun b => (fst b, req_size (snd b))) [(p, n)]) (p, req_size n) PW).
- rewrite <- map_app. apply Permutation_map.
  apply (Permutation_trans HP). rewrite <- app_assoc. apply Permutation_app_head.
  apply Permutation_cons_append.
- cbn [snd]. lia.
- left. reflexivity.
- apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, n)). exact Hin.
Qed.
(* ---- THE LANE'S OBLIGATION AT EVERY FREE: the freed block's own head is NOT in U ----
   U is a permutation of the boundary's listed heads, and every listed head names a live block at its own address.
   If the freed block's head were in U, that head's block would sit at the freed block's address, so (crtD2_block_at)
   it would BE the freed block - listed both as the block being freed and somewhere else in the live list, which
   crtD2_once refutes. The side condition is therefore the easy one: every head of the boundary's list names a block
   of the live list WITH THE FREED BLOCK REMOVED. At 0x82348 / 0x82350 that holds because want and same are the two
   plain interceptor-malloc blocks (0x81ca4 / 0x81cb8): __wrap_malloc owns no head for them, so they appear in no
   head list at all. ---- *)
Lemma crtD2_no_head : forall ly S (W : world tfibsegs) mem md U UL L1 L2 p n,
  AR tfibsegs B ly S W mem md -> FSupoisonU.fs_heads B ly S U ->
  Permutation (ablocks B ly S) (L1 ++ (p, n) :: L2) -> Permutation U UL ->
  (forall q, In (q, 16) UL -> exists m, In (q, m) (L1 ++ L2)) ->
  ~ In (p, 16) U.
Proof.
intros ly S W mem md U UL L1 L2 p n HAR FH HPL HPU HUL Hin.
destruct (HUL p (Permutation_in _ HPU Hin)) as (m & Hm).
assert (HmA : In (p, m) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_app_or in Hm as [Hq|Hq];
  apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
assert (HnA : In (p, n) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; left; reflexivity).
assert (Emn : m = n)
  by exact (crtD2_block_at ly S W mem md p m n HAR HmA HnA
              (crtD2_blk_nonneg ly S W mem md p m HAR HmA) (crtD2_blk_nonneg ly S W mem md p n HAR HnA)).
subst m. exact (crtD2_once ly S W mem md L1 L2 (p, n) HAR HPL Hm).
Qed.
(* every head a reader tree contributes names that tree's own block (rd_heads / rd_hblocks are the same map) *)
Lemma crtD2_rd_head : forall (D : list (Z * Z)) q,
  In (q, 16) (rd_heads D) -> exists k, In (q, k + HEAD) (rd_hblocks D).
Proof.
intros D q Hin. unfold rd_heads in Hin. apply in_map_iff in Hin as (ak & E & Hak).
destruct ak as (a, k). cbn [fst snd] in E.
assert (Eq : q = a - HEAD) by (inversion E; reflexivity).
exists k. unfold rd_hblocks. rewrite Eq.
exact (in_map (fun b : Z * Z => (fst b - HEAD, snd b + HEAD)) D (a, k) Hak).
Qed.
End u.

(* ================= the lane's own call-site facts =================
   The call-site precondition itself is the BASE's lib/A/FSH_crt_site.v (crt_site_pre, crt_ch1; a Theorem Labs lane's
   v13, a Theorem Labs lane's proved text): this file IMPORTS it and keeps no copy of it. What stays here is what only this lane
   needs - the fake frame's place at a boundary, and the window premise of pj_free_spec at a frame object. *)
Section pre. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* crt's journal from its entry, with its frame (3, pos) as own (crt_from's premise) *)
Definition crtD2_J (cx : crt_cx) ly3 S3 (W3 : world tfibsegs) mem3 md3 (k : Z) : Prop :=
  @ajournal rc SK tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 mem3 md3 k.

Lemma crtD2_F_at : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 k,
  crtD2_J cx ly3 S3 W3 mem3 md3 k -> frame_addr ly3 3 (c_pos cx) = crt_F cx.
Proof.
intros cx ly3 S3 W3 mem3 md3 k (_ & Hly & _). unfold crt_F, frame_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma crtD2_FL_at : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 k,
  crtD2_J cx ly3 S3 W3 mem3 md3 k -> flag_addr ly3 3 (c_pos cx) = crt_FL cx.
Proof.
intros cx ly3 S3 W3 mem3 md3 k (_ & Hly & _). unfold crt_FL, flag_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
(* the frame's place: 32-aligned, at or above 4096, below alloc_ceiling, an application range, its shadow inside
   [kLowMemEnd, kHighShadowEnd) *)
Lemma crtD2_F_facts : forall cx ly3 S3 U3 (W3 : world tfibsegs) mem3 md3 k,
  crtD2_J cx ly3 S3 W3 (unpoison U3 mem3) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  crt_F cx mod 32 = 0 /\ 4096 <= crt_F cx /\ crt_F cx + 512 <= alloc_ceiling /\ in_app (crt_F cx) 512 /\
  kLowMemEnd <= crt_SF cx /\ crt_SF cx + 64 <= kHighShadowEnd.
Proof.
intros cx ly3 S3 U3 W3 mem3 md3 k HJ HARU Hfr.
pose proof (crtD2_F_at cx _ _ _ _ _ _ HJ) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
assert (Hin : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (Hal & Happ & _).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (H4096 & Hceil & _).
rewrite EF, crt_frame3 in *. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds (crt_F cx) ltac:(lia)) as (S1 & _).
pose proof (shadow_addr_bounds (crt_F cx + 511) ltac:(lia)) as (_ & S2).
assert (HS512 : shadow_addr (crt_F cx) + 64 <= shadow_addr (crt_F cx + 511) + 1)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
unfold crt_SF. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Happ|]. split; lia.
Qed.

(* ---- the window premise of pj_free_spec at a frame object: the object lies in the class-3 fake frame, which is
   below alloc_ceiling, and the callee's window top is crt's re-aligned sp, which is above alloc_ceiling by crt's own
   room. So `v + 56 <= spZ regs - STK_pj_free 2` (the first disjunct of pj_free_spec's window premise). ---- *)
Lemma crtD2_window : forall cx ly3 S3 U3 (W3 : world tfibsegs) mem3 md3 k regsC off STKc,
  crt_base B cx ->
  crtD2_J cx ly3 S3 W3 (unpoison U3 mem3) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  spZ regsC = crt_sp1 cx -> 0 <= off -> off + 56 <= 512 -> STKc + 208 <= STK_check_round_trip ->
  crt_F cx + off + 56 <= spZ regsC - STKc.
Proof.
intros cx ly3 S3 U3 W3 mem3 md3 k regsC off STKc HB HJ HARU Hfr Esp Hoff0 Hoff1 HSTK.
destruct (crtD2_F_facts cx ly3 S3 U3 W3 mem3 md3 k HJ HARU Hfr) as (_ & _ & Hceil & _ & _ & _).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
(* lia treats alloc_ceiling as opaque: its range is YM05's own fact *)
pose proof (@alloc_ceiling_value rc) as (HCr & _).
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
rewrite Esp. lia.
Qed.
End pre.

(* ================= the lane's five INNER boundaries =================
   crt_INV_822ac (the base, D1's text) is the lane's ENTRY and crt_INV_T (the base) its EXIT; the five boundaries
   between the six calls are this lane's own, so they live here (lane head: inner invariants live in the lane's file).
   Each is crt_INV_822ac with what the call before it freed removed, and with the BUDGET carried as the REMAINING
   allowance - `k + <ticks still to come> <= EV_check_round_trip` - rather than as a prefix bound. That form is what
   the callee room premises need (`st_nev S + EV_callee <= EV_MAX` follows from crt_base's
   `st_nev (c_S cx) + EV_check_round_trip <= EV_MAX` and the journal's `st_nev S3 <= st_nev (c_S cx) + k`), and it
   mentions no list that the call before it has already freed.
   The frees, in order (MEASURED, see the header): pj_free (&back) drops Dback's blocks and their heads; pj_free
   (&doc) drops Ddoc's; fuzz_free (back) drops back's block and its head; fuzz_free (text) drops text's; free (want)
   and free (same) drop the two interceptor blocks, which have NO head - so U is already c_U at 0x82344 and the two
   thunks leave it alone. ---- *)
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

Definition crtD2_blocks (cx : crt_cx) (extra : list (Z * Z)) (ly3 : alayout) (S3 : astate) : Prop :=
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ extra).
Definition crtD2_heads (cx : crt_cx) (extra U3 : list (Z * Z)) : Prop := Permutation U3 (c_U cx ++ extra).
(* the four blocks still live at the lane's entry, in crt_INV_822ac's order *)
Definition crtD2_L4 (cx : crt_cx) (same nsame back : Z) : list (Z * Z) :=
  let len := Z.of_nat (length (c_bs cx)) in let tb2 := WriterSpec.b64_enc (c_bs cx) in
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
   (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)].

(* 0x822b4, after pj_free (&back): Dback's blocks and heads are gone, back's own block is not (pj_free frees the
   tree's blocks, not the string the caller still holds); the doc object is still a pobj *)
Definition crtD2_INV_35 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\
  (exists (same nsame back : Z) (Ddoc : list (Z * Z)) (live peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     crtD2_blocks cx (crtD2_L4 cx same nsame back ++ rd_hblocks Ddoc) ly3 S3 /\
     crtD2_heads cx ([(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)] ++ rd_heads Ddoc) U3 /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\ rom_view tfibsegs W3 mem /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum Ddoc /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\
     k + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip).

(* 0x822bc, after pj_free (&doc): both trees are gone; the frame's objects are no longer read *)
Definition crtD2_INV_36 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  (exists (same nsame back : Z) (live peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     crtD2_blocks cx (crtD2_L4 cx same nsame back) ly3 S3 /\
     crtD2_heads cx [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)] U3 /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\ rom_view tfibsegs W3 mem /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\
     k + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip).

(* 0x8233c, after fuzz_free (back): back's block and its head are gone, and g_live is down by its size *)
Definition crtD2_INV_37 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let len := Z.of_nat (length (c_bs cx)) in
  (exists (same nsame : Z) (live peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\
     crtD2_blocks cx [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD);
                      (c_want cx, FSH_Fn_writer.enc_size len); (same, nsame)] ly3 S3 /\
     crtD2_heads cx [(c_text cx - HEAD, HEAD)] U3 /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\ rom_view tfibsegs W3 mem /\
     live = c_live cx + FSH_Fn_writer.enc_size len /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\
     k + EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip).

(* 0x82344, after fuzz_free (text): the walk holds only the two interceptor blocks, and U is back at the entry's
   (up to order) - the two `free` thunks that follow change it no further *)
Definition crtD2_INV_38 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let len := Z.of_nat (length (c_bs cx)) in
  (exists (same nsame : Z) (peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\
     crtD2_blocks cx [(c_want cx, FSH_Fn_writer.enc_size len); (same, nsame)] ly3 S3 /\
     crtD2_heads cx [] U3 /\ FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_glob tfibsegs W3 mem (c_live cx) peak cnt SIZE_MAXZ /\ rom_view tfibsegs W3 mem /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\
     k + 2 * CRT_EV_WRAP <= EV_check_round_trip).

(* 0x8234c, after free (want) *)
Definition crtD2_INV_39 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in
  (exists (same nsame : Z) (peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\
     crtD2_blocks cx [(same, nsame)] ly3 S3 /\
     crtD2_heads cx [] U3 /\ FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_glob tfibsegs W3 mem (c_live cx) peak cnt SIZE_MAXZ /\ rom_view tfibsegs W3 mem /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\
     k + CRT_EV_WRAP <= EV_check_round_trip).
End inv.
(* ================= U AT THE TWO INTERCEPTOR FREES (0x82348 want, 0x82350 same) =================
   The lane's entry boundary lists exactly three kinds of user-poisoned head: the entry's own (c_U cx), the text and
   back blocks', and the two reader trees'. NONE of them sits at want or at same, because __wrap_malloc (0x81ca4 /
   0x81cb8) hands back a raw block and owns no head for it. crtD2_no_head turns that into the `~ In (p, 16) U3` the
   free step needs, and crtD2_free_outside then gives afree_realizesU's range premise: every range of U3 lies
   outside the freed block. These two lemmas take crt_INV_822ac's own conjuncts, so they do not move when the
   invariant's unrelated clauses do. ================= *)
Section nh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the entry's listed heads, as crt_INV_822ac states them *)
Definition crtD2_UL (cx : crt_cx) (back : Z) (Ddoc Dback : list (Z * Z)) : list (Z * Z) :=
  c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dback).

Lemma crtD2_no_head_want : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 U3 Ddoc Dback same nsame back,
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  AR tfibsegs B ly3 S3 W3 mem3 md3 -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks (Ddoc ++ Dback)) ->
  Permutation U3 (crtD2_UL cx back Ddoc Dback) ->
  ~ In (c_want cx, 16) U3.
Proof.
intros cx ly3 S3 W3 mem3 md3 U3 Ddoc Dback same nsame back HFH0 HAR FH HPL HPU.
apply (crtD2_no_head B ly3 S3 W3 mem3 md3 U3 (crtD2_UL cx back Ddoc Dback)
  (ablocks B (c_ly cx) (c_S cx) ++ [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)])
  ([(same, nsame); (back - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)]
   ++ rd_hblocks (Ddoc ++ Dback))
  (c_want cx) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) HAR FH); [| exact HPU |].
- eapply Permutation_trans; [exact HPL|]. unfold crtD2_L4. rewrite <- app_assoc. cbn [app]. apply Permutation_refl.
- intros q Hq. unfold crtD2_UL in Hq.
  apply in_app_or in Hq as [Hq | Hq].
  + destruct (HFH0 (q, 16) Hq) as (_ & m & Hm & _). cbn [fst] in Hm.
    exists m. apply in_or_app. left. apply in_or_app. left. exact Hm.
  + apply in_app_or in Hq as [Hq | Hq].
    * cbn [In] in Hq. destruct Hq as [E | [E | []]]; injection E as Eq; subst q.
      -- exists (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD).
         apply in_or_app. left. apply in_or_app. right. left. reflexivity.
      -- exists (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
         apply in_or_app. right. apply in_or_app. left. right. left. reflexivity.
    * destruct (crtD2_rd_head (Ddoc ++ Dback) q Hq) as (kk & Hkk).
      exists (kk + HEAD). apply in_or_app. right. apply in_or_app. right. exact Hkk.
Qed.

Lemma crtD2_no_head_same : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 U3 Ddoc Dback same nsame back,
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  AR tfibsegs B ly3 S3 W3 mem3 md3 -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks (Ddoc ++ Dback)) ->
  Permutation U3 (crtD2_UL cx back Ddoc Dback) ->
  ~ In (same, 16) U3.
Proof.
intros cx ly3 S3 W3 mem3 md3 U3 Ddoc Dback same nsame back HFH0 HAR FH HPL HPU.
apply (crtD2_no_head B ly3 S3 W3 mem3 md3 U3 (crtD2_UL cx back Ddoc Dback)
  (ablocks B (c_ly cx) (c_S cx) ++ [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
                                   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))])
  ([(back - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)] ++ rd_hblocks (Ddoc ++ Dback))
  same nsame HAR FH); [| exact HPU |].
- eapply Permutation_trans; [exact HPL|]. unfold crtD2_L4. rewrite <- app_assoc. cbn [app]. apply Permutation_refl.
- intros q Hq. unfold crtD2_UL in Hq.
  apply in_app_or in Hq as [Hq | Hq].
  + destruct (HFH0 (q, 16) Hq) as (_ & m & Hm & _). cbn [fst] in Hm.
    exists m. apply in_or_app. left. apply in_or_app. left. exact Hm.
  + apply in_app_or in Hq as [Hq | Hq].
    * cbn [In] in Hq. destruct Hq as [E | [E | []]]; injection E as Eq; subst q.
      -- exists (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD).
         apply in_or_app. left. apply in_or_app. right. left. reflexivity.
      -- exists (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
         apply in_or_app. right. apply in_or_app. left. left. reflexivity.
    * destruct (crtD2_rd_head (Ddoc ++ Dback) q Hq) as (kk & Hkk).
      exists (kk + HEAD). apply in_or_app. right. apply in_or_app. right. exact Hkk.
Qed.

(* ---- and the premise each of the two thunks takes: every range of U lies outside the block being freed ---- *)
Lemma crtD2_free_outside_want : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 U3 Ddoc Dback same nsame back,
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks (Ddoc ++ Dback)) ->
  Permutation U3 (crtD2_UL cx back Ddoc Dback) ->
  let n := FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) in
  In (c_want cx, n) (ablocks B ly3 S3) /\
  forall r, In r U3 -> fst r + snd r <= c_want cx \/ c_want cx + req_size n <= fst r.
Proof.
intros cx ly3 S3 W3 mem3 md3 U3 Ddoc Dback same nsame back HFH0 HARU FH HPL HPU n.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
assert (Hin : In (c_want cx, n) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. apply in_or_app. left.
  unfold crtD2_L4. right. left. reflexivity. }
split; [exact Hin|].
exact (crtD2_free_outside B ly3 S3 U3 W3 mem3 md3 (c_want cx) n HARU FH Hin
  (crtD2_no_head_want cx ly3 S3 W3 (unpoison U3 mem3) md3 U3 Ddoc Dback same nsame back HFH0 HAR FH HPL HPU)).
Qed.
Lemma crtD2_free_outside_same : forall cx ly3 S3 (W3 : world tfibsegs) mem3 md3 U3 Ddoc Dback same nsame back,
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks (Ddoc ++ Dback)) ->
  Permutation U3 (crtD2_UL cx back Ddoc Dback) ->
  In (same, nsame) (ablocks B ly3 S3) /\
  forall r, In r U3 -> fst r + snd r <= same \/ same + req_size nsame <= fst r.
Proof.
intros cx ly3 S3 W3 mem3 md3 U3 Ddoc Dback same nsame back HFH0 HARU FH HPL HPU.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
assert (Hin : In (same, nsame) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. apply in_or_app. left.
  unfold crtD2_L4. right. right. left. reflexivity. }
split; [exact Hin|].
exact (crtD2_free_outside B ly3 S3 U3 W3 mem3 md3 same nsame HARU FH Hin
  (crtD2_no_head_same cx ly3 S3 W3 (unpoison U3 mem3) md3 U3 Ddoc Dback same nsame back HFH0 HAR FH HPL HPU)).
Qed.
End nh.

(* ================= THE SIX CALL-SITE PRECONDITIONS =================
   One bundle, instantiated six times. It needs NO boundary invariant: a call site of this lane is legal at any
   boundary state of the walk. Everything in it comes from crt_base, crt_E, the journal, ARU, the frame record and
   the ENGINE's answer at the call (the symbolic state ssC), through the base's crt_site_pre (FSH_crt_site.v).
   What each callee then takes ON TOP of this is the data it frees, which is the boundary invariant's business:
   pj_free_spec's pj_fd / pobj / rd_blocks_ok / rd_sum, fuzz_free_spec's U-split and fs_rblock, and
   afree_realizesU's block membership - whose range premise is crtD2_free_outside_want / _same above. ================= *)
Section site. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

Lemma crtD2_site : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md ss r STKc,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md ->
  crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) ->
  sr_get (ss_regs ss) 1%bv = SLit r -> sr_get (ss_regs ss) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> nth_error (ss_mem ss) 0 = Some crt_s0_region ->
  4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  raZ (ms_regs ms) = r /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms) = crt_sp1 cx /\ spZ (ms_regs ms) + 32 <= ly_top ly3.
Proof.
intros cx E k ly3 S3 U3 W3 ms md ss r STKc HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 G0 Hr Hr2 HSTKc HSTK.
pose proof HE as (E2 & _).
assert (Hrok : YK0s.ret_ok (Z_to_bv 64 r)) by (apply YK0s.ret_ok_even; rewrite (wz r) by lia; exact Hr2).
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms md ss r STKc HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 G0 Hr
  Hrok HSTKc HSTK) as (HP & Hra & HFL & HTOP).
assert (R2 : spZ (ms_regs ms) = crt_sp1 cx)
  by (unfold spZ; rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms 2%bv HS), G2, fsw_SOff0; exact E2).
split; [exact HP|]. split; [exact Hra|].
split; [exact HFL|]. split; [exact R2 | exact HTOP].
Qed.

(* the value the call passes in a0, as the boundary env reads it (the atom the engine answered with) *)
Lemma crtD2_a0 : forall E (W3 : world tfibsegs) ms ss a,
  st_ok tfibsegs E ss (restrict (w_H W3) ms) -> sr_get (ss_regs ss) 10%bv = SOff a 0 ->
  YK11.getr (ms_regs ms) 10%bv = ew E a.
Proof.
intros E W3 ms ss a HS G10.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms 10%bv HS), G10. apply fsw_SOff0.
Qed.

(* ---- site 1 and 2: pj_free (&back) at 0x822b0 and pj_free (&doc) at 0x822b8 ----
   a0 is the frame object (atom 18 = &back = F + 0x140, atom 26 = &doc = F + 0x20 under crt_INV_822ac), the window
   premise holds by crtD2_window. ---- *)
Lemma crtD2_pre_pj_free_back : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss34_pf (restrict (w_H W3) ms) ->
  fpreU tfibsegs B (STK_pj_free 2) ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  YK11.getr (ms_regs ms) 10%bv = ew E 18 /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  (forall off, 0 <= off -> off + 56 <= 512 -> crt_F cx + off + 56 <= spZ (ms_regs ms) - STK_pj_free 2).
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss34_pf_regs as (_ & _ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
pose proof HFR as (Hfr & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss34_pf 0x822b4 (STK_pj_free 2)
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (H & _); lia) crtD2_stk_pj_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|].
split; [exact (crtD2_a0 E W3 ms crt_ss34_pf 18 HS G10)|].
split; [exact HFL|].
intros off H0 H1. exact (crtD2_window SK B cx ly3 S3 U3 W3 (ms_mem ms) md k (ms_regs ms) off (STK_pj_free 2)
  HB HJ HARU Hfr R2 H0 H1 crtD2_stk_pj_free).
Qed.
Lemma crtD2_pre_pj_free_doc : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss35_pf (restrict (w_H W3) ms) ->
  fpreU tfibsegs B (STK_pj_free 2) ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  YK11.getr (ms_regs ms) 10%bv = ew E 26 /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  (forall off, 0 <= off -> off + 56 <= 512 -> crt_F cx + off + 56 <= spZ (ms_regs ms) - STK_pj_free 2).
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss35_pf_regs as (_ & _ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
pose proof HFR as (Hfr & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss35_pf 0x822bc (STK_pj_free 2)
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (H & _); lia) crtD2_stk_pj_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|].
split; [exact (crtD2_a0 E W3 ms crt_ss35_pf 26 HS G10)|].
split; [exact HFL|].
intros off H0 H1. exact (crtD2_window SK B cx ly3 S3 U3 W3 (ms_mem ms) md k (ms_regs ms) off (STK_pj_free 2)
  HB HJ HARU Hfr R2 H0 H1 crtD2_stk_pj_free).
Qed.

(* ---- site 3 and 4: fuzz_free (back) at 0x82338 and fuzz_free (text) at 0x82340 ----
   a0 is the block itself: atom 25 (s9 = back, the parsed document's text) and atom 48 (the s1 slot 0x30 = text). ---- *)
Lemma crtD2_pre_fuzz_free_back : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss36_ff (restrict (w_H W3) ms) ->
  fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  YK11.getr (ms_regs ms) 10%bv = ew E 25 /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE.
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss36_ff_regs as (_ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss36_ff 0x8233c STK_fuzz_free
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (_ & H & _); lia) crtD2_stk_fuzz_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|].
split; [exact (crtD2_a0 E W3 ms crt_ss36_ff 25 HS G10) | exact HFL].
Qed.
Lemma crtD2_pre_fuzz_free_text : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss37_ff (restrict (w_H W3) ms) ->
  fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  YK11.getr (ms_regs ms) 10%bv = ew E 48 /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE.
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss37_ff_regs as (_ & _ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss37_ff 0x82344 STK_fuzz_free
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (_ & H & _); lia) crtD2_stk_fuzz_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|].
split; [exact (crtD2_a0 E W3 ms crt_ss37_ff 48 HS G10) | exact HFL].
Qed.

(* ---- site 5 and 6: the two __wrap_free thunks at 0x82348 (want, the s1 slot 0x38 = atom 49) and 0x82350 (same,
   atom 24 = s8). A RUNTIME call: FSW_malloc_free.fsw_aj_freeU takes it, so what it needs beyond the registers is the
   chain (inside fpreU's afn_pre) and ASTACK's room, not a fpreU of its own. ---- *)
Lemma crtD2_pre_free_want : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss38_fr (restrict (w_H W3) ms) ->
  fpreU tfibsegs B ASTACK ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  raZ (ms_regs ms) = 0x8234c /\
  YK11.getr (ms_regs ms) 10%bv = ew E 49 /\
  spZ (ms_regs ms) = crt_sp1 cx /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE.
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss38_fr_regs as (_ & _ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss38_fr 0x8234c ASTACK
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (_ & _ & H); lia) crtD2_stk_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|]. split; [exact Hra|].
split; [exact (crtD2_a0 E W3 ms crt_ss38_fr 49 HS G10)|]. split; [exact R2 | exact HFL].
Qed.
Lemma crtD2_pre_free_same : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx -> crt_E cx E ->
  crtD2_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md -> crt_frame_ok cx S3 W3 ms ->
  st_ok tfibsegs E crt_ss39_fr (restrict (w_H W3) ms) ->
  fpreU tfibsegs B ASTACK ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md (crt_ch1 cx) /\
  raZ (ms_regs ms) = 0x82354 /\
  YK11.getr (ms_regs ms) 10%bv = ew E 24 /\
  spZ (ms_regs ms) = crt_sp1 cx /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE.
Proof.
intros cx E k ly3 S3 U3 W3 ms md HB HE HJ HARU HFR HS.
destruct crtD2_ss39_fr_regs as (_ & _ & _ & G10 & G1 & G2 & G3 & G4 & G8 & _ & _).
destruct (crtD2_site cx E k ly3 S3 U3 W3 ms md crt_ss39_fr 0x82354 ASTACK
  HB HE HJ HARU HFR HS G1 G2 G3 G4 G8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
  ltac:(pose proof crtD2_stk_pos as (_ & _ & H); lia) crtD2_stk_free)
  as (HP & Hra & HFL & R2 & HTOP).
split; [exact HP|]. split; [exact Hra|].
split; [exact (crtD2_a0 E W3 ms crt_ss39_fr 24 HS G10)|]. split; [exact R2 | exact HFL].
Qed.
End site.
