(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 662 of its 702 lines of code are new or changed and 318 lines of the source are left out. *)
(* remember (image A, fuzz_link.asan 0x89db4; listing (internal path) (internal record, sha256 e02062b286f1)):
   THE STRCMP LOOP +0x5c .. +0x7c of the walk of lib/A/Prog/remember_c.v `remember_acontract`, by induction on the
   number of slots left, d = n - i, from the call config of turn i (pc = the strcmp trampoline, the call +0x64).

     rem_loop : at the call of turn i (0 <= i < n), with the machine invariant below, the walk reaches remember's
                apostF.

   One turn: the call through lib/A/Prog/rememberCalls.v `rem_strcmp_call` (the slot i against the name); the
   loop state rebuilt at +0x68 from the returned registers (lib/A/Prog/rememberLoop.v `rem_lentry`); then the
   branches of the listing:
   - +0x68 `beqz a0` taken (slot i is the name): the epilogue and `ret` +0xa4, closed by
     lib/A/Prog/rememberAppend.v `rem_ret_leaf` (a hit: the list is unchanged);
   - not taken: +0x74 `bnez s6`; taken: the run back to the call +0x64 of turn i + 1, and the induction
     hypothesis; not taken (i = n - 1, every slot differs from the name): +0x7c `bge a0, s4` with a0 = 31;
     taken (n <= 31): the append +0xa8 .. +0xf4 and the TAIL jump, closed by `rem_append_tail`; not taken
     (n = 32): the epilogue and `ret`, closed by `rem_ret_leaf` (the list is full).

   The invariant at the call of turn i (registers: what the listing holds there; memory: the call memory memc
   outside the window [sp - REMEMBER_AK, sp), the frame's eight saved words, every byte of memc still there):
   ra = +0x68, sp = entry sp - 64, s0 = p, s1 = q, a0 = s2 = p + 4 + 16 i, a1 = q, s3 = p + 4, s4 = n,
   s5 = the shadow byte address of p, s6 = n - i, gp / tp / s7..s11 as at the entry; the journal at k; the
   descriptors and the file system as at the call; and the slots j < i all differ from the name.

   Section hypotheses: LAWS, STRCMP (RtString.astrcmp_realizes at the strcmp trampoline, discharged by
   lib/A/Rt/RtStrcmpClosed.v link_strcmp_closed), SNP (LinkSnpDef.v asnprintf_link_realizes, discharged by
   link_snprintf), TB (PcapSyms B), HSEGS (pa_segs = tfibsegs), HV (LinkVals).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs LinkMfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  rememberPost rememberEntry rememberKept rememberCalls rememberLoop rememberAppend.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Small facts
   ========================================================================== *)

Lemma rem_br_eq : forall E n (x : word), ew E n = x ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned x =? 0).
Proof.
intros E n x Hn. rewrite branch_eq_U. pose proof (bv_unsigned_in_range 64 x) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite (U_atom E n (bv_unsigned x)) by first [rewrite Hn; symmetry; apply Z_to_bv_bv_unsigned | lia].
rewrite U_lit by lia. reflexivity.
Qed.

Lemma rem_br_ne : forall E n v, ew E n = Z_to_bv 64 v -> 1 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n (-1))) (sv_denot E (SLit 0)) = negb (v - 1 =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_ne_U. rewrite U_SOff, Hn, unsigned_lit_small by lia.
rewrite zcanon_id by (unfold M64; lia). rewrite U_lit by lia. reflexivity.
Qed.

Lemma rem_val_mem_keep : forall segs (m m' : word -> option byte) a n v,
  (forall b, a <= b < a + Z.of_nat n -> mbyte segs m' b = mbyte segs m b) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' a n v H Hv k Hk. rewrite (H (a + Z.of_nat k) ltac:(lia)). exact (Hv k Hk). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis STRCMP : RtString.astrcmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).
Hypothesis SNP : asnprintf_link_realizes pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* the loop's one shadow entry: the four bytes of m->n, through s0 = atom 8 *)
Lemma rem_lshok : forall (W : world pa_segs) memL (regs regsL : bvmap 5 word) p n,
  getr regsL 8 = Z_to_bv 64 p -> amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memL) p ->
  sh_ok pa_segs rBx lSH (Eimg (Ereg regsL (l_extra n regs))) (rdW W memL).
Proof.
intros W memL regs regsL p n Hs0 HBLK.
pose proof HBLK as (Hp0 & Hpm & Hpra & _ & _ & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regsL (l_extra n regs))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regsL (l_extra n regs)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E8 : ew E 8 = getr regsL 8)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 8 8%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RSB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (Hpb : p + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
assert (Hp' : bv_unsigned (getr regsL 8) = p) by (rewrite Hs0; apply unsigned_lit_small; lia).
assert (UB : U E rBx = RSB).
{ unfold rBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold RSB; lia).
  apply zcanon_id. unfold RSB, M64. lia. }
assert (UM : U E (SOff 8 0) = p).
{ rewrite U_SOff, E8, Z.add_0_r, Hp'. apply zcanon_id. unfold M64. lia. }
apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UM, Z.add_0_r.
split.
- intros x Hx. exact (Hpra x ltac:(unfold MK_SIZE; lia)).
- intros a Ha. cbn [Z.min Z.max] in Ha.
  unfold amem_range, MK_SIZE in Hpm. unfold RSB.
  destruct Hpm as [Hx | [Hy Hx]]; lia.
Qed.

(* the callee-saved registers and ra after the epilogue +0x80 .. +0xa0 (or +0xd0 .. +0xf0) of a loop state *)
Lemma rem_epi : forall E ss (ms : machine_state) (H : word -> bool) (regs regsL : bvmap 5 word) n,
  st_ok pa_segs E ss (restrict H ms) ->
  (forall a, (a < 42)%nat -> ew E a = ew (Ereg regsL (l_extra n regs)) a) ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 64) -> 64 <= spZ regs < 2 ^ 64 ->
  (forall r, r = 3 \/ r = 4 \/ 23 <= r <= 27 -> getr regsL (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  map (fun r => sr_get (ss_regs ss) (Z_to_bv 5 r)) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]
    = [SOff 34 0; SOff 2 64; SOff 3 0; SOff 4 0; SOff 35 0; SOff 36 0; SOff 37 0; SOff 38 0; SOff 39 0;
       SOff 40 0; SOff 41 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] ->
  aregs_preserved regs (ms_regs ms) /\ getr (ms_regs ms) (Z_to_bv 5 1) = getr regs (Z_to_bv 5 1).
Proof.
intros E ss ms H regs regsL n HS HE H2 Hsp HRS Hl.
cbn [map] in Hl.
injection Hl as E1 E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
assert (G : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_restrict_reg pa_segs H E ss ms r HS)).
assert (X : forall a k, (a < 42)%nat ->
          sv_denot E (SOff a k) = Z_to_bv 64 (bv_unsigned (ew (Ereg regsL (l_extra n regs)) a) + k))
  by (intros a k Ha; cbn [sv_denot]; rewrite (HE a Ha); reflexivity).
assert (Xs : forall a (r : Z), (a < 32)%nat -> Z.of_nat a = r -> r = 3 \/ r = 4 \/ 23 <= r <= 27 ->
          sv_denot E (SOff a 0) = getr regs (Z_to_bv 5 r)).
{ intros a r Ha Har Hr. rewrite (X a 0 ltac:(lia)), Z.add_0_r.
  rewrite (ew_Ereg_nat regsL _ a (Z_to_bv 5 r)) by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; exact Har).
  rewrite (HRS r Hr). apply Z_to_bv_bv_unsigned. }
assert (Xf : forall j (r : Z), (j < 10)%nat -> nth j (l_extra n regs) (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r) ->
          sv_denot E (SOff (32 + j) 0) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj Hn. rewrite (X (32 + j)%nat 0 ltac:(lia)), Z.add_0_r, ew_Ereg_extra, Hn.
  apply Z_to_bv_bv_unsigned. }
split.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    rewrite G.
  + rewrite E2, (X 2%nat 64 ltac:(lia)).
    rewrite (ew_Ereg_nat regsL _ 2 2%bv eq_refl), H2, unsigned_lit_small by lia.
    replace (spZ regs - 64 + 64) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + rewrite E3. exact (Xs 3%nat 3 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E4. exact (Xs 4%nat 4 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E8. exact (Xf 3%nat 8 ltac:(lia) eq_refl).
  + rewrite E9. exact (Xf 4%nat 9 ltac:(lia) eq_refl).
  + rewrite E18. exact (Xf 5%nat 18 ltac:(lia) eq_refl).
  + rewrite E19. exact (Xf 6%nat 19 ltac:(lia) eq_refl).
  + rewrite E20. exact (Xf 7%nat 20 ltac:(lia) eq_refl).
  + rewrite E21. exact (Xf 8%nat 21 ltac:(lia) eq_refl).
  + rewrite E22. exact (Xf 9%nat 22 ltac:(lia) eq_refl).
  + rewrite E23. exact (Xs 23%nat 23 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E24. exact (Xs 24%nat 24 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E25. exact (Xs 25%nat 25 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E26. exact (Xs 26%nat 26 ltac:(lia) eq_refl ltac:(lia)).
  + rewrite E27. exact (Xs 27%nat 27 ltac:(lia) eq_refl ltac:(lia)).
- rewrite G, E1. exact (Xf 2%nat 1 ltac:(lia) eq_refl).
Qed.

(* the block's shadow and place, and its bytes, at a later memory that agrees with memc outside the window *)
Lemma rem_blk_keep : forall (W : world pa_segs) (regs : bvmap 5 word) memc memL p,
  alloc_ceiling <= spZ regs - REMEMBER_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memL a = aview pa_segs (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W memL) ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) p ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memL) p.
Proof.
intros W regs memc memL p Hceil UN GR HBLK.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
assert (Hpb : p + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
split; [exact Hp0|]. split; [exact Hpm|].
split.
{ apply (ra_shadow_eq (ard pa_segs (rdW W memc))); [exact Hpra|].
  intros y Hy.
  assert (Hs : SHADOW_OFF <= shadow_addr y < kHighShadowEnd).
  { unfold shadow_addr.
    pose proof (Z.div_pos y 8 ltac:(unfold MK_SIZE in *; lia) ltac:(lia)).
    assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold MK_SIZE in *; lia). lia. }
  apply UN; lia. }
split.
{ intros sh Hsh. exact (rem_aview_some_grow pa_segs (w_H W) memc memL sh GR (Hphv sh Hsh)). }
split; [|exact Hpap].
intros b Hb. exact (rem_aview_some_grow pa_segs (w_H W) memc memL b GR (Hptail b Hb)).
Qed.

Lemma rem_marks_keep : forall (W : world pa_segs) (regs : bvmap 5 word) memc memL p gbs,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memL a = aview pa_segs (w_H W) memc a) ->
  (forall x, apresent (w_H W) memc x -> apresent (w_H W) memL x) ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) p ->
  amarks_at pa_segs (rdW W memc) p gbs -> amarks_at pa_segs (rdW W memL) p gbs.
Proof.
intros W regs memc memL p gbs UN PR HBLK HMK.
pose proof HBLK as (Hp0 & Hpm & _ & _ & _ & Hpap).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (Hpb : p + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
pose proof HMK as (HMKb & HMKlen). pose proof HMKb as (HMKbytes & HMKwr).
apply (rem_marks_kept pa_segs (rdW W memc) (rdW W memL) p gbs HMK).
- intros a Ha. apply (rem_mbyte_eq_of_aview_eq W).
  apply UN; [unfold MK_SIZE in *; lia | unfold apart_frame, MK_SIZE in *; lia].
- intros a Ha. apply (writable_kept (w_H W) memc); [intros Hx; exact (PR _ Hx)|].
  replace a with (p + (a - p)) by lia. apply HMKwr. unfold MK_SIZE in *. lia.
Qed.

(* a run that wrote at most the count word [p, p + 4), which still reads n *)
Lemma rem_run_keep : forall (W : world pa_segs) (memA memB memc : word -> option byte) (regs : bvmap 5 word) p n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 4) ->
     mbyte pa_segs (rdW W memB) a = mbyte pa_segs (rdW W memA) a) ->
  val_mem pa_segs (rdW W memB) p 4 n -> val_mem pa_segs (rdW W memc) p 4 n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memA a = aview pa_segs (w_H W) memc a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
    aview pa_segs (w_H W) memB a = aview pa_segs (w_H W) memc a.
Proof.
intros W memA memB memc regs p n KK VB VC UNA a Ha Hn.
destruct (Z_lt_le_dec a p) as [Hlt | Hge];
  [|destruct (Z_lt_le_dec a (p + 4)) as [Hlt4 | Hge4]].
- transitivity (aview pa_segs (w_H W) memA a);
    [unfold aview; rewrite (KK a Ha ltac:(lia)); reflexivity | exact (UNA a Ha Hn)].
- unfold aview. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (VB (Z.to_nat (a - p)) ltac:(lia)), (VC (Z.to_nat (a - p)) ltac:(lia)). reflexivity.
- transitivity (aview pa_segs (w_H W) memA a);
    [unfold aview; rewrite (KK a Ha ltac:(lia)); reflexivity | exact (UNA a Ha Hn)].
Qed.

(* the write window of every run of the loop: the frame has none, the block has its count word *)
Ltac rem_awr regs U8 Hajw :=
  try unfold l_ss_at; cbn [ss_mem add_cond]; try unfold l_regions; try unfold frame_region;
  try unfold mk_region_loop;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?ew_ewset_other in Ha by lia; rewrite ?U8 in Ha;
  apply (Hajw a); unfold remember_awr; exists (aivl (aarg regs 0) MK_SIZE); split; [left; reflexivity|];
  unfold in_zr, aivl; cbn [fst snd];
  replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
  unfold MK_SIZE in *; lia.

(* a run's frame: every byte but the count word is the one before *)
Ltac rem_kk HFr U8 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; unfold mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
  rewrite unsigned_lit_small by lia;
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  try unfold l_ss_at in Hin; cbn [ss_mem add_cond] in Hin; try unfold l_regions in Hin; cbn [In] in Hin;
  destruct Hin as [<-|[<-|[]]]; try unfold frame_region in Hr; try unfold mk_region_loop in Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
  rewrite ?U8 in Hr; lia.

(* ==========================================================================
   2. The loop
   ========================================================================== *)
Lemma rem_loop : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) gbs nm,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  gx_ok pa_segs B G ->
  arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  (forall a, inFP (remember_awr regs (rdW W memc)) a -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  (forall a, inFP (remember_awr regs (rdW W memc)) a -> ~ in_roP pa_segs PCAP_RLO PCAP_RHI a) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  amarks_at pa_segs (rdW W memc) (aarg regs 0) gbs -> marks_wf gbs ->
  amarks_ledger (ablocks B lyc Sc) (aarg regs 0) ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) (aarg regs 0) ->
  aarg regs 1 <> 0 -> acstr_at pa_segs (rdW W memc) (aarg regs 1) nm -> (length nm <= 15)%nat ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) (aarg regs 1) nm ->
  apart (aarg regs 1) (Z.of_nat (length nm) + 8) (aarg regs 0) MK_SIZE ->
  acstr_at pa_segs (rdW W memc) LA_FMT_S S_FMT_S ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) LA_FMT_S S_FMT_S ->
  forall (d : nat) (i : Z) (regsT : bvmap 5 word) memT mdT,
  Z.of_nat d = mk_n gbs - i -> 0 <= i < mk_n gbs ->
  getr regsT 1 = Z_to_bv 64 (pa_val A_TEXT + (AF_remember + 0x68)) ->
  getr regsT 2 = Z_to_bv 64 (spZ regs - 64) ->
  getr regsT 8 = Z_to_bv 64 (aarg regs 0) -> getr regsT 9 = Z_to_bv 64 (aarg regs 1) ->
  getr regsT 10 = Z_to_bv 64 (aarg regs 0 + 4 + 16 * i) -> getr regsT 11 = Z_to_bv 64 (aarg regs 1) ->
  getr regsT 18 = Z_to_bv 64 (aarg regs 0 + 4 + 16 * i) -> getr regsT 19 = Z_to_bv 64 (aarg regs 0 + 4) ->
  getr regsT 20 = Z_to_bv 64 (mk_n gbs) -> getr regsT 21 = Z_to_bv 64 (RSB + aarg regs 0 / 8) ->
  getr regsT 22 = Z_to_bv 64 (mk_n gbs - i) ->
  (forall r, r = 3 \/ r = 4 \/ 23 <= r <= 27 -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 0) 8 (bv_unsigned (getr regs 22)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 8) 8 (bv_unsigned (getr regs 21)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 16) 8 (bv_unsigned (getr regs 20)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 24) 8 (bv_unsigned (getr regs 19)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 40) 8 (bv_unsigned (getr regs 9)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 48) 8 (bv_unsigned (getr regs 8)) ->
  val_mem pa_segs (rdW W memT) (spZ regs - 64 + 56) 8 (bv_unsigned (getr regs 1)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W memT) ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  m_fds mdT = m_fds mdc -> m_fs mdT = m_fs mdc ->
  (forall j, 0 <= j < i -> cstr (slice gbs (MK_NAME + MARK_LEN * j) MARK_LEN) <> nm) ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strcmp)) memT (seg_rom pa_segs)) mdT)
    (apostF SK pa_segs B REMEMBER_AK 0 (fun a => inFP (remember_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP
       ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
       (fun ly2 S2 W2 regs2 mem2 _ =>
          S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
          remember_apost pa_segs regs (rdW W memc) regs2 (rdW W2 mem2))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs nm
  HJ0 HGok HROD Hraw Hra4 Hgp Htp Hal16 Hwlo Hwhi Hajw Hnro Hfrm0 HMK HWF HLED HBLK Hqnz HNM Hlen HNMrt
  Hapart HFMT HFMTrt.
pose proof HLED as (HLEDin & HIMG).
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HNMrt as (Hq0 & Hql & Hqm & Hqra & Hqhv & Hqtail & Hqap).
pose proof HMK as (HMKb & HMKlen). pose proof HMKb as (HMKbytes & HMKwr).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HIMG as HOFF. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
(* the block is at or above 4096: AR's block law on the ledger fact *)
assert (H4096 : 4096 <= aarg regs 0).
{ pose proof (rem_aj_AR SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ0) as HAR0.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ HAR0 HLEDin) as (_ & H4 & _). exact H4. }
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
destruct (re_aj_bounds SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ0)
  as (Hceil & H47 & HXO & Hpres).
assert (Hnr : 0 <= mk_n gbs <= 32)
  by (pose proof (amk_n_range gbs HWF) as X; unfold MARKS_MAX in X; exact X).
assert (Hpb : aarg regs 0 + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
assert (Hqb : aarg regs 1 + Z.of_nat (length nm) + 8 <= 2 ^ 47 - 1)
  by (unfold amem_range in Hqm; destruct Hqm as [Hx | [_ Hx]]; lia).
assert (HnV : val_mem pa_segs (rdW W memc) (aarg regs 0) 4 (mk_n gbs))
  by exact (amk_n_val pa_segs _ _ gbs HMK).
assert (HFMTa : pa_val 302 = LA_FMT_S).
{ change 302%nat with (A_OBJ 61). rewrite (lv_obj HV 61%nat ltac:(unfold link_nobj; lia)). reflexivity. }
assert (HSIG : pa_sigma LS___interceptor_trampoline_snprintf = LA_W_SNPRINTF)
  by (rewrite (lv_sigma HV); reflexivity).
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
induction d as [|d IH]; intros i regsT memT mdT Hd Hi R1 R2 R8 R9 R10 R11 R18 R19 R20 R21 R22 RS
  F0 F1 F2 F3 F4 F5 F6 F7 UN GR HJT FDs FSs NOT; [lia|].
assert (QspT : spZ regsT = spZ regs - 64)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
(* ---- the call +0x64: slot i against the name ---- *)
eapply SRr_bind.
{ apply (rem_strcmp_call SK B LAWS STRCMP G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT
    (Z_to_bv 64 (pa_val A_TEXT + (AF_remember + 0x68))) (aarg regs 0 + (MK_NAME + MARK_LEN * i)) (aarg regs 1)
    (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) nm HGok HJT HROD Hal16 Hwlo Hwhi UN GR QspT).
  - transitivity (getr regs 3); [exact (RS 3 ltac:(lia)) | exact Hgp].
  - transitivity (getr regs 4); [exact (RS 4 ltac:(lia)) | exact Htp].
  - exact R1.
  - apply ret_ok_codeptr_v; unfold AF_remember; [lia | reflexivity].
  - unfold w64, MK_NAME, MARK_LEN. rewrite R10. f_equal. lia.
  - exact R11.
  - exact (amk_slot_cstr pa_segs _ _ gbs i HMK HWF ltac:(lia)).
  - eapply rem_slot_rt; [exact HMK | exact HWF | reflexivity | exact HBLK | lia].
  - exact HNM.
  - exact HNMrt. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ & HP2 & Hsbm & Hres & Heff & Hpres2).
assert (FD2 : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
{ rewrite (same_but_materialized_wvb _ _ Hsbm), (proj1 (wvb_fds_fs _ _ _)), (proj2 (wvb_fds_fs _ _ _)).
  split; assumption. }
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
          aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memc a)
  by (intros a Ha Hn; rewrite (Heff a Ha ltac:(rewrite QspT; lia)); exact (UN a Ha Hn)).
assert (FR2 : forall b, spZ regs - 64 <= b < spZ regs ->
          mbyte pa_segs (rdW W mem2) b = mbyte pa_segs (rdW W memT) b)
  by (intros b Hb; apply (rem_mbyte_eq_of_aview_eq W); apply Heff; [lia | rewrite QspT; lia]).
assert (GR2 : mem_grows (rdW W memc) (rdW W mem2))
  by (intros x Hx; apply (rem_grows_of_present _ _ _ Hpres2); apply GR; exact Hx).
assert (PR2 : forall x, apresent (w_H W) memc x -> apresent (w_H W) mem2 x)
  by (intros x Hx; exact (apresent_grows _ _ _ x GR2 Hx)).
assert (FK : forall a v, spZ regs - 64 <= a -> a + 8 <= spZ regs ->
          val_mem pa_segs (rdW W memT) a 8 v -> val_mem pa_segs (rdW W mem2) a 8 v)
  by (intros a v H1 H2; apply rem_val_mem_keep; intros b Hb; apply FR2; lia).
pose proof (FK (spZ regs - 64 + 0) _ ltac:(lia) ltac:(lia) F0) as F0'.
pose proof (FK (spZ regs - 64 + 8) _ ltac:(lia) ltac:(lia) F1) as F1'.
pose proof (FK (spZ regs - 64 + 16) _ ltac:(lia) ltac:(lia) F2) as F2'.
pose proof (FK (spZ regs - 64 + 24) _ ltac:(lia) ltac:(lia) F3) as F3'.
pose proof (FK (spZ regs - 64 + 32) _ ltac:(lia) ltac:(lia) F4) as F4'.
pose proof (FK (spZ regs - 64 + 40) _ ltac:(lia) ltac:(lia) F5) as F5'.
pose proof (FK (spZ regs - 64 + 48) _ ltac:(lia) ltac:(lia) F6) as F6'.
pose proof (FK (spZ regs - 64 + 56) _ ltac:(lia) ltac:(lia) F7) as F7'.
assert (HMK2 : amarks_at pa_segs (rdW W mem2) (aarg regs 0) gbs)
  by exact (rem_marks_keep W regs memc mem2 _ gbs UN2 PR2 HBLK HMK).
assert (HBLK2 : amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W mem2) (aarg regs 0))
  by exact (rem_blk_keep W regs memc mem2 _ ltac:(lia) UN2 GR2 HBLK).
assert (Q2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)) by exact HP2.
assert (S2 : getr regs2 2 = Z_to_bv 64 (spZ regs - 64))
  by (rewrite <- R2; exact (Q2 2 ltac:(unfold acallee_saved; lia))).
assert (S8 : getr regs2 8 = Z_to_bv 64 (aarg regs 0))
  by (rewrite <- R8; exact (Q2 8 ltac:(unfold acallee_saved; lia))).
assert (S9 : getr regs2 9 = Z_to_bv 64 (aarg regs 1))
  by (rewrite <- R9; exact (Q2 9 ltac:(unfold acallee_saved; lia))).
assert (S18 : getr regs2 18 = Z_to_bv 64 (aarg regs 0 + 4 + 16 * i))
  by (rewrite <- R18; exact (Q2 18 ltac:(unfold acallee_saved; lia))).
assert (S19 : getr regs2 19 = Z_to_bv 64 (aarg regs 0 + 4))
  by (rewrite <- R19; exact (Q2 19 ltac:(unfold acallee_saved; lia))).
assert (S20 : getr regs2 20 = Z_to_bv 64 (mk_n gbs))
  by (rewrite <- R20; exact (Q2 20 ltac:(unfold acallee_saved; lia))).
assert (S21 : getr regs2 21 = Z_to_bv 64 (RSB + aarg regs 0 / 8))
  by (rewrite <- R21; exact (Q2 21 ltac:(unfold acallee_saved; lia))).
assert (S22 : getr regs2 22 = Z_to_bv 64 (mk_n gbs - i))
  by (rewrite <- R22; exact (Q2 22 ltac:(unfold acallee_saved; lia))).
assert (RS2 : forall r, r = 3 \/ r = 4 \/ 23 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; rewrite (Q2 r ltac:(unfold acallee_saved; lia)); exact (RS r Hr)).
(* ---- the loop state at +0x68, rebuilt from the returned registers ---- *)
assert (HS : st_ok_pi pa_segs pa_val (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) (l_ss_at (AF_remember + 0x68))
               (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (pa_val A_TEXT + (AF_remember + 0x68))) mem2 (seg_rom pa_segs)))).
{ eapply rem_lentry;
    [exact S2 | exact S8 | exact S9 | exact S21 | exact F0' | exact F1' | exact F2' | exact F3' | exact F4'
    | exact F5' | exact F6' | exact F7' | exact HMK2 | exact HWF | reflexivity | exact HBLK2 | exact H4096
    | lia | lia | lia | lia | exact Hal16 | intros a Ha; apply PR2; apply Hpres; lia]. }
assert (SHOK : sh_ok pa_segs rBx lSH (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) (rdW W mem2))
  by exact (rem_lshok W mem2 regs regs2 (aarg regs 0) (mk_n gbs) S8 HBLK2).
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs)))) by apply Eimg_env.
assert (U8 : bv_unsigned (ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) 8) = aarg regs 0).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), S8.
  apply unsigned_lit_small. lia. }
assert (EA : forall a, (a < 42)%nat ->
          ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) a = ew (Ereg regs2 (l_extra (mk_n gbs) regs)) a)
  by (intros a Ha; apply Eimg_low; unfold A_TEXT; lia).
assert (VN33 : bv_unsigned (sv_denot (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) (SOff 33 0))
                 mod 2 ^ (8 * Z.of_N 4) = mk_n gbs).
{ cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs2 (l_extra (mk_n gbs) regs) 1 : ew _ 33 = _).
  cbn [nth l_extra]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia.
  change (2 ^ (8 * Z.of_N 4)) with 4294967296. apply Z.mod_small. lia. }
(* ---- +0x68 `beqz a0` ---- *)
psrr_branch_tok RUN BR HS SHOK rSpan.
- (* hit: slot i is the name *)
  assert (E10 : ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) 10 = getr regs2 10)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
  rewrite (rem_br_eq _ _ _ E10) in Hc. apply Z.eqb_eq in Hc.
  assert (HSL : cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN) = nm).
  { apply Hres. apply bv_eq. rewrite Hc. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  paj_run_tok RUN HS HJ SHOK rSpan.
  { rem_awr regs U8 Hajw. }
  assert (KK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
            mbyte pa_segs (rdW W (ms_mem ms)) a = mbyte pa_segs (rdW W mem2) a) by (rem_kk HFr U8).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_region_nth Ex (abs_ss pa_val ssx) _ 1%nat _ HS eq_refl) as HRG;
    pose proof (field_of_region_any Ex _ 8%nat (aarg regs 0) _ _ _ _ _ 0 4%N _ HRG U8
                  ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HCNT;
    destruct (rem_epi Ex (abs_ss pa_val ssx) msx (w_H W) regs regs2 (mk_n gbs) HS EA S2 ltac:(lia) RS2
                ltac:(vm_compute; reflexivity)) as (HAPR & HRA)
  end.
  rewrite VN33 in HCNT.
  assert (HCNTf : val_mem pa_segs (rdW W (ms_mem ms)) (aarg regs 0) 4 (mk_n gbs)).
  { intros kk Hkk. pose proof (HCNT kk Hkk) as X. cbn [ms_mem restrict] in X.
    rewrite Z.add_0_r in X. exact X. }
  eapply (paj_ret_at (PL := PL_link) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR.
  replace (v_jalr (getr (ms_regs ms) 1) 0) with (getr regs 1)
    by (transitivity (v_jalr (getr regs 1) 0); [symmetry; exact Hraw | f_equal; symmetry; exact HRA]).
  apply (rem_ret_leaf SK B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs nm
           (ms_regs ms) (ms_mem ms) _ HJ0 Hwlo Hwhi HMK HWF HBLK HNM).
  + left. apply (existsb_some _ nm (Z.to_nat i)).
    rewrite amk_names_nth by lia. rewrite Z2Nat.id by lia. rewrite HSL. reflexivity.
  + apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low). exact HJ.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact (proj1 FD2).
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact (proj2 FD2).
  + exact HAPR.
  + exact (rem_run_keep W mem2 (ms_mem ms) memc regs (aarg regs 0) (mk_n gbs) KK1 HCNTf HnV UN2).
  + intros x Hx. apply (apresent_grows (w_H W) memc (ms_mem ms) x); [|exact Hx].
    intros y Hy. exact (HG y (GR2 y Hy)).
- (* miss: slot i is not the name *)
  assert (E10 : ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) 10 = getr regs2 10)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
  rewrite (rem_br_eq _ _ _ E10) in Hc. apply Z.eqb_neq in Hc.
  assert (HSL : cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN) <> nm).
  { intros Heq. apply Hc. apply (proj2 Hres) in Heq. rewrite Heq. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (NOT1 : forall j, 0 <= j < i + 1 -> cstr (slice gbs (MK_NAME + MARK_LEN * j) MARK_LEN) <> nm).
  { intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact HSL | apply NOT; lia]. }
  paj_run_tok RUN HS HJ SHOK rSpan.
  { rem_awr regs U8 Hajw. }
  assert (KK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
            mbyte pa_segs (rdW W (ms_mem ms)) a = mbyte pa_segs (rdW W mem2) a) by (rem_kk HFr U8).
  rename HG into HG1. clear HF HFr.
  clear Hc.
  assert (E22 : ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) 22 = Z_to_bv 64 (mk_n gbs - i))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact S22).
  psrr_branch_tok RUN BR HS SHOK rSpan.
  + (* bnez s6 taken: the next turn *)
    rewrite (rem_br_ne _ 22 (mk_n gbs - i) E22 ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK rSpan.
    { rem_awr regs U8 Hajw. }
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
      assert (KK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
                mbyte pa_segs (rdW W mB) a = mbyte pa_segs (rdW W mem2) a)
        by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
            intros a Ha Hn; transitivity (mbyte pa_segs (rdW W mA) a);
            [revert a Ha Hn; rem_kk HFr U8 | exact (KK1 a Ha Hn)])
    end.
    lazymatch type of HS with
    | st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_region_nth Ex ssx _ 1%nat _ HS eq_refl) as HRG;
      pose proof (field_of_region_any Ex _ 8%nat (aarg regs 0) _ _ _ _ _ 0 4%N _ HRG U8
                    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HCNT
    end.
    rewrite VN33 in HCNT.
    pmkst HS.
    prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 2) Q2'. prreg HS (Z_to_bv 5 8) Q8.
    prreg HS (Z_to_bv 5 9) Q9. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
    prreg HS (Z_to_bv 5 18) Q18. prreg HS (Z_to_bv 5 19) Q19. prreg HS (Z_to_bv 5 20) Q20.
    prreg HS (Z_to_bv 5 21) Q21. prreg HS (Z_to_bv 5 22) Q22.
    cbn [A_TEXT A_LIM Nat.leb andb] in Q1, Q2', Q8, Q9, Q10, Q11, Q18, Q19, Q20, Q21, Q22.
    assert (HCNTf : val_mem pa_segs (rdW W (ms_mem ms0)) (aarg regs 0) 4 (mk_n gbs)).
    { intros kk Hkk. pose proof (HCNT kk Hkk) as X. cbn [ms_mem restrict] in X.
      rewrite Z.add_0_r in X. exact X. }
    assert (FK2 : forall a v, spZ regs - 64 <= a -> a + 8 <= spZ regs ->
              val_mem pa_segs (rdW W mem2) a 8 v -> val_mem pa_segs (rdW W (ms_mem ms0)) a 8 v).
    { intros a v H1 H2. apply rem_val_mem_keep. intros b Hb. apply KK2; [lia|].
      unfold apart_frame, MK_SIZE in Hpap. lia. }
    assert (HAE : env_agree 32 (Ereg regs2 (l_extra (mk_n gbs) regs))
                    (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))))
      by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    apply (IH (i + 1)).
    * lia.
    * lia.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 1)); [reflexivity|].
      rewrite Q1, unsigned_lit_small by (pose proof (pa_val_range 240); lia). reflexivity.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 2)); [reflexivity|].
      rewrite Q2', (ew_Ereg_nat regs2 _ 2 2%bv eq_refl). exact S2.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 8)); [reflexivity|].
      rewrite Q8, (ew_Ereg_nat regs2 _ 8 8%bv eq_refl). exact S8.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 9)); [reflexivity|].
      rewrite Q9, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). exact S9.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 10)); [reflexivity|].
      rewrite Q10, (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), S18, unsigned_lit_small by lia.
      f_equal. lia.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 11)); [reflexivity|].
      rewrite Q11, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). exact S9.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 18)); [reflexivity|].
      rewrite Q18, (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), S18, unsigned_lit_small by lia.
      f_equal. lia.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 19)); [reflexivity|].
      rewrite Q19, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl). exact S19.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 20)); [reflexivity|].
      rewrite Q20, (ew_Ereg_nat regs2 _ 20 20%bv eq_refl). exact S20.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 21)); [reflexivity|].
      rewrite Q21, (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), S8.
      rewrite (ew_Ereg_extra regs2 (l_extra (mk_n gbs) regs) 0 : ew _ 32 = _). cbn [nth l_extra].
      rewrite rl_srl3 by lia.
      assert (Hd8 : 0 <= aarg regs 0 / 8 < 2 ^ 44)
        by (pose proof (Z.div_pos (aarg regs 0) 8 ltac:(lia) ltac:(lia));
            split; [lia | apply Z.div_lt_upper_bound; lia]).
      rewrite alu_add_small by (unfold M64, RSB; lia). f_equal. lia.
    * transitivity (getr (ms_regs ms0) (Z_to_bv 5 22)); [reflexivity|].
      rewrite Q22, (ew_Ereg_nat regs2 _ 22 22%bv eq_refl), S22, unsigned_lit_small by lia.
      f_equal. lia.
    * intros r Hr. rewrite <- (RS2 r Hr).
      assert (Hr' : r = 3 \/ r = 4 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      lazymatch type of HS with
      | st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
        destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
        match goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
          exact (regs_kept_of_st_ok pa_segs Ex ssx (restrict (w_H W) msx) regs2 (l_extra (mk_n gbs) regs)
                   [Z_to_bv 5 rr] HS HAE ltac:(vm_compute; reflexivity) (Z_to_bv 5 rr) (or_introl eq_refl))
        end
      end.
    * apply FK2; [lia | lia | exact F0'].
    * apply FK2; [lia | lia | exact F1'].
    * apply FK2; [lia | lia | exact F2'].
    * apply FK2; [lia | lia | exact F3'].
    * apply FK2; [lia | lia | exact F4'].
    * apply FK2; [lia | lia | exact F5'].
    * apply FK2; [lia | lia | exact F6'].
    * apply FK2; [lia | lia | exact F7'].
    * exact (rem_run_keep W mem2 (ms_mem ms0) memc regs (aarg regs 0) (mk_n gbs) KK2 HCNTf HnV UN2).
    * intros x Hx. apply HG. apply HG1. apply GR2. exact Hx.
    * exact HJ.
    * repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact (proj1 FD2).
    * repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact (proj2 FD2).
    * exact NOT1.
  + (* bnez s6 not taken: every slot differs from the name *)
    rewrite (rem_br_ne _ 22 (mk_n gbs - i) E22 ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK rSpan.
    { rem_awr regs U8 Hajw. }
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
      assert (KK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
                mbyte pa_segs (rdW W mB) a = mbyte pa_segs (rdW W mem2) a)
        by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
            intros a Ha Hn; transitivity (mbyte pa_segs (rdW W mA) a);
            [revert a Ha Hn; rem_kk HFr U8 | exact (KK1 a Ha Hn)])
    end.
    rename HG into HG2. clear HF HFr KK1.
    assert (NOTn : forall j, 0 <= j < mk_n gbs -> cstr (slice gbs (MK_NAME + MARK_LEN * j) MARK_LEN) <> nm)
      by (intros j Hj; apply NOT1; lia).
    assert (HEX : existsb (fun y => bl_eqb y nm) (mk_names gbs) = false).
    { apply existsb_none. intros j Hj. rewrite amk_names_length in Hj.
      rewrite amk_names_nth by exact Hj. intros Heq. injection Heq as Heq.
      exact (NOTn (Z.of_nat j) ltac:(lia) Heq). }
    assert (E20 : ew (Eimg (Ereg regs2 (l_extra (mk_n gbs) regs))) 20 = Z_to_bv 64 (mk_n gbs))
      by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact S20).
    clear Hc.
    psrr_branch_tok RUN BR HS SHOK rSpan.
    * (* bge a0, s4 taken: n <= 31, the append +0xa8 .. +0xf4 *)
      assert (Hn31 : mk_n gbs <= 31).
      { revert Hc. cbn [sv_denot]. rewrite E20, Z.add_0_r, unsigned_lit_small by lia.
        cbn [branch_taken]. unfold bv_lts.
        rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia).
        rewrite !unsigned_lit_small by lia.
        intros H. destruct (Z.ltb_spec 31 (mk_n gbs)); cbn in H; [discriminate | lia]. }
      paj_run_tok RUN HS HJ SHOK rSpan.
      { rem_awr regs U8 Hajw. }
      lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
        assert (KK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
                  mbyte pa_segs (rdW W mB) a = mbyte pa_segs (rdW W mem2) a)
          by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
              intros a Ha Hn; transitivity (mbyte pa_segs (rdW W mA) a);
              [revert a Ha Hn; rem_kk HFr U8 | exact (KK2 a Ha Hn)])
      end.
      lazymatch type of HS with
      | st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
        assert (U8x : bv_unsigned (ew Ex 8) = aarg regs 0) by (rewrite !ew_ewset_other by lia; exact U8);
        assert (EAx : forall a, (a < 42)%nat -> ew Ex a = ew (Ereg regs2 (l_extra (mk_n gbs) regs)) a)
          by (intros a Ha; rewrite !ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia);
        assert (VN : bv_unsigned (sv_denot Ex (SOff 20 1)) mod 2 ^ (8 * Z.of_N 4) = mk_n gbs + 1)
          by (cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite E20;
              rewrite (unsigned_lit_small (mk_n gbs)) by lia; rewrite unsigned_lit_small by lia;
              change (2 ^ (8 * Z.of_N 4)) with 4294967296; apply Z.mod_small; lia);
        pose proof (st_ok_region_nth Ex ssx _ 1%nat _ HS eq_refl) as HRG;
        pose proof (field_of_region_any Ex _ 8%nat (aarg regs 0) _ _ _ _ _ 0 4%N _ HRG U8x
                      ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HCNT;
        rewrite VN in HCNT;
        destruct (rem_epi Ex ssx msx (w_H W) regs regs2 (mk_n gbs) HS EAx S2 ltac:(lia) RS2
                    ltac:(vm_compute; reflexivity)) as (HAPR & HRA);
        assert (HCNTf : val_mem pa_segs (rdW W (ms_mem msx)) (aarg regs 0) 4 (mk_n gbs + 1))
          by (intros kk Hkk; pose proof (HCNT kk Hkk) as X; cbn [ms_mem restrict] in X;
              rewrite Z.add_0_r in X; exact X);
        assert (PRGx : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
          by (intros x Hx; apply (apresent_grows (w_H W) memc (ms_mem msx) x); [|exact Hx];
              intros y Hy; exact (HG y (HG2 y (HG1 y (GR2 y Hy)))))
      end.
      pmkst HS.
      prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
      prreg HS (Z_to_bv 5 12) Q12. prreg HS (Z_to_bv 5 13) Q13.
      cbn [A_TEXT A_LIM Nat.leb andb] in Q10, Q11, Q12, Q13.
      rewrite HSIG.
      eapply (rem_append_tail SK B LAWS SNP TB HSEGS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                regs gbs nm _ _ _ HJ0 HGok HROD Hraw Hra4 Hgp Htp Hal16 Hwlo Hwhi Hajw Hnro
                Hfrm0 HMK HWF HLED HBLK Hqnz HNM Hlen HNMrt Hapart HFMT HFMTrt).
      -- exact Hn31.
      -- exact HEX.
      -- exact HJ.
      -- repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact (proj1 FD2).
      -- repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact (proj2 FD2).
      -- exact HAPR.
      -- exact HRA.
      -- match goal with |- getr ?rg _ = _ => transitivity (getr rg (Z_to_bv 5 10)); [reflexivity|] end.
         rewrite Q10, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), S19, (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), S20.
         rewrite (YI08.alu64_sll_lit (mk_n gbs) 4) by lia. change (2 ^ 4) with 16.
         rewrite alu_add_small by (unfold M64; lia).
         unfold w64, MK_NAME, MARK_LEN. f_equal. lia.
      -- exact Q11.
      -- match goal with |- getr ?rg _ = _ => transitivity (getr rg (Z_to_bv 5 12)); [reflexivity|] end.
         rewrite Q12, HFMTa. reflexivity.
      -- match goal with |- getr ?rg _ = _ => transitivity (getr rg (Z_to_bv 5 13)); [reflexivity|] end.
         rewrite Q13, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), S9. reflexivity.
      -- intros a Ha H1 H2. rewrite (KK3 a Ha H2). apply (rem_mbyte_eq_of_aview_eq W). exact (UN2 a Ha H1).
      -- exact HCNTf.
      -- exact PRGx.
    * (* bge a0, s4 not taken: n = 32, the list is full *)
      assert (Hn32 : mk_n gbs = MARKS_MAX).
      { unfold MARKS_MAX. revert Hc. cbn [sv_denot]. rewrite E20, Z.add_0_r, unsigned_lit_small by lia.
        cbn [branch_taken]. unfold bv_lts.
        rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia).
        rewrite !unsigned_lit_small by lia.
        intros H. destruct (Z.ltb_spec 31 (mk_n gbs)); cbn in H; [lia | discriminate]. }
      paj_run_tok RUN HS HJ SHOK rSpan.
      { rem_awr regs U8 Hajw. }
      lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
        assert (KK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
                  mbyte pa_segs (rdW W mB) a = mbyte pa_segs (rdW W mem2) a)
          by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
              intros a Ha Hn; transitivity (mbyte pa_segs (rdW W mA) a);
              [revert a Ha Hn; rem_kk HFr U8 | exact (KK2 a Ha Hn)])
      end.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        assert (U8x : bv_unsigned (ew Ex 8) = aarg regs 0) by (rewrite ?ew_ewset_other by lia; exact U8);
        assert (EAx : forall a, (a < 42)%nat -> ew Ex a = ew (Ereg regs2 (l_extra (mk_n gbs) regs)) a)
          by (intros a Ha; rewrite ?ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia);
        assert (VN : bv_unsigned (sv_denot Ex (SOff 33 0)) mod 2 ^ (8 * Z.of_N 4) = mk_n gbs)
          by (etransitivity; [|exact VN33]; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; reflexivity);
        pose proof (st_ok_region_nth Ex (abs_ss pa_val ssx) _ 1%nat _ HS eq_refl) as HRG;
        pose proof (field_of_region_any Ex _ 8%nat (aarg regs 0) _ _ _ _ _ 0 4%N _ HRG U8x
                      ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HCNT;
        rewrite VN in HCNT;
        destruct (rem_epi Ex (abs_ss pa_val ssx) msx (w_H W) regs regs2 (mk_n gbs) HS EAx S2 ltac:(lia) RS2
                    ltac:(vm_compute; reflexivity)) as (HAPR & HRA);
        assert (HCNTf : val_mem pa_segs (rdW W (ms_mem msx)) (aarg regs 0) 4 (mk_n gbs))
          by (intros kk Hkk; pose proof (HCNT kk Hkk) as X; cbn [ms_mem restrict] in X;
              rewrite Z.add_0_r in X; exact X);
        assert (PRGx : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
          by (intros x Hx; apply (apresent_grows (w_H W) memc (ms_mem msx) x); [|exact Hx];
              intros y Hy; exact (HG y (HG2 y (HG1 y (GR2 y Hy)))));
        assert (UNx : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
                  aview pa_segs (w_H W) (ms_mem msx) a = aview pa_segs (w_H W) memc a)
          by exact (rem_run_keep W mem2 (ms_mem msx) memc regs (aarg regs 0) (mk_n gbs) KK3 HCNTf HnV UN2);
        eapply (paj_ret_at (PL := PL_link) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        let matR := fresh "matR" in intros matR;
        replace (v_jalr (getr (ms_regs msx) 1) 0) with (getr regs 1)
          by (transitivity (v_jalr (getr regs 1) 0); [symmetry; exact Hraw | f_equal; symmetry; exact HRA]);
        apply (rem_ret_leaf SK B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs nm
                 (ms_regs msx) (ms_mem msx) _ HJ0 Hwlo Hwhi HMK HWF HBLK HNM)
      end.
      -- right. exact Hn32.
      -- apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low). exact HJ.
      -- repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact (proj1 FD2).
      -- repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact (proj2 FD2).
      -- exact HAPR.
      -- exact UNx.
      -- exact PRGx.
Qed.

End b.
End a.

About rem_loop.
Print Assumptions rem_loop.
