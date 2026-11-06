(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 211 of its 262 lines of code are new or changed and 402 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA: the cut KEY 0x8661c to the
   memchr wrapper's return (mf_keya_d.v kb_key : KB_RMC_stmt n -> MF_KEY_stmt n):
     0x8661c  li a1,61                      the byte searched for is 0x3d ('=' , SegModel.EQ)
     0x86620  mv a0,s10                     a0 = s = p + i, a2 = e - s = j - i (set before the cut, 0x864e8)
     0x86624  jal 43ac8 <wrapper_memchr>    memchr(s, 61, j - i), its return 0x86628 = KB_RMC
   One FP state (memchr's post keeps it). The step is m_file_memchr.v's aj_memchr_atM on the
   interceptor row 20 text MemchrDef.amemchr_realizesM at musl's constant window SegInstB.memchr_loA .. memchr_hiA;
   the window's read-only view comes from the walk's image fact MCROM and m_file_k.v's mf_rod_now. A light seed at
   KEY (every register its own atom, no region: the two instructions read no memory), and every cut fact crosses the
   call by m_file_k.v's mf_keep_win0 (memchr writes only [s1 - ESTACK, s1)). The answer becomes SegModel.memchr of
   the stripped line by mf_keya_m.v's kb_memchr_found / kb_memchr_nf.
   The template is image A's m_file_s_keya_a.v (commit ddef332b859f, its KEY-to-memchr half) at
   image B's registers (s = s10 = x26, e = s4 = x20, the length in a2 = x12, line + 1 in s11 = x27).
   A walk lane of the image-B m_file-family owner's G2B. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_m mf_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the light state at KEY: every register its own atom, no region (the two instructions read no memory) *)
Definition kk_ss : sstate := mkSS MF_KEY sr_atoms [] None (mkFacts [ (18%nat, mkAF SB SB 0) ] [] []).
Definition kk_Bx : sv := SOff 18 0.
(* the registers neither the run (a0, a1, ra) nor memchr (the callee-saved set) writes *)
Definition KK_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition kk_E (regs1 : bvmap 5 word) : env := Eimg (Ereg regs1 []).
Lemma kk_ew_reg : forall regs1 n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (kk_E regs1) n = getr regs1 r.
Proof.
intros regs1 n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold kk_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma kk_env_agree : forall regs1, env_agree 32 (Ereg regs1 []) (kk_E regs1).
Proof. intros. split; [intros n Hn; unfold kk_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma kk_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc,
getr regs1 18 = w64 SHADOW_OFF ->
st_ok_pi SEGS VAL (kk_E regs1) kk_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + MF_KEY)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc H18.
assert (E18 : ew (kk_E regs1) 18 = Z_to_bv 64 SB) by (rewrite (kk_ew_reg regs1 18 18%bv eq_refl); exact H18).
rewrite restrict_mkst_fx. unfold kk_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* a run over read-only regions keeps every view *)
Lemma kk_keep_step : forall E rs (m0 m m' : word -> option byte) (H : word -> bool),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H HFr HW KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. pose proof (HW b wlo whi Hin). lia.
Qed.
Lemma kk_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
(* the shadow hull of a sub-range (image A's a_hull_sub) *)
Lemma kk_hull_sub : forall (rd : reader) q nn x m, shadow_hull_vis rd q nn -> 0 <= q -> q <= x -> x + m <= q + nn ->
0 < m -> shadow_hull_vis rd x m.
Proof.
unfold shadow_hull_vis, shadow_addr. intros rd q nn x m H Hq Hx Hxm Hm s Hs. apply H.
pose proof (Z.div_le_mono q x 8 ltac:(lia) Hx) as D1.
pose proof (Z.div_le_mono (SHADOW_OFF + q / 8) (SHADOW_OFF + x / 8) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (x + m - 1) (q + nn - 1) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x + m - 1) / 8) (SHADOW_OFF + (q + nn - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstB.memchr_loA SegInstB.memchr_hiA
    (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Ltac kk_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let En := lazymatch goal with
      | HS : st_ok_pi _ _ ?En _ (restrict _ msn) |- _ => En
      | HS : st_ok _ ?En _ (restrict _ msn) |- _ => En end in
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (kk_keep_step Eo rs _ _ _ _ HFr ltac:(intros b wlo whi Hin; vm_compute in Hin; repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac kk_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac kk_kept := cbv [KK_KEPT In]; tauto.

Lemma kb_key : forall n, KB_RMC_stmt B n -> MF_KEY_stmt B n.
Proof.
intros n RMC. unfold MF_KEY_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j CX LS FRM CORE CELLS RG Hn Hr LOOP HL Hij HjL HSL
  HLBR HFIN R26 R20 R12 R21 NP R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & (Ht00 & _) & _).
pose proof CORE as (HJ & HPm & _).
pose proof LOOP as (LP1 & LP2 & LP3 & LSTR & LADDR & LCUR & _).
pose proof LADDR as (Hp0 & Hp63 & HAM & HRA & HHULL).
pose proof LSTR as ((ZS & _) & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
assert (HES : ESTACK = 4096) by reflexivity.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs1m & _).
assert (Hs1o : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E | E]; rewrite E; [replace (mv_sp v - 320 - mv_sp v) with (-320) by lia
      | replace (mv_sp v - 336 - mv_sp v) with (-336) by lia]; reflexivity).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
set (s1 := mf_s1 (mv_sp v)) in *.
assert (Hs1b : alloc_ceiling + 16 + ESTACK <= s1 /\ s1 + 336 <= mv_sp v + 16 /\ s1 < 2 ^ 47)
  by (destruct Hs1 as [E | E]; rewrite E; lia).
pose proof (kb_line_len rest) as HLr.
set (L := mf_line rest) in *.
set (sl := slice i j L) in *.
assert (Hsl : length sl = (j - i)%nat) by (subst sl; apply kb_slice_length; lia).
(* the bytes of the stripped line in memory, and where the text lies *)
assert (HSB : forall k, (k < length sl)%nat -> rdW Wc memc (p + Z.of_nat i + Z.of_nat k) = Some (nth k sl 0)).
{ intros k Hk. rewrite Hsl in Hk. replace (p + Z.of_nat i + Z.of_nat k) with (p + Z.of_nat (i + k)%nat) by lia.
  rewrite (ZS (i + k)%nat ltac:(rewrite length_app; cbn [length]; lia)). f_equal. rewrite app_nth1 by lia.
  subst sl L. symmetry. apply kb_sl_byte; lia. }
assert (HBS : forall a, p <= a < p + Z.of_nat (length rest) + 1 -> a < s1 - 2 * ESTACK).
{ intros a Ha. pose proof (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as HTH.
  apply (mf_heap_below_stack B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CX CORE HTH). rewrite LP3 in Ha. lia. }
(* ---- KEY to the memchr call: li a1,61; mv a0,s10; jal ---- *)
pose proof (kk_entry Wc regs1 memc R18) as HS.
assert (SHOK : sh_ok SEGS kk_Bx [] (kk_E regs1) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kk_E regs1)) by (unfold kk_E; apply Eimg_env).
pose proof (kk_env_agree regs1) as HA0.
assert (E26 : ew (kk_E regs1) 26 = Z_to_bv 64 (p + Z.of_nat i))
  by (rewrite (kk_ew_reg regs1 26 26%bv eq_refl); exact R26).
assert (E12 : ew (kk_E regs1) 12 = Z_to_bv 64 (Z.of_nat (j - i)))
  by (rewrite (kk_ew_reg regs1 12 12%bv eq_refl); exact R12).
revert HS SHOK HEI HA0 E26 E12. generalize (kk_E regs1) as E0. intros E0 HS SHOK HEI HA0 E26 E12.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
unfold mf_at.
paj_run_tok RUN HS HJ SHOK Bspan; [ kk_awr | ].
kk_after E0 HAE KM.
lazymatch goal with HS : st_ok _ ?En ?ssx (restrict _ ?msx) |- _ =>
  pose proof (regs_kept_of_st_ok SEGS En ssx (restrict (w_H Wc) msx) regs1 [] KK_KEPT HS (kk_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK1 end.
cbn [ms_regs restrict] in HK1.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?mdx) _ => set (rg := r) in *; set (mm := m) in *; set (md1 := mdx) in * end.
assert (HRT : rdW Wc mm = rdW Wc memc).
{ apply functional_extensionality. apply (mf_aview_all (w_H Wc) memc mm). intros a Ha. exact (KM a Ha). }
assert (G2 : getr rg 2 = w64 s1) by (rewrite (HK1 2%bv) by kk_kept; exact R2).
assert (Usp : spZ rg = s1) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hx0 : 0 < p + Z.of_nat i) by lia.
set (nn := Z.of_nat (j - i)) in *.
set (x := p + Z.of_nat i) in *.
(* ---- memchr(s, '=', j - i) ---- *)
eapply SRr_bind.
{ apply (aj_memchr_atM SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_memchr) SegInstB.RLO_A
    SegInstB.RHI_A (AMEMCHR fx) MCROM Wc rg mm SegInstB.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc
    md1 0 x 61 nn (s1 - mv_sp v) (Z_to_bv 64 (BASE + KB_RMC)) HJ).
  - rewrite Q10, E26. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q12, E12. reflexivity.
  - lia.
  - subst nn. lia.
  - exact Hx0.
  - subst nn x. lia.
  - rewrite Usp. lia.
  - exact Hs1o.
  - lia.
  - rewrite HES, HSTK. lia.
  - rewrite (HK1 3%bv) by kk_kept. exact R3.
  - rewrite (HK1 4%bv) by kk_kept. exact R4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold KB_RMC, AF_m_file; lia | vm_compute; reflexivity].
  - intros a Ha. rewrite HRT, Usp. split.
    + replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
      rewrite HSB by (rewrite Hsl; subst nn; lia). discriminate.
    + pose proof (HBS a ltac:(subst x nn; lia)). lia.
  - unfold amem_range in *. subst x nn. lia.
  - rewrite HRT. exact (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) x nn HRA ltac:(subst x nn; lia)
      ltac:(subst x nn; lia)).
  - intros Hn0. rewrite HRT. apply (kk_hull_sub _ p (Z.of_nat (length rest) + 1));
      [apply HHULL; lia | lia | subst x; lia | subst x nn; lia | lia].
  - rewrite HRT. exact (mf_rod_now B RELRO v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HFB & HRES & HK2 & HPR2).
replace (mv_sp v + (s1 - mv_sp v)) with s1 in HK2 by lia.
(* every byte outside memchr's window as at KEY *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - ESTACK <= a < s1) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw. rewrite (HK2 a Ha Hw). exact (KM a Ha). }
(* the registers kept from KEY *)
assert (HKA : forall r, In r KK_KEPT -> getr regs2 r = getr regs1 r).
{ intros r Hrr. rewrite <- (HK1 r) by exact Hrr.
  rewrite <- (Z_to_bv_bv_unsigned _ r). apply HP2.
  cbv [KK_KEPT In] in Hrr. unfold acallee_saved.
  repeat (destruct Hrr as [<- | Hrr];
    [lazymatch goal with |- context [bv_unsigned ?b] =>
       let z := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with z end; lia |]).
  destruct Hrr. }
(* the cut facts at memchr's return *)
destruct (mf_keep_win0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur Sc Wc mem2 md2 (s1 - ESTACK) s1 CX CORE CELLS
  HJ2 (Permutation_refl _) ltac:(rewrite HSTK, HES; lia) ltac:(lia) K2) as (CORE2 & CELLS2 & NPf & LOOPf).
pose proof (NPf _ NP) as NP2. pose proof (LOOPf mcc cur line p rest LOOP) as LOOP2.
assert (RG2 : mf_regs_at B v lyc pos regs2).
{ apply (mf_regs_at_of B v lyc pos regs1 regs2 RG); apply HKA; kk_kept. }
(* the bytes memchr read, through the run's memory *)
assert (HSB' : forall k, (k < length sl)%nat -> rdW Wc mm (x + Z.of_nat k) = Some (nth k sl 0))
  by (intros k Hk; rewrite HRT; exact (HSB k Hk)).
pose proof HFB as (Hkk & Hpre & Hat).
(* the model at KB_RMC is m_key's at the stripped line *)
assert (HFIN' : mf_fin (m_key mcc cur sl (line + 1), cur) line rest = mf_final v) by (subst sl L; rewrite HSL; exact HFIN).
(* memchr's answer as SegModel.memchr of the stripped line *)
assert (HRESM : exists res, getr regs2 10 = w64 res /\
  match memchr sl EQ with Some ei => res = p + Z.of_nat (i + ei) | None => res = 0 end).
{ destruct (Z.ltb_spec kk nn) as [Hkn | Hkn].
  - exists (x + kk). split; [rewrite HRES; reflexivity|].
    assert (Hei : memchr sl EQ = Some (Z.to_nat kk)).
    { apply (kb_memchr_found sl (rdW Wc mm) x 61 kk HSB'); [rewrite Hsl; subst nn; lia | exact Hpre | exact (Hat Hkn)]. }
    rewrite Hei. subst x. lia.
  - exists 0. split; [rewrite HRES; reflexivity|].
    assert (Hnf : memchr sl EQ = None).
    { apply (kb_memchr_nf sl (rdW Wc mm) x 61 HSB'). intros i' Hi'. apply Hpre. rewrite Hsl in Hi'. subst nn. lia. }
    rewrite Hnf. reflexivity. }
destruct HRESM as (res & HR10 & HRM).
apply (RMC v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i j res
  CX LS FRM CORE2 CELLS2 RG2 Hn Hr LOOP2 Hij HjL).
- exact HRM.
- exact HFIN'.
- exact HR10.
- rewrite HKA by kk_kept. exact R26.
- rewrite HKA by kk_kept. exact R20.
- rewrite HKA by kk_kept. exact R27.
- exact NP2.
Qed.
End e.
End f.
End d.
