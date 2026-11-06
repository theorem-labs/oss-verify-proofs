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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 400 of its 444 lines of code are new or changed and 409 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: KEY 0x8633c to the key's front strip (L1 0x86364 or
   J1 0x86434) or to the refusal (0x863ac jal m_refuse):
     0x8633c  li a1,61; mv a0,s11; jal memchr        memchr(s, '=', e - s), s = p + i, e - s = j - i in a2
     0x86348  ld a1,136(s1); beqz a1 -> 0x863a4      cur = NULL: refused
     0x86350  beqz a0 -> 0x863a4                     no '=' in [s, e): refused
     0x86354  bgeu s11,a0 -> J1                      the '=' first: an empty key, J1 at i
     0x86358  sub a2,a0,s11; add a2,s11,a2; mv a1,s11   L1 at q = i
     0x863a4  mv a0,s5; mv a1,s6; 0x863ac jal m_refuse   KA_REF_stmt (m_file_s_keya_r.v)
   ka_key : KA_REF_stmt n -> KA_L1_stmt n -> KA_J1_stmt n -> MF_KEY_stmt n (one FP state: memchr's post keeps it).
   Two light seeds (every register its own atom): at KEY with no region (the run to the call reads no memory), and
   at memchr's return 0x86348 with the cur slot 136(s1) as a read-only region (atom 32). The memchr step is
   m_file_memchr.v's aj_memchr_atM; every cut fact crosses the call by m_file_k.v's mf_keep_win0 (memchr writes only
   [s1 - ESTACK, s1)). The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_memchr m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_keya_m m_file_s_keya_d m_file_s_keya_k m_file_s_keya_r.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the light states: at KEY no region; at memchr's return the cur slot 136(s1) (base s1 = atom 9) as atom 32 *)
Definition a0_ss : sstate := mkSS MF_KEY sr_atoms [] None (mkFacts [ (18%nat, mkAF SB SB 0) ] [] []).
Definition a1_regions : smem := [ YP09.mkRegion (Some 9%nat) 136 144 0 0 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))] ].
Definition a1_ss : sstate := mkSS KA_RMC sr_atoms a1_regions None (mkFacts [ (18%nat, mkAF SB SB 0) ] [] []).
Definition a_Bx : sv := SOff 18 0.
(* the registers neither run nor memchr writes, kept from KEY to every leaf *)
Definition KA_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the registers a run keeps (run 1 writes a0, a1, ra; run 2 a0, a1, a2) *)
Definition A_RUN_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition a_E (regs1 : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs1 (map (Z_to_bv 64) xs)).
Lemma a_ew_reg : forall regs1 xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (a_E regs1 xs) n = getr regs1 r.
Proof.
intros regs1 xs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold a_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma a_ew32 : forall regs1 x, ew (a_E regs1 [x]) 32 = Z_to_bv 64 x.
Proof. intros. unfold a_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma a_env_agree : forall regs1 xs, env_agree 32 (Ereg regs1 (map (Z_to_bv 64) xs)) (a_E regs1 xs).
Proof. intros. split; [intros n Hn; unfold a_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Lemma a0_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc,
getr regs1 18 = w64 SHADOW_OFF ->
st_ok_pi SEGS VAL (a_E regs1 []) a0_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + MF_KEY)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc H18.
assert (E18 : ew (a_E regs1 []) 18 = Z_to_bv 64 SB) by (rewrite (a_ew_reg regs1 [] 18 18%bv eq_refl); exact H18).
rewrite restrict_mkst_fx. unfold a0_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma a1_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 cv,
getr regs1 9 = w64 s1 -> getr regs1 18 = w64 SHADOW_OFF -> 0 <= s1 -> s1 + 144 <= 2 ^ 64 -> 0 <= cv < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) memc) (s1 + 136) 8 cv ->
st_ok_pi SEGS VAL (a_E regs1 [cv]) a1_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KA_RMC)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 cv H9 H18 Hs0 Hs1 Hcv V136.
set (E := a_E regs1 [cv]).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (a_ew_reg regs1 [cv] 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite (a_ew_reg regs1 [cv] 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 cv) by (subst E; apply a_ew32).
rewrite restrict_mkst_fx. unfold a1_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s1 136 8 (SOff 32 0) cv);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V136].
- exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* a run over read-only regions keeps every view; with a set Zs left out, the same *)
Lemma a_keep_step : forall E rs (m0 m m' : word -> option byte) (H : word -> bool) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H Zs HFr HW KM a Ha HZ.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HFr); [exact (KM a Ha HZ) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. pose proof (HW b wlo whi Hin). lia.
Qed.
Lemma a_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma a_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma a_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H R Hc. rewrite branch_eq_U, (U_atom E n v H R), U_lit in Hc by lia. exact Hc.
Qed.
Lemma a_br_geu : forall E n1 v1 n2 v2 b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = b -> negb (v1 <? v2) = b.
Proof.
intros E n1 v1 n2 v2 b H1 H2 R1 R2 Hc.
rewrite branch_geu_U, (U_atom E n1 v1 H1 R1), (U_atom E n2 v2 H2 R2) in Hc. exact Hc.
Qed.

Section e.
(* the shadow hull of a sub-range *)
Lemma a_hull_sub : forall (rd : reader) p n x m, shadow_hull_vis rd p n -> 0 <= p -> p <= x -> x + m <= p + n -> 0 < m ->
shadow_hull_vis rd x m.
Proof.
unfold shadow_hull_vis, shadow_addr. intros rd p n x m H Hp Hx Hxm Hm s Hs. apply H.
pose proof (Z.div_le_mono p x 8 ltac:(lia) Hx) as D1.
pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + x / 8) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (x + m - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x + m - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstA.memchr_loA SegInstA.memchr_hiA (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac a_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let En := lazymatch goal with
      | HS : st_ok_pi _ _ ?En _ (restrict _ msn) |- _ => En
      | HS : st_ok _ ?En _ (restrict _ msn) |- _ => En end in
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (a_keep_step Eo rs _ _ _ _ _ HFr ltac:(intros b wlo whi Hin; vm_compute in Hin; repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac a_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* the leaf at the refusal's jal (a0 = s5 = c, a1 = s6 = line + 1), after the run from memchr's return *)
Ltac a_ref_leaf regs2 HA2 HAE HKA HJ2 KM F21 F22 CREF Hm :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ _) |- _ =>
    let HK3 := fresh "HK3" in let N10 := fresh "N10" in let N11 := fresh "N11" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ A_RUN_KEPT HS (a_ag32 _ _ _ _ HA2 HAE)
      ltac:(vm_compute; reflexivity)) as HK3;
    cbn [ms_regs restrict] in HK3;
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11;
    pmkst HS;
    exact (CREF _ _ _ Hm HJ2 KM (fun r Hrr => eq_trans (HK3 r Hrr) (HKA r Hrr))
      ltac:(rewrite N10, F21; reflexivity) ltac:(rewrite N11, F22; reflexivity))
  end.

Lemma ka_key : forall n, KA_REF_stmt B n -> KA_L1_stmt B n -> KA_J1_stmt B n -> MF_KEY_stmt B n.
Proof.
intros n REF L1 J1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j CX LS FRM CORE CELLS RG R24 Hn Hr LOOP
  HL Hij HjL HSL HLBR HFIN R27 R23 R12 R17 NP R22 R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & (Ht00 & _) & _).
pose proof CORE as (HJ & HPm & _ & _ & _ & _ & HMC & _).
pose proof LOOP as (LP1 & LP2 & LP3 & LSTR & LADDR & LCUR & _).
pose proof LADDR as (Hp0 & Hp63 & HAM & HRA & HHULL).
pose proof LSTR as ((ZS & _) & _).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (mf_line_len rest) as HLr.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & _).
assert (Hs1m : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E | E]; rewrite E; [replace (mv_sp v - 288 - mv_sp v) with (-288) by lia
      | replace (mv_sp v - 304 - mv_sp v) with (-304) by lia]; reflexivity).
change (spZ (mv_regs v)) with (mv_sp v) in *.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (s1 := mf_s1 (mv_sp v)) in *.
assert (Hs1b : alloc_ceiling + 16 + ESTACK <= s1 /\ s1 + 304 <= mv_sp v + 16 /\ s1 < 2 ^ 47).
{ destruct Hs1 as [E | E]; rewrite E; lia. }
set (L := mf_line rest) in *.
set (sl := slice i j L) in *.
assert (Hsl : length sl = (j - i)%nat) by (subst sl; apply slice_length; lia).
assert (HFIN' : mf_fin (m_key mcc cur sl (line + 1), cur) line rest = mf_final v) by (rewrite HSL; exact HFIN).
(* the bytes of sl in memory, and where the text lies *)
assert (HSB : forall k, (k < length sl)%nat -> rdW Wc memc (p + Z.of_nat i + Z.of_nat k) = Some (nth k sl 0)).
{ intros k Hk. rewrite Hsl in Hk. replace (p + Z.of_nat i + Z.of_nat k) with (p + Z.of_nat (i + k)%nat) by lia.
  rewrite (ZS (i + k)%nat ltac:(rewrite length_app; cbn [length]; lia)). f_equal. rewrite app_nth1 by lia.
  subst sl L. symmetry. apply ka_sl_byte; lia. }
assert (HBS : forall a, p <= a < p + Z.of_nat (length rest) + 1 -> a < s1 - 2 * ESTACK).
{ intros a Ha. pose proof (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as HTH.
  apply (mf_heap_below_stack B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CX CORE HTH). rewrite LP3 in Ha. lia. }
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64 /\ (mf_cur_ptr (mv_c v) cur = 0 <-> cur = None)).
{ pose proof HMC as (bs & _ & (_ & Hseg32 & _)). pose proof HMP as (Hc0 & _ & _ & _ & (Hcl & Hch & _) & _).
  destruct cur as [gi|]; cbn [mf_cur_ptr]; [|split; [lia | tauto]].
  cbn [mf_cur_ok] in LCUR. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [intros E; exfalso; lia | discriminate]. }
(* the leaves: L1 / J1 (cur = Some gi, the '=' at ei) and the refusal, each from facts at a memory that keeps every
   byte outside memchr's window [s1 - ESTACK, s1) *)
assert (CKA : forall gi ei regs' mem' md', cur = Some gi -> memchr sl EQ = Some ei ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - ESTACK <= a < s1) -> rdW Wc mem' a = rdW Wc memc a) ->
  (forall r, In r KA_KEPT -> getr regs' r = getr regs1 r) ->
  ka_ctx B v lyc Sc Wc mem' md' pos mcc gi line p rest i j ei n /\ ka_regs B v lyc pos regs' line).
{ intros gi ei regs' mem' md' Hcur' Hei HJ' K' HK.
  destruct (mf_keep_win0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur Sc Wc mem' md' (s1 - ESTACK) s1 CX CORE CELLS
    HJ' (Permutation_refl _) ltac:(lia) ltac:(lia) K') as (CORE' & CELLS' & NPf & LPf).
  pose proof (LPf mcc cur line p rest LOOP) as LOOP'. pose proof (NPf _ NP) as NP'.
  subst cur. split.
  - exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hr (conj LOOP' (conj HL (conj Hij
      (conj HjL (conj HSL (conj Hei (conj (ka_model_disp mcc gi sl line rest ei (mf_final v) Hei HFIN') NP')))))))))))))).
  - unfold ka_regs, mf_regs_at. rewrite !HK by (cbv [KA_KEPT In]; tauto). exact (conj RG R22). }
assert (CREF : forall regs' mem' md', (memchr sl EQ = None \/ cur = None) ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - ESTACK <= a < s1) -> rdW Wc mem' a = rdW Wc memc a) ->
  (forall r, In r KA_KEPT -> getr regs' r = getr regs1 r) ->
  getr regs' 10 = w64 (mv_c v) -> getr regs' 11 = w64 (line + 1) ->
  SRr SEGS Wc (mkCfg (mkst regs' (Z_to_bv 64 (BASE + KA_JREF)) mem' (seg_rom SEGS)) md') (MF_POST B v)).
{ intros regs' mem' md' Hm HJ' K' HK R10' R11'.
  destruct (mf_keep_win0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur Sc Wc mem' md' (s1 - ESTACK) s1 CX CORE CELLS
    HJ' (Permutation_refl _) ltac:(lia) ltac:(lia) K') as (CORE' & CELLS' & NPf & LPf).
  pose proof (LPf mcc cur line p rest LOOP) as LOOP'. pose proof (NPf _ NP) as NP'.
  apply (REF v lyc Sc Wc regs' mem' md' pos mcc cur line p rest CX LS FRM CORE' CELLS').
  - unfold mf_regs_at. rewrite !HK by (cbv [KA_KEPT In]; tauto). exact RG.
  - rewrite HK by (cbv [KA_KEPT In]; tauto). exact R24.
  - exact Hn.
  - exact Hr.
  - exact LOOP'.
  - exact (ka_model_refuse mcc cur sl line rest (mf_final v) Hm HFIN').
  - exact NP'.
  - exact R10'.
  - exact R11'.
  - rewrite HK by (cbv [KA_KEPT In]; tauto). exact R21.
  - rewrite HK by (cbv [KA_KEPT In]; tauto). exact R22. }
(* ---- KEY to the memchr call: li a1,61; mv a0,s11; jal ---- *)
pose proof (a0_entry Wc regs1 memc R18) as HS.
assert (SHOK : sh_ok SEGS a_Bx [] (a_E regs1 []) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (a_E regs1 [])) by (unfold a_E; apply Eimg_env).
pose proof (a_env_agree regs1 []) as HA0.
assert (E27 : ew (a_E regs1 []) 27 = Z_to_bv 64 (p + Z.of_nat i)) by (rewrite (a_ew_reg regs1 [] 27 27%bv eq_refl); exact R27).
assert (E12 : ew (a_E regs1 []) 12 = Z_to_bv 64 (Z.of_nat (j - i))) by (rewrite (a_ew_reg regs1 [] 12 12%bv eq_refl); exact R12).
revert HS SHOK HEI HA0 E27 E12. generalize (a_E regs1 []) as E0. intros E0 HS SHOK HEI HA0 E27 E12.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ False -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
unfold mf_at.
paj_run_tok RUN HS HJ SHOK Bspan; [ a_awr | ].
a_after E0 HAE KM.
(* the registers at the call *)
lazymatch goal with HS : st_ok _ ?En ?ssx (restrict _ ?msx) |- _ =>
  pose proof (regs_kept_of_st_ok SEGS En ssx (restrict (w_H Wc) msx) regs1 [] A_RUN_KEPT HS (a_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK1 end.
cbn [ms_regs restrict] in HK1.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?mdx) _ => set (rg := r) in *; set (mm := m) in *; set (md1 := mdx) in * end.
assert (HRT : rdW Wc mm = rdW Wc memc) by (apply (ka_rd_ext (w_H Wc) memc mm); intros a Ha; exact (KM a Ha (fun x => x))).
assert (G2 : getr rg 2 = w64 s1) by (rewrite (HK1 2%bv) by (cbv [A_RUN_KEPT In]; tauto); exact R2).
assert (Usp : spZ rg = s1) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hx0 : 0 < p + Z.of_nat i) by lia.
(* ---- memchr(s, '=', j - i) ---- *)
eapply SRr_bind.
{ apply (aj_memchr_atM SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_memchr) SegInstA.RLO_A SegInstA.RHI_A
    (AMEMCHR fx) MCROM Wc rg mm SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v)
    (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc md1 0 (p + Z.of_nat i) 61 (Z.of_nat (j - i))
    (s1 - mv_sp v) (Z_to_bv 64 (BASE + KA_RMC)) HJ).
  - rewrite Q10, E27. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q12, E12. reflexivity.
  - lia.
  - lia.
  - exact Hx0.
  - lia.
  - rewrite Usp. lia.
  - exact Hs1m.
  - lia.
  - rewrite HES, HSTK. lia.
  - rewrite (HK1 3%bv) by (cbv [A_RUN_KEPT In]; tauto). exact R3.
  - rewrite (HK1 4%bv) by (cbv [A_RUN_KEPT In]; tauto). exact R4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold KA_RMC, AF_m_file; lia | vm_compute; reflexivity].
  - intros a Ha. rewrite HRT, Usp. split.
    + replace a with (p + Z.of_nat i + Z.of_nat (Z.to_nat (a - (p + Z.of_nat i)))) by lia.
      rewrite HSB by (rewrite Hsl; lia). discriminate.
    + pose proof (HBS a ltac:(lia)). lia.
  - unfold amem_range in *. lia.
  - rewrite HRT. exact (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat i) (Z.of_nat (j - i))
      HRA ltac:(lia) ltac:(lia)).
  - intros Hn0. rewrite HRT. apply (a_hull_sub _ p (Z.of_nat (length rest) + 1)); [apply HHULL; lia | lia | lia | lia | lia].
  - rewrite HRT. exact (mf_rod_now B RELRO v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HFB & HRES & HK2 & HPR2).
replace (mv_sp v + (s1 - mv_sp v)) with s1 in HK2 by lia.
(* every byte outside memchr's window as at KEY *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - ESTACK <= a < s1) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw. rewrite (HK2 a Ha Hw). exact (KM a Ha (fun x => x)). }
(* the registers kept from KEY *)
assert (HKA : forall r, In r KA_KEPT -> getr regs2 r = getr regs1 r).
{ intros r Hrr. rewrite <- (HK1 r) by exact Hrr.
  rewrite <- (Z_to_bv_bv_unsigned _ r). apply HP2.
  cbv [KA_KEPT In] in Hrr. unfold acallee_saved.
  repeat (destruct Hrr as [<- | Hrr];
    [lazymatch goal with |- context [bv_unsigned ?b] =>
       let z := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with z end; lia |]).
  destruct Hrr. }
(* the facts at memchr's return *)
clear HS SHOK HEI HAE KM HA0 Q10 Q11 Q12 Q1 E27 E12. try clear E0.
destruct (mf_keep_win0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur Sc Wc mem2 md2 (s1 - ESTACK) s1 CX CORE CELLS
  HJ2 (Permutation_refl _) ltac:(lia) ltac:(lia) K2) as (CORE2 & CELLS2 & _ & _).
pose proof CELLS2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
assert (G9 : getr regs2 9 = w64 s1) by (rewrite HKA by (cbv [KA_KEPT In]; tauto); exact R9).
assert (G18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite HKA by (cbv [KA_KEPT In]; tauto); exact R18).
set (nn := Z.of_nat (j - i)) in *.
set (x := p + Z.of_nat i) in *.
(* the bytes memchr read, through the run's memory *)
assert (HSB' : forall k, (k < length sl)%nat -> rdW Wc mm (x + Z.of_nat k) = Some (nth k sl 0))
  by (intros k Hk; rewrite HRT; exact (HSB k Hk)).
pose proof HFB as (Hkk & Hpre & Hat).
(* the leaves after the run from memchr's return, with the memory kept outside memchr's window *)
assert (Hcv : 0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64) by exact (proj1 Hcur).
set (cv := mf_cur_ptr (mv_c v) cur) in *.
pose proof (a1_entry Wc regs2 mem2 s1 cv G9 G18 ltac:(lia) ltac:(lia) Hcv V136) as HS.
assert (SHOK : sh_ok SEGS a_Bx [] (a_E regs2 [cv]) (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (a_E regs2 [cv])) by (unfold a_E; apply Eimg_env).
pose proof (a_env_agree regs2 [cv]) as HA2.
assert (F10 : ew (a_E regs2 [cv]) 10 = getr regs2 10) by (rewrite (a_ew_reg regs2 [cv] 10 10%bv eq_refl); reflexivity).
assert (F27 : ew (a_E regs2 [cv]) 27 = Z_to_bv 64 x)
  by (rewrite (a_ew_reg regs2 [cv] 27 27%bv eq_refl), HKA by (cbv [KA_KEPT In]; tauto); exact R27).
assert (F21 : ew (a_E regs2 [cv]) 21 = Z_to_bv 64 (mv_c v))
  by (rewrite (a_ew_reg regs2 [cv] 21 21%bv eq_refl), HKA by (cbv [KA_KEPT In]; tauto); exact R21).
assert (F22 : ew (a_E regs2 [cv]) 22 = Z_to_bv 64 (line + 1))
  by (rewrite (a_ew_reg regs2 [cv] 22 22%bv eq_refl), HKA by (cbv [KA_KEPT In]; tauto); exact R22).
pose proof (a_ew32 regs2 cv) as F32.
revert HS SHOK HEI HA2 F10 F27 F21 F22 F32. generalize (a_E regs2 [cv]) as E1. intros E1 HS SHOK HEI HA2 F10 F27 F21 F22 F32.
pose proof (env_agree_refl 34 E1) as HAE.
pose proof K2 as KM.
destruct (Z.ltb_spec kk nn) as [Hkn | Hkn].
- (* found at kk *)
  assert (F10' : ew E1 10 = Z_to_bv 64 (x + kk)) by (rewrite F10, HRES; reflexivity).
  assert (Hei : memchr sl EQ = Some (Z.to_nat kk)).
  { apply (ka_memchr_found sl (rdW Wc mm) x 61 kk HSB'); [rewrite Hsl; subst nn; lia | exact Hpre | exact (Hat Hkn)]. }
  paj_run_tok RUN HS HJ2 SHOK Bspan; [ a_awr | ].
  a_after E1 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* cur = NULL: refused *)
    pose proof (a_br_eq0 _ 32 cv true (a_ag_ew _ _ 32 cv HAE ltac:(lia) F32) Hcv Hc) as Hb1. apply Z.eqb_eq in Hb1. clear Hc.
    assert (HcN : cur = None) by exact (proj1 (proj2 Hcur) Hb1).
    paj_run_to_tok RUNTO HS HJ2 SHOK Bspan KA_JREF. { a_awr. }
    a_after E1 HAE KM.
    a_ref_leaf regs2 HA2 HAE HKA HJ2 KM F21 F22 CREF (or_intror (A := memchr sl EQ = None) HcN).
  + pose proof (a_br_eq0 _ 32 cv false (a_ag_ew _ _ 32 cv HAE ltac:(lia) F32) Hcv Hc) as Hb1. apply Z.eqb_neq in Hb1. clear Hc.
    assert (HSm : exists gi, cur = Some gi).
    { destruct cur as [gi|]; [exists gi; reflexivity | exfalso; apply Hb1; exact (proj2 (proj2 Hcur) eq_refl)]. }
    destruct HSm as (gi & Egi).
    paj_run_tok RUN HS HJ2 SHOK Bspan; [ a_awr | ].
    a_after E1 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * exfalso. pose proof (a_br_eq0 _ 10 (x + kk) true (a_ag_ew _ _ 10 _ HAE ltac:(lia) F10') ltac:(lia) Hc) as Hb2.
      apply Z.eqb_eq in Hb2. lia.
    * pose proof (a_br_eq0 _ 10 (x + kk) false (a_ag_ew _ _ 10 _ HAE ltac:(lia) F10') ltac:(lia) Hc) as Hb2. clear Hc.
      paj_run_tok RUN HS HJ2 SHOK Bspan; [ a_awr | ].
      a_after E1 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* the '=' first (kk = 0): J1 at a = i *)
         pose proof (a_br_geu _ 27 x 10 (x + kk) true (a_ag_ew _ _ 27 x HAE ltac:(lia) F27)
           (a_ag_ew _ _ 10 _ HAE ltac:(lia) F10') ltac:(lia) ltac:(lia) Hc) as Hb3. clear Hc.
         apply negb_true_iff, Z.ltb_ge in Hb3.
         assert (Hk0 : kk = 0) by lia.
         paj_run_to_tok RUNTO HS HJ2 SHOK Bspan KA_J1. { a_awr. }
         a_after E1 HAE KM.
         lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ _) |- _ =>
           pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ A_RUN_KEPT HS (a_ag32 _ _ _ _ HA2 HAE)
             ltac:(vm_compute; reflexivity)) as HK3 end.
         cbn [ms_regs restrict] in HK3.
         prreg HS (10%bv : bv 5) N10.
         pmkst HS.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg3 _ ?mm3 _) ?md3) _ =>
           destruct (CKA gi (Z.to_nat kk) rg3 mm3 md3 Egi Hei HJ2 KM (fun r Hrr => eq_trans (HK3 r Hrr) (HKA r Hrr)))
             as (CTX & RG3) end.
         apply (J1 v lyc Sc Wc _ _ _ pos mcc gi line p rest i j (Z.to_nat kk) i CTX RG3).
         ++ lia.
         ++ intros k Hk. lia.
         ++ left. lia.
         ++ rewrite HK3 by (cbv [A_RUN_KEPT In]; tauto). rewrite HKA by (cbv [KA_KEPT In]; tauto). exact R27.
         ++ rewrite N10. rewrite ?F10'. unfold w64. f_equal. subst x. lia.
         ++ rewrite HK3 by (cbv [A_RUN_KEPT In]; tauto). rewrite HKA by (cbv [KA_KEPT In]; tauto). exact R23.
      -- (* the key's front strip at q = i *)
         pose proof (a_br_geu _ 27 x 10 (x + kk) false (a_ag_ew _ _ 27 x HAE ltac:(lia) F27)
           (a_ag_ew _ _ 10 _ HAE ltac:(lia) F10') ltac:(lia) ltac:(lia) Hc) as Hb3. clear Hc.
         apply negb_false_iff, Z.ltb_lt in Hb3.
         paj_run_to_tok RUNTO HS HJ2 SHOK Bspan KA_L1. { a_awr. }
         a_after E1 HAE KM.
         lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ _) |- _ =>
           pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ A_RUN_KEPT HS (a_ag32 _ _ _ _ HA2 HAE)
             ltac:(vm_compute; reflexivity)) as HK3 end.
         cbn [ms_regs restrict] in HK3.
         prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
         pmkst HS.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg3 _ ?mm3 _) ?md3) _ =>
           destruct (CKA gi (Z.to_nat kk) rg3 mm3 md3 Egi Hei HJ2 KM (fun r Hrr => eq_trans (HK3 r Hrr) (HKA r Hrr)))
             as (CTX & RG3) end.
         apply (L1 v lyc Sc Wc _ _ _ pos mcc gi line p rest i j (Z.to_nat kk) i CTX RG3).
         ++ lia.
         ++ intros k Hk. lia.
         ++ rewrite HK3 by (cbv [A_RUN_KEPT In]; tauto). rewrite HKA by (cbv [KA_KEPT In]; tauto). exact R27.
         ++ rewrite N11, F27. reflexivity.
         ++ rewrite N10. rewrite ?F10'. unfold w64. f_equal. subst x. lia.
         ++ rewrite N12, F10', F27. unfold w64. apply bv_eq.
            rewrite alu64_unsigned, mul_div_unsigned. cbn [zalu_raw zmd_raw]. rewrite !Z_to_bv_unsigned.
            unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z_mod_same_full, Z.mul_0_r, Zmod_0_l, Z.add_0_r.
            rewrite Z.mod_mod by lia. f_equal. subst x. lia.
         ++ rewrite HK3 by (cbv [A_RUN_KEPT In]; tauto). rewrite HKA by (cbv [KA_KEPT In]; tauto). exact R23.
- (* no '=' in the stripped line *)
  assert (Hkk' : kk = nn) by lia.
  assert (F10' : ew E1 10 = Z_to_bv 64 0) by (rewrite F10, HRES; reflexivity).
  assert (Hnf : memchr sl EQ = None).
  { apply (ka_memchr_nf sl (rdW Wc mm) x 61 HSB'). intros i' Hi'. apply Hpre. rewrite Hsl in Hi'. subst nn. lia. }
  paj_run_tok RUN HS HJ2 SHOK Bspan; [ a_awr | ].
  a_after E1 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + pose proof (a_br_eq0 _ 32 cv true (a_ag_ew _ _ 32 cv HAE ltac:(lia) F32) Hcv Hc) as Hb1. apply Z.eqb_eq in Hb1. clear Hc.
    paj_run_to_tok RUNTO HS HJ2 SHOK Bspan KA_JREF. { a_awr. }
    a_after E1 HAE KM.
    a_ref_leaf regs2 HA2 HAE HKA HJ2 KM F21 F22 CREF (or_introl (B := cur = None) Hnf).
  + clear Hc.
    paj_run_tok RUN HS HJ2 SHOK Bspan; [ a_awr | ].
    a_after E1 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * clear Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK Bspan KA_JREF. { a_awr. }
      a_after E1 HAE KM.
      a_ref_leaf regs2 HA2 HAE HKA HJ2 KM F21 F22 CREF (or_introl (B := cur = None) Hnf).
    * exfalso. pose proof (a_br_eq0 _ 10 0 false (a_ag_ew _ _ 10 _ HAE ltac:(lia) F10') ltac:(lia) Hc) as Hb2.
      discriminate Hb2.
Qed.
End e.
End f.
End d.
