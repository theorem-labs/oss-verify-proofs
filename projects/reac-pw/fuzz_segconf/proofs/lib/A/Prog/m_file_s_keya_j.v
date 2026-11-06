(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module names changed; 329 of its 363 lines of code are new or changed and 220 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: the three joins between the strip loops
   (m_file_s_keya_d.v), in the form of plugin-hostd/fuzz_command's lib/A/Prog walks (origin/ossv/recipes
   501c0d516c69), each a light seed and one or two runs (no load, no store):
     J1 0x86434  bgeu s11,a0 -> 0x86484        the front strip stopped at the '=' (a = i + ei):
                 0x86484 mv a2,a0; j 0x86550   J2 with the key empty, b = a
                 0x86438 addi a1,a0,-1; mv a2,a0 -> L2 0x86440 with b = i + ei
     J2 0x86550  addi s5,a0,1; bgeu s5,s7 -> J3 0x865a0 with c = i + ei + 1 (= j, the value empty)
                 0x86558 addi a0,a0,1 -> L3 0x8655c with c = i + ei + 1
     J3 0x865a0  bgeu s5,s7 -> J4 0x865f0 with d = c (= j, the value empty)
                 0x865a4 addi a0,s7,-1 -> L4 0x865a8 with d = j
   The state of a join: every register its own atom, no region, no fact; no shadow entry (no check runs); the runs
   write registers only, so every byte keeps its view (kept_of_frame over no window) and ka_ctx follows by
   m_file_s_keya_k.v ka_ctx_kept. The branches compare atoms (BC_GEU); i + ei < j is memchr's index in the
   stripped line (memchr_some, slice_length). The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_keya_m m_file_s_keya_d m_file_s_keya_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the state of a join: no region, no fact ---- *)
Definition kj_facts : facts := mkFacts [] [] [].
Definition kj_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None kj_facts.
Definition kj_Bx : sv := SOff 18 0.
(* the registers each join keeps (J1 writes a1, a2; J2 writes s5, a0; J3 writes a0) *)
Definition KJ1_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 10; 18; 19; 22; 23; 25; 26; 27]%bv.
Definition KJ2_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 12; 18; 19; 22; 23; 25; 26; 27]%bv.
Definition KJ3_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 12; 18; 19; 21; 22; 23; 25; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition kj_E (regs1 : bvmap 5 word) : env := Eimg (Ereg regs1 []).
Lemma kj_ew_reg : forall regs1 n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (kj_E regs1) n = getr regs1 r.
Proof.
intros regs1 n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold kj_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma kj_env_agree : forall regs1, env_agree 32 (Ereg regs1 []) (kj_E regs1).
Proof. intros. split; [intros n Hn; unfold kj_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seed of a join *)
Lemma kj_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc pc,
st_ok_pi SEGS VAL (kj_E regs1) (kj_ss pc) (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc pc.
rewrite restrict_mkst_fx. unfold kj_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- exact (conj I (conj I I)).
Qed.

(* a run writes nothing: every byte keeps its view *)
Lemma kj_keep_step : forall E rs (m0 m m' : word -> option byte) (H : word -> bool),
frame_of E rs (mrestrict H m) (mrestrict H m') -> windows rs = [] ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H HFr HW KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. rewrite HW in Hin. destruct Hin.
Qed.
Lemma kj_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma kj_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* `bgeu x + c, y` over the atoms' values *)
Lemma kj_br_geu : forall E n1 v1 c n2 v2 b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v1 + c < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff n1 c)) (sv_denot E (SOff n2 0)) = b -> negb (v1 + c <? v2) = b.
Proof.
intros E n1 v1 c n2 v2 b H1 H2 R1 R1c R2 Hc.
rewrite branch_geu_U, (U_atom_off E n1 v1 c H1 R1 R1c), (U_atom E n2 v2 H2 R2) in Hc. exact Hc.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run: the environment agrees with the seed's E0 below 34 (HAE), the memory keeps every view (KM) *)
Ltac kj_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (kj_keep_step Eo _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac kj_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  apply awr_ok_nil.
Ltac kj_kept := cbv [KJ1_KEPT KJ2_KEPT KJ3_KEPT In]; tauto.

(* J1 0x86434: the front strip stopped at a; on to the back strip (a < i + ei) or J2 with the key [a, a) *)
Lemma ka_j1 : forall n, KA_L2_stmt B n -> KA_J2_stmt B n -> KA_J1_stmt B n.
Proof.
intros n L2 J2 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a CTX RG Ha HAB Hsa R27 R10 R23.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
pose proof CORE as (HJ & _).
pose proof (mf_line_len rest) as HLr.
pose proof (memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite slice_length in Hei by lia.
set (L := mf_line rest) in *.
(* the leaf at J2: the key is empty, b = a = i + ei *)
assert (CJ2 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ1_KEPT -> getr regs1' r = getr regs1 r) ->
  a = (i + ei)%nat -> getr regs1' 12 = w64 (p + Z.of_nat a) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_J2)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hae R12'.
  apply (J2 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a a
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - unfold ka_key_at. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [left; exact Hae|].
    split; [intros k Hk; lia | left; reflexivity].
  - exact R12'.
  - rewrite HK by kj_kept. exact R27.
  - rewrite HK by kj_kept. exact R10.
  - rewrite HK by kj_kept. exact R23. }
(* the leaf at L2: the back strip from b = i + ei *)
assert (CL2 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ1_KEPT -> getr regs1' r = getr regs1 r) ->
  (a < i + ei)%nat -> getr regs1' 12 = w64 (p + Z.of_nat (i + ei)) ->
  getr regs1' 11 = w64 (p + Z.of_nat (i + ei) - 1) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_L2)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hlt R12' R11'.
  apply (L2 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a (i + ei)%nat
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - lia.
  - lia.
  - exact HAB.
  - exact Hsa.
  - intros k Hk; lia.
  - exact R12'.
  - exact R11'.
  - rewrite HK by kj_kept. exact R27.
  - rewrite HK by kj_kept. exact R10.
  - rewrite HK by kj_kept. exact R23. }
pose proof (kj_entry Wc regs1 memc KA_J1) as HS.
assert (SHOK : sh_ok SEGS kj_Bx [] (kj_E regs1) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kj_E regs1)) by (unfold kj_E; apply Eimg_env).
pose proof (kj_env_agree regs1) as HA0.
assert (E27 : ew (kj_E regs1) 27 = Z_to_bv 64 (p + Z.of_nat a)) by (rewrite (kj_ew_reg regs1 27 27%bv eq_refl); exact R27).
assert (E10 : ew (kj_E regs1) 10 = Z_to_bv 64 (p + Z.of_nat (i + ei)))
  by (rewrite (kj_ew_reg regs1 10 10%bv eq_refl); exact R10).
revert HS SHOK HEI HA0 E27 E10.
generalize (kj_E regs1) as E0.
intros E0 HS SHOK HEI HA0 E27 E10.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc x = rdW Wc memc x) by (intros; reflexivity).
unfold mf_at.
(* `bgeu s11,a0` *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s11 = a0: a2 := a0, J2 *)
  pose proof (kj_br_geu _ 27 (p + Z.of_nat a) 0 10 (p + Z.of_nat (i + ei)) true E27 E10
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_true_iff, Z.ltb_ge in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J2. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ1_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (12%bv : bv 5) N12.
  pmkst HS.
  exact (CJ2 _ _ _ HJ KM HK ltac:(lia) ltac:(rewrite N12, E10; unfold w64; f_equal; lia)).
- (* s11 < a0: a1 := a0 - 1, a2 := a0, L2 *)
  pose proof (kj_br_geu _ 27 (p + Z.of_nat a) 0 10 (p + Z.of_nat (i + ei)) false E27 E10
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_false_iff, Z.ltb_lt in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_L2. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ1_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (12%bv : bv 5) N12. prreg HS (11%bv : bv 5) N11.
  pmkst HS.
  exact (CL2 _ _ _ HJ KM HK ltac:(lia) ltac:(rewrite N12, E10; reflexivity)
    ltac:(rewrite N11; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)).
Qed.

(* J2 0x86550: the key is [a, b); s5 := a0 + 1, on to the value's front strip or J3 with the value empty *)
Lemma ka_j2 : forall n, KA_L3_stmt B n -> KA_J3_stmt B n -> KA_J2_stmt B n.
Proof.
intros n L3 J3 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b CTX RG KEY R12 R27 R10 R23.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
pose proof CORE as (HJ & _).
pose proof (mf_line_len rest) as HLr.
pose proof (memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite slice_length in Hei by lia.
set (L := mf_line rest) in *.
(* the leaf at J3: the value's front strip has nothing to strip, c = j = i + ei + 1 *)
assert (CJ3 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ2_KEPT -> getr regs1' r = getr regs1 r) ->
  (i + S ei = j)%nat -> getr regs1' 21 = w64 (p + Z.of_nat j) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_J3)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hej R21'.
  apply (J3 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b j
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - exact KEY.
  - unfold ka_vfront_at. split; [lia|]. split; [intros k Hk; lia | left; reflexivity].
  - exact R21'.
  - rewrite HK by kj_kept. exact R23.
  - rewrite HK by kj_kept. exact R12.
  - rewrite HK by kj_kept. exact R27. }
(* the leaf at L3: the value's front strip from c = i + ei + 1 *)
assert (CL3 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ2_KEPT -> getr regs1' r = getr regs1 r) ->
  (i + S ei < j)%nat -> getr regs1' 21 = w64 (p + Z.of_nat (i + S ei)) ->
  getr regs1' 10 = w64 (p + Z.of_nat (i + S ei)) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_L3)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hlt R21' R10'.
  apply (L3 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b (i + S ei)%nat
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - exact KEY.
  - lia.
  - intros k Hk; lia.
  - exact R21'.
  - exact R10'.
  - rewrite HK by kj_kept. exact R23.
  - rewrite HK by kj_kept. exact R12.
  - rewrite HK by kj_kept. exact R27. }
pose proof (kj_entry Wc regs1 memc KA_J2) as HS.
assert (SHOK : sh_ok SEGS kj_Bx [] (kj_E regs1) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kj_E regs1)) by (unfold kj_E; apply Eimg_env).
pose proof (kj_env_agree regs1) as HA0.
assert (E10 : ew (kj_E regs1) 10 = Z_to_bv 64 (p + Z.of_nat (i + ei)))
  by (rewrite (kj_ew_reg regs1 10 10%bv eq_refl); exact R10).
assert (E23 : ew (kj_E regs1) 23 = Z_to_bv 64 (p + Z.of_nat j)) by (rewrite (kj_ew_reg regs1 23 23%bv eq_refl); exact R23).
revert HS SHOK HEI HA0 E10 E23.
generalize (kj_E regs1) as E0.
intros E0 HS SHOK HEI HA0 E10 E23.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc x = rdW Wc memc x) by (intros; reflexivity).
unfold mf_at.
(* `addi s5,a0,1`, `bgeu s5,s7` *)
paj_run_tok RUN HS HJ SHOK Bspan. { kj_awr. }
kj_after E0 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s5 = s7: J3 with c = j *)
  pose proof (kj_br_geu _ 10 (p + Z.of_nat (i + ei)) 1 23 (p + Z.of_nat j) true
    (kj_ag_ew _ _ 10 _ HAE ltac:(lia) E10) (kj_ag_ew _ _ 23 _ HAE ltac:(lia) E23)
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_true_iff, Z.ltb_ge in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J3. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ2_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (21%bv : bv 5) N21.
  pmkst HS.
  exact (CJ3 _ _ _ HJ KM HK ltac:(lia)
    ltac:(rewrite N21; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)).
- (* s5 < s7: a0 := a0 + 1, L3 with c = i + ei + 1 *)
  pose proof (kj_br_geu _ 10 (p + Z.of_nat (i + ei)) 1 23 (p + Z.of_nat j) false
    (kj_ag_ew _ _ 10 _ HAE ltac:(lia) E10) (kj_ag_ew _ _ 23 _ HAE ltac:(lia) E23)
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_false_iff, Z.ltb_lt in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_L3. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ2_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (21%bv : bv 5) N21. prreg HS (10%bv : bv 5) N10.
  pmkst HS.
  exact (CL3 _ _ _ HJ KM HK ltac:(lia)
    ltac:(rewrite N21; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(rewrite N10; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)).
Qed.

(* J3 0x865a0: the value's front strip stopped at c; on to the back strip (c < j) or J4 with the value empty *)
Lemma ka_j3 : forall n, KA_L4_stmt B n -> KA_J4_stmt B n -> KA_J3_stmt B n.
Proof.
intros n L4 J4 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c CTX RG KEY VF R21 R23 R12 R27.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
pose proof CORE as (HJ & _).
pose proof (mf_line_len rest) as HLr.
pose proof VF as (HVc & _ & _).
set (L := mf_line rest) in *.
(* the leaf at J4: the value's back strip has nothing to strip, d = c = j *)
assert (CJ4 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ3_KEPT -> getr regs1' r = getr regs1 r) ->
  c = j ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_J4)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hcj.
  apply (J4 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b c c
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - exact KEY.
  - exact VF.
  - lia.
  - intros k Hk; lia.
  - left; reflexivity.
  - rewrite HK by kj_kept. exact R21.
  - rewrite HK by kj_kept. rewrite Hcj. exact R23.
  - rewrite HK by kj_kept. exact R12.
  - rewrite HK by kj_kept. exact R27. }
(* the leaf at L4: the value's back strip from d = j *)
assert (CL4 : forall regs1' memc' mdc',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r KJ3_KEPT -> getr regs1' r = getr regs1 r) ->
  (c < j)%nat -> getr regs1' 10 = w64 (p + Z.of_nat j - 1) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_L4)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' HJ' KM' HK Hlt R10'.
  apply (L4 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b c j
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold ka_regs, mf_regs_at. rewrite !HK by kj_kept. exact RG.
  - exact KEY.
  - exact VF.
  - lia.
  - intros k Hk; lia.
  - rewrite HK by kj_kept. exact R23.
  - exact R10'.
  - rewrite HK by kj_kept. exact R21.
  - rewrite HK by kj_kept. exact R12.
  - rewrite HK by kj_kept. exact R27. }
pose proof (kj_entry Wc regs1 memc KA_J3) as HS.
assert (SHOK : sh_ok SEGS kj_Bx [] (kj_E regs1) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM (kj_E regs1)) by (unfold kj_E; apply Eimg_env).
pose proof (kj_env_agree regs1) as HA0.
assert (E21 : ew (kj_E regs1) 21 = Z_to_bv 64 (p + Z.of_nat c)) by (rewrite (kj_ew_reg regs1 21 21%bv eq_refl); exact R21).
assert (E23 : ew (kj_E regs1) 23 = Z_to_bv 64 (p + Z.of_nat j)) by (rewrite (kj_ew_reg regs1 23 23%bv eq_refl); exact R23).
revert HS SHOK HEI HA0 E21 E23.
generalize (kj_E regs1) as E0.
intros E0 HS SHOK HEI HA0 E21 E23.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc x = rdW Wc memc x) by (intros; reflexivity).
unfold mf_at.
(* `bgeu s5,s7` *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s5 = s7: J4 with d = c *)
  pose proof (kj_br_geu _ 21 (p + Z.of_nat c) 0 23 (p + Z.of_nat j) true E21 E23
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_true_iff, Z.ltb_ge in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J4. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ3_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  exact (CJ4 _ _ _ HJ KM HK ltac:(lia)).
- (* s5 < s7: a0 := s7 - 1, L4 with d = j *)
  pose proof (kj_br_geu _ 21 (p + Z.of_nat c) 0 23 (p + Z.of_nat j) false E21 E23
    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C1. apply negb_false_iff, Z.ltb_lt in C1. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_L4. { kj_awr. }
  kj_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KJ3_KEPT HS (kj_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) N10.
  pmkst HS.
  exact (CL4 _ _ _ HJ KM HK ltac:(lia)
    ltac:(rewrite N10; rewrite ?E23; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)).
Qed.
End e.
End f.
End d.
