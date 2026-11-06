(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module names changed; 278 of its 311 lines of code are new or changed and 221 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: the value's back strip, L4 0x865a8 .. J4 0x865f0
   (m_file_s_keya_d.v ka_l4 : KA_J4_stmt n -> KA_L4_stmt n), by strong induction on d - c, one iteration per step
   re-seeded with a light state, in the form of m_file_s_keya_l1.v (fuzz_command's lib/A/Prog/answer_l.v,
   origin/ossv/recipes 501c0d516c69):
     0x865a8  srli a1,a0,3; add a1,a1,s2; lb a1,0(a1); bnez a1 -> slow  the instrumented check of the byte at a0
     0x865b8  addi a1,s7,-1; lbu a3,0(a1); bltu s3,a3 -> J4             above ' ': not blank, stop (d stays)
     0x865c4  srl a3,s9,a3; andi a3,a3,1; beqz a3 -> J4                 the blank mask: not blank, stop (d stays)
     0x865d0  addi a0,a0,-1; mv s7,a1; bltu s5,a1 -> L4                 blank: on to the byte before (d - 1)
     0x865dc  j 0x865ec; 0x865ec mv s7,s5                              every value byte blank: s7 = s5 (d := c)
   The state of an iteration: every register its own atom; atom 32 the byte at s7 - 1 = a0; one read-only region,
   that byte (base s7, offset -1); the shadow base s2 (atom 18) as the check's base; no shadow entry (the check
   leaves the obligation that the byte at a0 is addressable, from mf_loop's sa_addr of the text left).
   The KEYA segment lane of the G2 walk owner's G2. *)
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

(* ---- the state of an iteration ---- *)
Definition l4_regions : smem :=
[ YP09.mkRegion (Some 23%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))] ].
Definition l4_facts : facts :=
mkFacts [ (10%nat, mkAF 0 (2 ^ 47 - 2) 0); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition l4_ss : sstate := mkSS KA_L4 sr_atoms l4_regions None l4_facts.
Definition l4_Bx : sv := SOff 18 0.
(* the registers no iteration writes (it writes a0, a1, a3, s7) *)
Definition L4_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition l4_E (regs1 : bvmap 5 word) (Cz : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 Cz]).
Lemma l4_ew_reg : forall regs1 Cz n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (l4_E regs1 Cz) n = getr regs1 r.
Proof.
intros regs1 Cz n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold l4_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma l4_ew32 : forall regs1 Cz, ew (l4_E regs1 Cz) 32 = Z_to_bv 64 Cz.
Proof. intros. unfold l4_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma l4_env_agree : forall regs1 Cz, env_agree 32 (Ereg regs1 [Z_to_bv 64 Cz]) (l4_E regs1 Cz).
Proof. intros. split; [intros n Hn; unfold l4_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seed of an iteration: a0 = P, s7 = P + 1, the byte at P *)
Lemma l4_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc P Cz,
getr regs1 10 = w64 P -> getr regs1 23 = w64 (P + 1) -> getr regs1 18 = w64 SHADOW_OFF ->
0 <= P <= 2 ^ 47 - 2 -> rdW W memc P = Some Cz ->
st_ok_pi SEGS VAL (l4_E regs1 Cz) l4_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KA_L4)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc P Cz H10 H23 H18 HP HrdP.
destruct (aview_byte SEGS (w_H W) memc P Cz HrdP) as (b & Hb & Hv & HCz).
set (E := l4_E regs1 Cz).
assert (E10 : ew E 10 = Z_to_bv 64 P) by (subst E; rewrite (l4_ew_reg regs1 Cz 10 10%bv eq_refl); exact H10).
assert (E23 : ew E 23 = Z_to_bv 64 (P + 1)) by (subst E; rewrite (l4_ew_reg regs1 Cz 23 23%bv eq_refl); exact H23).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite (l4_ew_reg regs1 Cz 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 Cz) by (subst E; apply l4_ew32).
rewrite restrict_mkst_fx. unfold l4_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E23, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small Cz), (unsigned_lit_small Cz) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst Cz. apply Z_to_bv_bv_unsigned.
  + replace (P + 1 + -1 + 0) with P by lia. exact Hb.
- exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [l4_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E18, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* a run writes nothing: every byte keeps its view *)
Lemma l4_keep_step : forall E cs (m0 m m' : word -> option byte) (H : word -> bool),
frame_of E [YP09.mkRegion (Some 23%nat) (-1) 0 0 0 cs] (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs m0 m m' H HFr KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Hq | []]. injection Hq as <- <- <-. lia.
Qed.
Lemma l4_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma l4_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* the branches of an iteration, over the atoms' values *)
Lemma l4_br_ltu : forall E n1 v1 n2 v2 b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = b -> (v1 <? v2) = b.
Proof.
intros E n1 v1 n2 v2 b H1 H2 R1 R2 Hc.
rewrite branch_ltu_U, (U_atom E n1 v1 H1 R1), (U_atom E n2 v2 H2 R2) in Hc. exact Hc.
Qed.
Lemma l4_br_ltu_off : forall E n1 v1 n2 v2 c b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v2 + c < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 c)) = b -> (v1 <? v2 + c) = b.
Proof.
intros E n1 v1 n2 v2 c b H1 H2 R1 R2 R2c Hc.
rewrite branch_ltu_U, (U_atom E n1 v1 H1 R1), (U_atom_off E n2 v2 c H2 R2 R2c) in Hc. exact Hc.
Qed.
Lemma l4_br_mask : forall E Cz b, ew E 25 = Z_to_bv 64 MF_BLANK -> ew E 32 = Z_to_bv 64 Cz -> 0 <= Cz <= 32 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SOff 25 0) (SOff 32 0)) (SLit 1))) (sv_denot E (SLit 0)) = b ->
blank Cz = negb b.
Proof.
intros E Cz b H25 H32 HC Hc.
rewrite branch_eq_U, U_and_lit, U_SAlu, (U_atom E 25 MF_BLANK H25), (U_atom E 32 Cz H32), U_lit in Hc
  by (unfold MF_BLANK; lia).
subst b.
assert (EN : exists k, Cz = Z.of_nat k /\ (k <= 32)%nat) by (exists (Z.to_nat Cz); split; lia).
destruct EN as [k [-> Hk]]. clear - Hk.
do 33 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run: the environment agrees with the seed's E0 below 34 (HAE), the memory keeps every view (KM) *)
Ltac l4_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (l4_keep_step Eo _ _ _ _ _ HFr KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac l4_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

Lemma ka_l4 : forall n, KA_J4_stmt B n -> KA_L4_stmt B n.
Proof.
intros n J4.
assert (ALL : forall m, forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d,
  (d - c <= m)%nat ->
  ka_ctx B v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs B v lyc pos regs1 line ->
  ka_key_at (mf_line rest) i ei a b -> ka_vfront_at (mf_line rest) i j ei c ->
  (c < d <= j)%nat -> all_blank (mf_line rest) d j ->
  getr regs1 23 = w64 (p + Z.of_nat d) -> getr regs1 10 = w64 (p + Z.of_nat d - 1) ->
  getr regs1 21 = w64 (p + Z.of_nat c) ->
  getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
  mf_at B v Wc regs1 memc mdc KA_L4).
{ induction m as [|m IH];
  intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d Hm CTX RG KAT VFR Hd HAB R23 R10 R21 R12 R27;
  [lia|].
  pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
  pose proof LOOP as (_ & _ & _ & ((ZS & _) & _) & (Hp0 & _ & HAM & HRA & _) & _).
  pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26) & R22).
  pose proof CORE as (HJ & _).
  pose proof (mf_line_len rest) as HLr.
  set (L := mf_line rest) in *.
  set (P := p + Z.of_nat (d - 1)).
  set (Cz := nth (d - 1) L 0).
  assert (HrdP : rdW Wc memc P = Some Cz).
  { subst P Cz. rewrite (ZS (d - 1)%nat ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    rewrite app_nth1 by lia. subst L. apply mf_line_nth. lia. }
  destruct (aview_byte SEGS (w_H Wc) memc P Cz HrdP) as (bz & _ & _ & HCz).
  assert (R10P : getr regs1 10 = w64 P) by (rewrite R10; unfold w64; f_equal; subst P; lia).
  assert (R23P : getr regs1 23 = w64 (P + 1)) by (rewrite R23; unfold w64; f_equal; subst P; lia).
  (* a leaf at J4 with the back strip stopped at d' *)
  assert (CJ4 : forall regs1' memc' mdc' d',
    ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
      (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
    (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
    (forall r, In r L4_KEPT -> getr regs1' r = getr regs1 r) ->
    (c <= d' <= j)%nat -> all_blank L d' j -> (d' = c \/ blank (nth (d' - 1) L 0) = false) ->
    getr regs1' 23 = w64 (p + Z.of_nat d') ->
    SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_J4)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
  { intros regs1' memc' mdc' d' HJ' KM' HK Hd' HAd Hsd R23'.
    apply (J4 v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b c d'
      (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
    - unfold ka_regs, mf_regs_at. rewrite !HK by (cbv [L4_KEPT In]; tauto). exact RG.
    - exact KAT.
    - exact VFR.
    - exact Hd'.
    - exact HAd.
    - exact Hsd.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R21.
    - exact R23'.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R12.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R27. }
  (* a leaf back at L4 with the byte at d - 1 blank *)
  assert (CL4 : forall regs1' memc' mdc',
    ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
      (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
    (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
    (forall r, In r L4_KEPT -> getr regs1' r = getr regs1 r) ->
    (c < d - 1)%nat -> blank Cz = true ->
    getr regs1' 23 = w64 (p + Z.of_nat (d - 1)) -> getr regs1' 10 = w64 (p + Z.of_nat (d - 1) - 1) ->
    SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_L4)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
  { intros regs1' memc' mdc' HJ' KM' HK Hd' Hbl R23' R10'.
    apply (IH v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b c (d - 1)%nat).
    - lia.
    - exact (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM').
    - unfold ka_regs, mf_regs_at. rewrite !HK by (cbv [L4_KEPT In]; tauto). exact RG.
    - exact KAT.
    - exact VFR.
    - lia.
    - intros k Hk. destruct (Nat.eq_dec k (d - 1)) as [->|Hne]; [exact Hbl | apply HAB; lia].
    - exact R23'.
    - exact R10'.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R21.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R12.
    - rewrite HK by (cbv [L4_KEPT In]; tauto). exact R27. }
  assert (HPb : 0 <= P /\ P + 1 <= p + Z.of_nat (length rest) + 1 /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 47 - 1).
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM. subst P. lia. }
  pose proof (l4_entry Wc regs1 memc P Cz R10P R23P R18 ltac:(lia) HrdP) as HS.
  assert (SHOK : sh_ok SEGS l4_Bx [] (l4_E regs1 Cz) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
  assert (HEI : img_env VAL A_LIM (l4_E regs1 Cz)) by (unfold l4_E; apply Eimg_env).
  pose proof (l4_env_agree regs1 Cz) as HA0.
  assert (E10 : ew (l4_E regs1 Cz) 10 = Z_to_bv 64 P) by (rewrite (l4_ew_reg regs1 Cz 10 10%bv eq_refl); exact R10P).
  assert (E18 : ew (l4_E regs1 Cz) 18 = Z_to_bv 64 SB) by (rewrite (l4_ew_reg regs1 Cz 18 18%bv eq_refl); exact R18).
  assert (E19 : ew (l4_E regs1 Cz) 19 = Z_to_bv 64 32) by (rewrite (l4_ew_reg regs1 Cz 19 19%bv eq_refl); exact R19).
  assert (E25 : ew (l4_E regs1 Cz) 25 = Z_to_bv 64 MF_BLANK) by (rewrite (l4_ew_reg regs1 Cz 25 25%bv eq_refl); exact R25).
  assert (E21 : ew (l4_E regs1 Cz) 21 = Z_to_bv 64 (p + Z.of_nat c))
    by (rewrite (l4_ew_reg regs1 Cz 21 21%bv eq_refl); exact R21).
  assert (E23 : ew (l4_E regs1 Cz) 23 = Z_to_bv 64 (p + Z.of_nat d))
    by (rewrite (l4_ew_reg regs1 Cz 23 23%bv eq_refl); exact R23).
  pose proof (l4_ew32 regs1 Cz) as E32.
  revert HS SHOK HEI HA0 E10 E18 E19 E25 E21 E23 E32.
  generalize (l4_E regs1 Cz) as E0.
  intros E0 HS SHOK HEI HA0 E10 E18 E19 E25 E21 E23 E32.
  pose proof (env_agree_refl 34 E0) as HAE.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
  unfold mf_at.
  (* the check of the byte at a0, its load at s7 - 1, `bltu s3,a3` *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { cbn [ms_mem]. unfold l4_Bx. rewrite (U_atom _ 18 SB E18), (U_atom _ 10 P E10) by (unfold SB; lia).
    rewrite SB_SHADOW_OFF.
    exact (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) P 1 HRA ltac:(subst P; lia) ltac:(lia)). }
  { l4_awr. }
  l4_after E0 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* above ' ': not blank, J4 at d *)
    pose proof (l4_br_ltu _ 19 32 32 Cz true (l4_ag_ew _ _ 19 32 HAE ltac:(lia) E19)
      (l4_ag_ew _ _ 32 Cz HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as C1. apply Z.ltb_lt in C1. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J4. { l4_awr. }
    l4_after E0 HAE KM.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ L4_KEPT HS (l4_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (23%bv : bv 5) N23.
    pmkst HS.
    exact (CJ4 _ _ _ d HJ KM HK ltac:(lia) HAB (or_intror (blank_gt32 Cz C1)) ltac:(rewrite N23, E23; reflexivity)).
  - pose proof (l4_br_ltu _ 19 32 32 Cz false (l4_ag_ew _ _ 19 32 HAE ltac:(lia) E19)
      (l4_ag_ew _ _ 32 Cz HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as C1. apply Z.ltb_ge in C1. clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan. { l4_awr. }
    l4_after E0 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    + (* the mask bit 0: not blank, J4 at d *)
      pose proof (l4_br_mask _ Cz true (l4_ag_ew _ _ 25 MF_BLANK HAE ltac:(lia) E25)
        (l4_ag_ew _ _ 32 Cz HAE ltac:(lia) E32) ltac:(lia) Hc) as C2. cbn [negb] in C2. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J4. { l4_awr. }
      l4_after E0 HAE KM.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ L4_KEPT HS (l4_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (23%bv : bv 5) N23.
      pmkst HS.
      exact (CJ4 _ _ _ d HJ KM HK ltac:(lia) HAB (or_intror C2) ltac:(rewrite N23, E23; reflexivity)).
    + (* blank: a0, s7 back one, `bltu s5,a1` *)
      pose proof (l4_br_mask _ Cz false (l4_ag_ew _ _ 25 MF_BLANK HAE ltac:(lia) E25)
        (l4_ag_ew _ _ 32 Cz HAE ltac:(lia) E32) ltac:(lia) Hc) as C2. cbn [negb] in C2. clear Hc.
      paj_run_tok RUN HS HJ SHOK Bspan. { l4_awr. }
      l4_after E0 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      * (* another value byte: back at L4 with d - 1 *)
        pose proof (l4_br_ltu_off _ 21 (p + Z.of_nat c) 23 (p + Z.of_nat d) (-1) true (l4_ag_ew _ _ 21 _ HAE ltac:(lia) E21)
          (l4_ag_ew _ _ 23 _ HAE ltac:(lia) E23) ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C3. clear Hc.
        apply Z.ltb_lt in C3.
        paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_L4. { l4_awr. }
        l4_after E0 HAE KM.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ L4_KEPT HS (l4_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
        cbn [ms_regs restrict] in HK.
        prreg HS (23%bv : bv 5) N23. prreg HS (10%bv : bv 5) N10.
        pmkst HS.
        exact (CL4 _ _ _ HJ KM HK ltac:(lia) C2
          ltac:(rewrite N23; rewrite ?E23; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia)
          ltac:(rewrite N10; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; subst P; lia)).
      * (* the last value byte was blank: s7 := s5, J4 at c *)
        pose proof (l4_br_ltu_off _ 21 (p + Z.of_nat c) 23 (p + Z.of_nat d) (-1) false (l4_ag_ew _ _ 21 _ HAE ltac:(lia) E21)
          (l4_ag_ew _ _ 23 _ HAE ltac:(lia) E23) ltac:(lia) ltac:(lia) ltac:(lia) Hc) as C3. clear Hc.
        apply Z.ltb_ge in C3.
        paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_J4. { l4_awr. }
        l4_after E0 HAE KM.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ L4_KEPT HS (l4_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
        cbn [ms_regs restrict] in HK.
        prreg HS (23%bv : bv 5) N23.
        pmkst HS.
        assert (Hcd : c = (d - 1)%nat) by lia.
        exact (CJ4 _ _ _ c HJ KM HK ltac:(lia)
          ltac:(intros k Hk; destruct (Nat.eq_dec k (d - 1)) as [->|Hne]; [exact C2 | apply HAB; lia])
          (or_introl eq_refl) ltac:(rewrite N23; rewrite ?E21; reflexivity)). }
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d CTX RG KAT VFR Hd HAB R23 R10 R21 R12 R27.
exact (ALL (d - c)%nat v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d (le_n _) CTX RG KAT VFR Hd HAB
  R23 R10 R21 R12 R27).
Qed.
End e.
End f.
End d.
