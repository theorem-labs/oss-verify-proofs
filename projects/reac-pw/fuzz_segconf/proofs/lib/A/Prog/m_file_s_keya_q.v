(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_def.v, with its module paths and module names changed; 679 of its 738 lines of code are new or changed and 1104 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: the quotes and low.i in scope, J4 0x865f0 .. KDISP
   0x86684 (m_file_s_keya_d.v ka_j4 : MF_KDISP_stmt n -> KA_J4_stmt n), in the form of plugin-hostd/fuzz_command's
   lib/A/Prog walks (origin/ossv/recipes 501c0d516c69): a token run with read-only regions over the two inline
   checks to 0x8665c (KA_M, this file's own statement), then a plain run with low.i's shadow bytes writable
   (check_reply_s1.v:397-416) over the eight stores to KDISP.
     0x865f0  sub a0,s7,s5; li a1,2; blt a0,a1 -> 0x86658          vl < 2: no quote test
     0x865fc  srli a0,s5,3; add a0,a0,s2; lb a0,0(a0); bnez -> slow the instrumented check of v[0] (byte at s5)
     0x8660c  lbu a1,0(s5); li a0,39; beq a1,a0 -> 0x86620; li a0,34; bne a1,a0 -> 0x86658
     0x86620  addi a0,s7,-1; srli a3,a0,3; add a3,a3,s2; lb a3,0(a3); bnez -> slow   the check of v[vl - 1]
     0x86634  lbu a3,-1(s7); beq a3,a1 -> 0x86640; mv a0,s7
     0x86640  mv s8,s6; xor a1,a3,a1; seqz a1,a1; add s5,s5,a1; mv s7,a0; j 0x8665c   a matching pair goes
     0x86658  mv s8,s6
     0x8665c  sub s6,a2,s11; sub s4,s7,s5                              KA_M: s6 = kl, s4 = vl
     0x86664  sb zero,8(s10) .. sb zero,7(s10)                         low.i's 8 shadow bytes := 0 (s10 = shadow(FB))
   The token run's states: every register its own atom; for vl >= 2 two read-only regions, the byte v[0] at s5
   (atom 32) and the byte v[vl - 1] at s7 - 1 (atom 33); for vl < 2 none (the run reads no byte). The plain run's
   state: every register its own atom and one region, low.i's shadow bytes at s10 + 4 .. s10 + 12, writable (the
   frame (1, pos) is the run's own, so the journal allows them). The facts of the KDISP cut at the new memory: the
   eight bytes read back from the region (field_of_region), every other byte kept (kept_of_frame), and the cut's
   reader facts carried across by kq_keep (a byte of the text, the mconf block, a frame slot or the frame is outside
   the shadow band; a shadow byte an addressable range reads is not one of the eight, which held 0xf8 before).
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_keya_m m_file_s_keya_d m_file_s_keya_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x8665c, after the quotes: s5 / s7 the unquoted value, s8 = line + 1 *)
Definition KA_M : Z := AF_m_file + 0x7a0.

(* ---- the token run's states at J4 ---- *)
Definition j4_Bx : sv := SOff 18 0.
(* vl < 2: no byte is read *)
Definition j0_ss : sstate := mkSS KA_J4 sr_atoms [] None (mkFacts [ (18%nat, mkAF SB SB 0) ] [] []).
(* vl >= 2: v[0] at s5 (atom 32) and v[vl - 1] at s7 - 1 (atom 33), read-only *)
Definition j2_regions : smem :=
[ YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 23%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 33 0))] ].
Definition j2_facts : facts :=
mkFacts [ (18%nat, mkAF SB SB 0); (21%nat, mkAF 0 (2 ^ 47 - 2) 0); (23%nat, mkAF 1 (2 ^ 47 - 1) 0);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition j2_ss : sstate := mkSS KA_J4 sr_atoms j2_regions None j2_facts.
(* the registers the run J4 .. 0x8665c does not write (it writes a0, a1, a3, a4, s5, s7, s8) *)
Definition J4_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 25; 26; 27]%bv.

(* ---- the plain run's state at 0x8665c ---- *)
Definition km_regions : smem := [ YP09.mkRegion (Some 26%nat) 4 12 4 12 [] ].
Definition km_ss : sstate := mkSS KA_M sr_atoms km_regions None (mkFacts [] [] []).
(* the registers the run 0x8665c .. KDISP does not write (it writes s6, s4) *)
Definition KM_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 21; 23; 24; 25; 26; 27]%bv.

(* low.i's 8 shadow bytes of the frame at F *)
Definition kq_win (F x : Z) : Prop := SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 12.

Lemma kq_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma kq_U_neg : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SMd M_MUL (SOff n 0) (SLit (-1))) = (- v) mod 2 ^ 64.
Proof.
intros E n v H Hv. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n v H Hv), U_SLit.
unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (v * (2 ^ 64 - 1)) with (- v + v * 2 ^ 64) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
(* a2 - s11 and s7 - s5 as the executor forms them *)
Lemma kq_U_diffA : forall E n1 v1 n2 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 - v2 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n1 0) (SMd M_MUL (SOff n2 0) (SLit (-1)))) = v1 - v2.
Proof.
intros E n1 v1 n2 v2 H1 H2 R1 R2 R12. rewrite U_SAlu. cbn [zalu_raw].
rewrite (kq_U_neg E n2 v2 H2 R2), (U_atom E n1 v1 H1 R1). unfold zcanon, M64.
rewrite Z.add_mod_idemp_r by lia. replace (v1 + - v2) with (v1 - v2) by ring. apply Z.mod_small. lia.
Qed.
Lemma kq_U_diffB : forall E n1 v1 n2 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 - v2 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n2 0) (SLit (-1))) (SOff n1 0)) = v1 - v2.
Proof.
intros E n1 v1 n2 v2 H1 H2 R1 R2 R12. rewrite U_SAlu. cbn [zalu_raw].
rewrite (kq_U_neg E n2 v2 H2 R2), (U_atom E n1 v1 H1 R1). unfold zcanon, M64.
rewrite Z.add_mod_idemp_l by lia. replace (- v2 + v1) with (v1 - v2) by ring. apply Z.mod_small. lia.
Qed.
(* a register of a state as its symbolic value, without normalizing it *)
Ltac kreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* `blt a0,a1` after `sub a0,n1,n2`: the difference against a small literal *)
Lemma kq_br_lt : forall E n1 v1 n2 v2 k b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 - v2 < 2 ^ 63 -> 0 <= k < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n2 0) (SLit (-1))) (SOff n1 0)))
  (sv_denot E (SLit k)) = b ->
(v1 - v2 <? k) = b.
Proof.
intros E n1 v1 n2 v2 k b H1 H2 R1 R2 R12 Rk Hc.
rewrite YO0c.branch_lt in Hc.
assert (A1 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n2 0) (SLit (-1))) (SOff n1 0))) = v1 - v2)
  by exact (kq_U_diffB E n1 v1 n2 v2 H1 H2 R1 R2 ltac:(lia)).
assert (A2 : bv_unsigned (sv_denot E (SLit k)) = k)
  by (change (U E (SLit k) = k); rewrite U_SLit; apply zcanon_id; unfold M64; lia).
rewrite A1, A2, (YO0b.s64_small (v1 - v2) ltac:(lia)), (YO0b.s64_small k ltac:(lia)) in Hc. exact Hc.
Qed.
(* `beq`/`bne` of two byte atoms, or of a byte atom against a literal *)
Lemma kq_br_eq_lit : forall E n v k b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit k)) = b -> (v =? k) = b.
Proof.
intros E n v k b H Hv Hk Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma kq_br_ne_lit : forall E n v k b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit k)) = b -> negb (v =? k) = b.
Proof.
intros E n v k b H Hv Hk Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma kq_br_eq_at : forall E n1 v1 n2 v2 b, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = b -> (v1 =? v2) = b.
Proof.
intros E n1 v1 n2 v2 b H1 H2 R1 R2 Hc.
rewrite branch_eq_U, (U_atom E n1 v1 H1 R1), (U_atom E n2 v2 H2 R2) in Hc. exact Hc.
Qed.
(* `xor a1,a3,a1; seqz a1,a1; add s5,s5,a1`: s5 goes on by one when the two bytes are equal *)
Lemma kq_U_seqz : forall E n0 v0 n1 v1 n2 v2,
ew E n0 = Z_to_bv 64 v0 -> ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
0 <= v0 -> v0 + 1 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n0 0) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff n1 0) (SOff n2 0)) (SLit 1)))
  = v0 + (if v1 =? v2 then 1 else 0).
Proof.
intros E n0 v0 n1 v1 n2 v2 H0 H1 H2 R0 R0' R1 R2.
pose proof (Z_lxor_range v1 v2 R1 R2) as HX.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n0 v0 H0 ltac:(lia)).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n1 v1 H1 R1), (U_atom E n2 v2 H2 R2).
rewrite (zcanon_id (Z.lxor v1 v2)) by (unfold M64; lia).
rewrite (zcanon_id 1) by (unfold M64; lia).
destruct (Z.eqb_spec v1 v2) as [-> | Hne].
- rewrite Z.lxor_nilpotent. cbn [Z.ltb Z.compare].
  rewrite (zcanon_id 1) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
- assert (Hnz : Z.lxor v1 v2 <> 0) by (intros Hz; apply Hne; apply Z.lxor_eq; exact Hz).
  replace (Z.lxor v1 v2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- environments and seeds ---- *)
Definition j_E (regs1 : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs1 extra).
Lemma j_ew_reg : forall regs1 extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (j_E regs1 extra) n = getr regs1 r.
Proof.
intros regs1 extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold j_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma j_ew_extra : forall regs1 extra j, (32 + j < A_TEXT)%nat -> ew (j_E regs1 extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros. unfold j_E. rewrite Eimg_low by exact H. apply ew_Ereg_extra. Qed.
Lemma j_env_agree : forall regs1 extra, env_agree 32 (Ereg regs1 extra) (j_E regs1 extra).
Proof. intros. split; [intros n Hn; unfold j_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seed at 0x8665c: low.i's shadow bytes at s10 + 4 .. s10 + 12, writable *)
Lemma km_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc S0,
getr regs1 26 = w64 S0 -> 0 <= S0 -> S0 + 12 <= 2 ^ 64 ->
(forall o, 4 <= o < 12 -> apresent (w_H W) memc (S0 + o)) ->
st_ok_pi SEGS VAL (j_E regs1 []) km_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KA_M)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc S0 H26 HS0 HS1 HP.
assert (E26 : ew (j_E regs1 []) 26 = Z_to_bv 64 S0) by (rewrite (j_ew_reg regs1 [] 26 26%bv eq_refl); exact H26).
rewrite restrict_mkst_fx. unfold km_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E26, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- exact (conj I I).
- split; [exact I | split; exact I].
Qed.

(* the seed at J4 for vl < 2 *)
Lemma j0_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc,
getr regs1 18 = w64 SHADOW_OFF ->
st_ok_pi SEGS VAL (j_E regs1 []) j0_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KA_J4)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc H18.
assert (E18 : ew (j_E regs1 []) 18 = Z_to_bv 64 SB) by (rewrite (j_ew_reg regs1 [] 18 18%bv eq_refl); exact H18).
rewrite restrict_mkst_fx. unfold j0_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* the seed at J4 for vl >= 2: v[0] = C0 at P0 = s5, v[vl - 1] = C1 at P1 - 1 (P1 = s7) *)
Lemma j2_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc P0 P1 C0 C1,
getr regs1 21 = w64 P0 -> getr regs1 23 = w64 P1 -> getr regs1 18 = w64 SHADOW_OFF ->
0 <= P0 -> P0 + 1 <= P1 - 1 -> P1 <= 2 ^ 47 - 1 ->
rdW W memc P0 = Some C0 -> rdW W memc (P1 - 1) = Some C1 ->
st_ok_pi SEGS VAL (j_E regs1 [Z_to_bv 64 C0; Z_to_bv 64 C1]) j2_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + KA_J4)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc P0 P1 C0 C1 H21 H23 H18 HP0 HP01 HP1 Hr0 Hr1.
destruct (aview_byte SEGS (w_H W) memc P0 C0 Hr0) as (b0 & Hb0 & Hv0 & HC0).
destruct (aview_byte SEGS (w_H W) memc (P1 - 1) C1 Hr1) as (b1 & Hb1 & Hv1 & HC1).
set (E := j_E regs1 [Z_to_bv 64 C0; Z_to_bv 64 C1]).
assert (E21 : ew E 21 = Z_to_bv 64 P0) by (subst E; rewrite (j_ew_reg _ _ 21 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 P1) by (subst E; rewrite (j_ew_reg _ _ 23 23%bv eq_refl); exact H23).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite (j_ew_reg _ _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 C0) by (subst E; exact (j_ew_extra _ _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 C1) by (subst E; exact (j_ew_extra _ _ 1 ltac:(unfold A_TEXT; lia))).
rewrite restrict_mkst_fx. unfold j2_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E21, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    exists b0. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
      rewrite !Z.add_0_r, (unsigned_lit_small C0), (unsigned_lit_small C0) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      subst C0. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb0.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E23, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    exists b1. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E33.
      rewrite !Z.add_0_r, (unsigned_lit_small C1), (unsigned_lit_small C1) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      subst C1. apply Z_to_bv_bv_unsigned.
    * replace (P1 + -1 + 0) with (P1 - 1) by lia. exact Hb1.
- cbn [j2_regions pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E21, E23, !unsigned_lit_small by lia.
  split; [split; [left; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  cbn [j2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E21, E23, E32, E33, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* ---- a run that writes nothing keeps every byte's view ---- *)
Lemma kq_ro_keep : forall E rs (m0 m m' : word -> option byte) (H : word -> bool),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs m0 m m' H HFr Hro KM a Ha.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HFr); [exact (KM a Ha) | | exact Ha | intros []].
intros b wlo whi a' Hin Hr. unfold windows in Hin. apply in_map_iff in Hin as (r & Hq & Hr').
rewrite forallb_forall in Hro. specialize (Hro r Hr'). apply Z.leb_le in Hro.
injection Hq as <- <- <-. lia.
Qed.
Lemma kq_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma kq_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.

(* ---- the reader facts across a run that writes only low.i's shadow bytes ---- *)
Lemma kq_vm : forall H (m m' : word -> option byte) x n v,
(forall k, (k < n)%nat -> aview SEGS H m' (x + Z.of_nat k) = aview SEGS H m (x + Z.of_nat k)) ->
val_mem SEGS (mrestrict H m) x n v -> val_mem SEGS (mrestrict H m') x n v.
Proof.
intros H m m' x n v K Hv k Hk. specialize (Hv k Hk). specialize (K k Hk). unfold aview in K. rewrite Hv in K.
destruct (mbyte SEGS (mrestrict H m') (x + Z.of_nat k)) as [b|]; cbn [option_map] in K; [|discriminate K].
injection K as K. f_equal. apply bv_eq. exact K.
Qed.
(* every byte keeps its view, or it is one of the eight: 0xf8 before, 0 after *)
Definition kq_sp (H : word -> bool) (m m' : word -> option byte) : Prop :=
forall x, aview SEGS H m' x = aview SEGS H m x \/ (aview SEGS H m x = Some 248 /\ aview SEGS H m' x = Some 0).
Lemma kq_split : forall H (m m' : word -> option byte) F,
0 <= F / 8 -> SHADOW_OFF + F / 8 + 12 <= 2 ^ 64 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ kq_win F x -> aview SEGS H m' x = aview SEGS H m x) ->
(forall i, 4 <= i < 12 -> aview SEGS H m (SHADOW_OFF + F / 8 + i) = Some 248) ->
(forall i, 4 <= i < 12 -> aview SEGS H m' (SHADOW_OFF + F / 8 + i) = Some 0) ->
kq_sp H m m'.
Proof.
intros H m m' F HF0 HF1 K V0 V1 x.
rewrite (ka_aview_mod H m' x), (ka_aview_mod H m x).
pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hx.
set (y := x mod 2 ^ 64) in *.
destruct (Z_lt_le_dec y (SHADOW_OFF + F / 8 + 4)) as [Hl|Hl]; [left; apply K; [lia | unfold kq_win; lia]|].
destruct (Z_lt_le_dec y (SHADOW_OFF + F / 8 + 12)) as [Hh|Hh]; [|left; apply K; [lia | unfold kq_win; lia]].
right. replace y with (SHADOW_OFF + F / 8 + (y - SHADOW_OFF - F / 8)) by lia.
split; [apply V0 | apply V1]; lia.
Qed.
Lemma kq_some : forall H m m', kq_sp H m m' -> forall x, aview SEGS H m x <> None -> aview SEGS H m' x <> None.
Proof. intros H m m' SP x Hx. destruct (SP x) as [E|[_ E]]; rewrite E; [exact Hx | discriminate]. Qed.
Lemma kq_ra : forall H m m', kq_sp H m m' -> forall q n,
range_addressable (aview SEGS H m) SHADOW_OFF q n -> range_addressable (aview SEGS H m') SHADOW_OFF q n.
Proof.
intros H m m' SP q n HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (SP (shadow_of_addr SHADOW_OFF x)) as [E|[E0 _]]; [rewrite E; exact Hs|].
exfalso. rewrite E0 in Hs. injection Hs as <-. unfold saddr_ok in Hok. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.
Lemma kq_sa_addr : forall H m m', kq_sp H m m' -> forall q n,
sa_addr (aview SEGS H m) q n -> sa_addr (aview SEGS H m') q n.
Proof.
intros H m m' SP q n (H0 & H1 & H2 & H3 & H4).
refine (conj H0 (conj H1 (conj H2 (conj (kq_ra H m m' SP q n H3) _)))).
intros Hn s Hs. exact (kq_some H m m' SP s (H4 Hn s Hs)).
Qed.
Lemma kq_sa_tail : forall H m m', kq_sp H m m' -> forall e, sa_tail (aview SEGS H m) e -> sa_tail (aview SEGS H m') e.
Proof. intros H m m' SP e HT x Hx. exact (kq_some H m m' SP x (HT x Hx)). Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* the cut facts at a memory that differs from memc only in low.i's 8 shadow bytes, now 0 *)
Lemma kq_keep : forall v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest,
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc (mf_next p rest) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ kq_win (frame_addr lyc 1 pos) x -> rdW Wc memc' x = rdW Wc memc x) ->
(forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) memc') (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_ON) ->
mf_core B v lyc Sc Wc memc' mdc' pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc' Wc cur /\
mf_loop v Wc memc' mcc cur line p rest /\ mf_np v memc' Wc (mf_next p rest).
Proof.
intros v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest CORE CELLS LOOP NP HJ' KM VW.
destruct CORE as (HJ & HPm & VFL & VSH & VSV & V112 & MC & MA & MT).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & HFapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 1) with 128 in *.
destruct HSTK as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HSTKv : SegInstA.STK_m_file = 8560) by reflexivity.
rewrite HSTKv in Hslo.
set (F := frame_addr lyc 1 pos) in *.
set (sp0 := mv_sp v) in *.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44 - 16) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HW : SHADOW_OFF + F / 8 + 12 <= kHighMemBeg) by (rewrite C3; unfold SHADOW_OFF; lia).
change MF_LOW_ON with 0 in VW. change MF_LOW_OFF with 248 in VSH.
assert (SP : kq_sp (w_H Wc) memc memc').
{ apply (kq_split (w_H Wc) memc memc' F); [lia | unfold SHADOW_OFF; lia | exact KM | |].
  - intros i Hi. apply aview_of_val_mem1; [exact (VSH i Hi) | lia].
  - intros i Hi. apply aview_of_val_mem1; [exact (VW i Hi) | lia]. }
assert (NW : forall x, 0 <= x < 2 ^ 64 -> (x < SHADOW_OFF \/ kHighMemBeg <= x) -> rdW Wc memc' x = rdW Wc memc x).
{ intros x Hx Hz. apply KM; [exact Hx|]. unfold kq_win. lia. }
assert (VK : forall x n w, 0 <= x -> x + Z.of_nat n <= 2 ^ 64 -> (x + Z.of_nat n <= SHADOW_OFF \/ kHighMemBeg <= x) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) x n w -> val_mem SEGS (mrestrict (w_H Wc) memc') x n w).
{ intros x n w H0 H1 H2. apply kq_vm. intros k Hk. apply NW; lia. }
assert (Hs1 : sp0 - 320 <= mf_s1 sp0 <= sp0 - 288).
{ unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)). lia. }
assert (VSL : forall k w, 0 <= k <= 280 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 sp0 + k) 8 w -> val_mem SEGS (mrestrict (w_H Wc) memc') (mf_s1 sp0 + k) 8 w).
{ intros k w Hk. apply VK; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
destruct LOOP as (L1 & L2 & L3 & ((ZS & Z0) & ZT) & SA & L6 & L7 & L8 & L9 & L10 & L11).
pose proof SA as (Hp0 & Hp63 & HAMp & _).
pose proof MA as (Hc0 & Hc63 & HAMc & _).
assert (TXT : forall x, p <= x < p + (Z.of_nat (length rest) + 1) -> rdW Wc memc' x = rdW Wc memc x).
{ intros x Hx. apply NW; [lia|]. unfold amem_range, kLowMemEnd, kHighMemEnd in HAMp. unfold SHADOW_OFF. lia. }
assert (BLK : forall x, mv_c v <= x < mv_c v + seg_spec.SEG_M_SIZE -> rdW Wc memc' x = rdW Wc memc x).
{ intros x Hx. apply NW; [lia|]. unfold amem_range, kLowMemEnd, kHighMemEnd in HAMc. unfold SHADOW_OFF. lia. }
destruct CELLS as (C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C104 & C120 & C128 & C136 & C152).
split; [|split; [|split]].
- refine (conj HJ' (conj HPm (conj _ (conj _ (conj _ (conj (VSL 112 _ ltac:(lia) V112) (conj _ (conj _ _)))))))).
  + apply VK; [lia | lia | |exact VFL]. unfold in_app, kLowShadowBeg in HFapp. unfold SHADOW_OFF. lia.
  + change MF_LOW_ON with 0. exact VW.
  + intros jj r Hr. pose proof (VSV jj r Hr) as V.
    assert (Hj : (jj < length mf_saved_regs)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
    cbn [length mf_saved_regs] in Hj.
    apply VK; [lia | lia | lia | exact V].
  + destruct MC as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
    pose proof (proj1 Henc) as Hlen. intros k Hk. rewrite BLK by lia. exact (Hbs k Hk).
  + exact (kq_sa_addr _ _ _ SP _ _ MA).
  + exact (kq_sa_tail _ _ _ SP _ MT).
- exact (conj (VSL 24 _ ltac:(lia) C24) (conj (VSL 32 _ ltac:(lia) C32) (conj (VSL 40 _ ltac:(lia) C40)
    (conj (VSL 48 _ ltac:(lia) C48) (conj (VSL 56 _ ltac:(lia) C56) (conj (VSL 64 _ ltac:(lia) C64)
    (conj (VSL 72 _ ltac:(lia) C72) (conj (VSL 80 _ ltac:(lia) C80) (conj (VSL 88 _ ltac:(lia) C88)
    (conj (VSL 104 _ ltac:(lia) C104) (conj (VSL 120 _ ltac:(lia) C120) (conj (VSL 128 _ ltac:(lia) C128)
    (conj (VSL 136 _ ltac:(lia) C136) (VSL 152 _ ltac:(lia) C152)))))))))))))).
- refine (conj L1 (conj L2 (conj L3 (conj (conj (conj _ Z0) (kq_sa_tail _ _ _ SP _ ZT))
    (conj (kq_sa_addr _ _ _ SP _ _ SA) (conj L6 (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))).
  intros k Hk. rewrite length_app in Hk. cbn [length] in Hk. rewrite TXT by lia. exact (ZS k ltac:(rewrite length_app; cbn [length]; lia)).
- exact (VSL 144 _ ltac:(lia) NP).
Qed.

(* ======================== 0x8665c: s6 := kl, s4 := vl, low.i's shadow := 0, KDISP ======================== *)
Definition KA_M_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c d : nat),
ka_ctx B v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> mf_regs_at B v lyc pos regs1 ->
(a <= b <= length (mf_line rest))%nat -> (c <= d <= length (mf_line rest))%nat ->
mf_fin (mk_disp mcc gi (slice a b (mf_line rest)) (slice c d (mf_line rest)) (line + 1), Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (p + Z.of_nat a) -> getr regs1 12 = w64 (p + Z.of_nat b) ->
getr regs1 21 = w64 (p + Z.of_nat c) -> getr regs1 23 = w64 (p + Z.of_nat d) ->
getr regs1 24 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KA_M.

Lemma ka_m : forall n, MF_KDISP_stmt B n -> KA_M_stmt n.
Proof.
intros n KD. unfold MF_KDISP_stmt, MF_KAT_stmt, mf_at in KD.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d CTX RG Hab Hcd HFIN' R27 R12 R21 R23 R24.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
unfold shadow_addr in HFSpres.
set (F := frame_addr lyc 1 pos) in *.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44 - 16) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (S0 := SHADOW_OFF + F / 8) in *.
assert (HS0 : 0 <= S0 /\ S0 + 12 <= 2 ^ 47) by (unfold S0, SHADOW_OFF; lia).
pose proof (km_entry Wc regs1 memc S0 R26 ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia))))) as HS.
assert (HEI : img_env VAL A_LIM (j_E regs1 [])) by (unfold j_E; apply Eimg_env).
pose proof (j_env_agree regs1 []) as HA0.
assert (E26 : ew (j_E regs1 []) 26 = Z_to_bv 64 S0) by (rewrite (j_ew_reg regs1 [] 26 26%bv eq_refl); exact R26).
assert (U26 : bv_unsigned (ew (j_E regs1 []) 26) = S0) by (rewrite E26; apply unsigned_lit_small; lia).
paj_run_to_sh RUNTOP HS HJ MF_KDISP.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 26%nat S0); [reflexivity | exact U26 | | apply awr_ok_nil].
  intros x Hx. cbn [YP09.r_wlo YP09.r_whi] in Hx. right; right; right; left. exists 1, pos.
  split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
  change (fs_frame_bytes 1 / 8) with 16. fold F. fold S0. lia. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the registers: the kept ones, s6 = a2 - s11 = kl, s4 = s7 - s5 = vl *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ KM_KEPT HS HA0 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
kreg HS (22%bv : bv 5) N22. kreg HS (20%bv : bv 5) N20.
assert (E12 : ew (j_E regs1 []) 12 = Z_to_bv 64 (p + Z.of_nat b)) by (rewrite (j_ew_reg regs1 [] 12 12%bv eq_refl); exact R12).
assert (E27 : ew (j_E regs1 []) 27 = Z_to_bv 64 (p + Z.of_nat a)) by (rewrite (j_ew_reg regs1 [] 27 27%bv eq_refl); exact R27).
assert (E21 : ew (j_E regs1 []) 21 = Z_to_bv 64 (p + Z.of_nat c)) by (rewrite (j_ew_reg regs1 [] 21 21%bv eq_refl); exact R21).
assert (E23 : ew (j_E regs1 []) 23 = Z_to_bv 64 (p + Z.of_nat d)) by (rewrite (j_ew_reg regs1 [] 23 23%bv eq_refl); exact R23).
pose proof (mf_line_len rest) as HLr.
(* low.i's shadow bytes, read back from the region *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth 0 rs (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (Z0 : forall Ex, bv_unsigned (sv_denot Ex (SLit 0)) mod 2 ^ (8 * Z.of_N 1) = MF_LOW_ON) by (intros; vm_compute; reflexivity).
assert (VW : forall k, 4 <= k < 12 -> val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (S0 + k) 1 MF_LOW_ON).
{ intros k Hk.
  assert (Ek : k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct Ek as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  match goal with |- val_mem _ _ (_ + ?kk) _ _ =>
    pose proof (field_of_region_any (segs := SEGS) _ _ 26 S0 _ _ _ _ _ kk 1%N (SLit 0) HR0 U26
      ltac:(repeat (first [left; reflexivity | right])) ltac:(lia)) as V end;
  rewrite Z0 in V; exact V. }
(* every other byte keeps its view *)
assert (KW : forall x, 0 <= x < 2 ^ 64 -> ~ kq_win F x -> rdW Wc (ms_mem ms) x = rdW Wc memc x).
{ intros x Hx Hnw.
  refine (kept_of_frame (segs := SEGS) (j_E regs1 []) km_regions (w_H Wc) memc (ms_mem ms) (kq_win F) HFr _ x Hx Hnw).
  intros bb wlo whi y Hwn Hy. cbn [windows map km_regions YP09.r_base YP09.r_wlo YP09.r_whi In] in Hwn.
  destruct Hwn as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hy. rewrite U26 in Hy.
  unfold kq_win. unfold S0 in Hy. lia. }
destruct (kq_keep v lyc Sc Wc memc mdc (ms_mem ms) mdv pos mcc (Some gi) line p rest CORE CELLS LOOP NP HJ KW VW)
  as (CORE' & CELLS' & LOOP' & NP').
pmkst HS.
apply (KD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv pos mcc gi line p rest a (b - a)%nat c (d - c)%nat
  (slice a b (mf_line rest)) (slice c d (mf_line rest)) CX LS FRM CORE' CELLS').
- unfold mf_regs_at. rewrite !HK by (cbv [KM_KEPT In]; tauto). exact RG.
- exact Hn.
- exact Hr.
- exact LOOP'.
- exact (ka_mk_kv rest a b c d Hab Hcd).
- constructor.
- exact HFIN'.
- rewrite HK by (cbv [KM_KEPT In]; tauto). exact R27.
- rewrite N22. unfold w64. apply kq_den.
  rewrite (kq_U_diffA _ 12 (p + Z.of_nat b) 27 (p + Z.of_nat a) E12 E27) by lia. lia.
- rewrite HK by (cbv [KM_KEPT In]; tauto). exact R21.
- rewrite N20. unfold w64. apply kq_den.
  rewrite (kq_U_diffB _ 23 (p + Z.of_nat d) 21 (p + Z.of_nat c) E23 E21) by lia. lia.
- rewrite HK by (cbv [KM_KEPT In]; tauto). rewrite R23. unfold w64. f_equal. lia.
- rewrite HK by (cbv [KM_KEPT In]; tauto). exact R24.
- exact NP'.
Qed.

(* ======================== J4 0x865f0: the quotes, to 0x8665c ======================== *)
(* after a token run: the environment agrees with the seed's E0 below 34 (HAE), every byte keeps its view (KM) *)
Ltac kq_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (kq_ro_keep Eo _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac kq_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyv own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Lemma ka_j4 : forall n, MF_KDISP_stmt B n -> KA_J4_stmt B n.
Proof.
intros n KD. pose proof (ka_m n KD) as KMS. clear KD.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d CTX RG KAT VF Hcd HABd Hsd R21 R23 R12 R27.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP).
pose proof LOOP as (_ & _ & _ & ((ZS & _) & _) & (Hp0 & _ & HAM & HRA & _) & _ & _ & Hln0 & HlnU & _ & _).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26) & R22).
pose proof CORE as (HJ & _).
pose proof (mf_line_len rest) as HLr.
pose proof (memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite slice_length in Hei by lia.
pose proof KAT as (Hia & Hbe & HA1 & HA2 & HB1 & HB2).
pose proof VF as (Hcj & HC1 & HC2).
set (L := mf_line rest) in *.
assert (HKY : h_strip (firstn ei (slice i j L)) = slice a b L) by (apply ka_key_idx; first [lia | assumption]).
assert (HVL : h_strip (skipn (S ei) (slice i j L)) = slice c d L) by (apply ka_val_idx; first [lia | assumption]).
rewrite HKY, HVL, (ka_unquote_idx L c d ltac:(lia)) in HFIN.
assert (HPb : p + Z.of_nat (length rest) + 1 <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; lia).
(* a leaf at 0x8665c with the value [c', d') *)
assert (CM : forall regs1' memc' mdc' c' d',
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
  (forall r, In r J4_KEPT -> getr regs1' r = getr regs1 r) ->
  (c' <= d' <= length L)%nat ->
  slice c' d' L = (if ka_q L c d then slice (S c) (d - 1) L else slice c d L) ->
  getr regs1' 21 = w64 (p + Z.of_nat c') -> getr regs1' 23 = w64 (p + Z.of_nat d') ->
  getr regs1' 24 = w64 (line + 1) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + KA_M)) memc' (seg_rom SEGS)) mdc') (MF_POST B v)).
{ intros regs1' memc' mdc' c' d' HJ' KM' HK Hcd' Hsl R21' R23' R24'.
  apply (KMS v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest i j ei a b c' d'
    (ka_ctx_kept B v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n CTX HJ' KM')).
  - unfold mf_regs_at. rewrite !HK by (cbv [J4_KEPT In]; tauto). exact (proj1 RG).
  - change (length (mf_line rest)) with (length L). lia.
  - exact Hcd'.
  - change (mf_line rest) with L. rewrite Hsl. exact HFIN.
  - rewrite HK by (cbv [J4_KEPT In]; tauto). exact R27.
  - rewrite HK by (cbv [J4_KEPT In]; tauto). exact R12.
  - exact R21'.
  - exact R23'.
  - exact R24'. }
unfold mf_at.
destruct (Nat.ltb_spec (d - c) 2) as [Hlt | Hge].
- (* vl < 2: no quote test *)
  pose proof (j0_entry Wc regs1 memc R18) as HS.
  assert (SHOK : sh_ok SEGS j4_Bx [] (j_E regs1 []) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
  assert (HEI : img_env VAL A_LIM (j_E regs1 [])) by (unfold j_E; apply Eimg_env).
  pose proof (j_env_agree regs1 []) as HA0.
  assert (E21 : ew (j_E regs1 []) 21 = Z_to_bv 64 (p + Z.of_nat c)) by (rewrite (j_ew_reg regs1 [] 21 21%bv eq_refl); exact R21).
  assert (E23 : ew (j_E regs1 []) 23 = Z_to_bv 64 (p + Z.of_nat d)) by (rewrite (j_ew_reg regs1 [] 23 23%bv eq_refl); exact R23).
  assert (E22 : ew (j_E regs1 []) 22 = Z_to_bv 64 (line + 1)) by (rewrite (j_ew_reg regs1 [] 22 22%bv eq_refl); exact R22).
  revert HS SHOK HEI HA0 E21 E23 E22. generalize (j_E regs1 []) as E0. intros E0 HS SHOK HEI HA0 E21 E23 E22.
  pose proof (env_agree_refl 34 E0) as HAE.
  assert (KM : forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc x = rdW Wc memc x) by (intros; reflexivity).
  paj_run_tok RUN HS HJ SHOK Bspan. { kq_awr. }
  kq_after E0 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* vl < 2 taken: 0x86658 mv s8,s6, KA_M with the value unchanged *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
    kq_after E0 HAE KM.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
    pmkst HS.
    refine (CM _ _ _ c d HJ KM HK ltac:(lia) _ _ _ _).
    * unfold ka_q. rewrite (proj2 (Nat.leb_gt 2 (d - c)) ltac:(lia)). reflexivity.
    * rewrite N21. apply kq_den. apply (U_atom E0 21 _ E21). lia.
    * rewrite N23. apply kq_den. apply (U_atom E0 23 _ E23). lia.
    * rewrite N24. apply kq_den. apply (U_atom E0 22 _ E22). lia.
  + (* vl < 2 not taken: impossible *)
    exfalso.
    pose proof (kq_br_lt _ 23 (p + Z.of_nat d) 21 (p + Z.of_nat c) 2 false E23 E21
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc) as X.
    apply Z.ltb_ge in X. lia.
- (* vl >= 2: the checks of v[0] and v[vl - 1] *)
  assert (Hr0 : rdW Wc memc (p + Z.of_nat c) = Some (nth c L 0)).
  { rewrite (ZS c ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    rewrite app_nth1 by lia. subst L. apply mf_line_nth. lia. }
  assert (Hr1 : rdW Wc memc (p + Z.of_nat d - 1) = Some (nth (d - 1) L 0)).
  { replace (p + Z.of_nat d - 1) with (p + Z.of_nat (d - 1)) by lia.
    rewrite (ZS (d - 1)%nat ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    rewrite app_nth1 by lia. subst L. apply mf_line_nth. lia. }
  destruct (aview_byte SEGS (w_H Wc) memc _ _ Hr0) as (_ & _ & _ & HB0).
  destruct (aview_byte SEGS (w_H Wc) memc _ _ Hr1) as (_ & _ & _ & HB1').
  pose proof (j2_entry Wc regs1 memc (p + Z.of_nat c) (p + Z.of_nat d) (nth c L 0) (nth (d - 1) L 0) R21 R23 R18
    ltac:(lia) ltac:(lia) ltac:(lia) Hr0 Hr1) as HS.
  assert (SHOK : sh_ok SEGS j4_Bx [] (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)])
    (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
  assert (HEI : img_env VAL A_LIM (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]))
    by (unfold j_E; apply Eimg_env).
  pose proof (j_env_agree regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) as HA0.
  assert (E21 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 21
    = Z_to_bv 64 (p + Z.of_nat c)) by (rewrite (j_ew_reg _ _ 21 21%bv eq_refl); exact R21).
  assert (E23 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 23
    = Z_to_bv 64 (p + Z.of_nat d)) by (rewrite (j_ew_reg _ _ 23 23%bv eq_refl); exact R23).
  assert (E22 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 22
    = Z_to_bv 64 (line + 1)) by (rewrite (j_ew_reg _ _ 22 22%bv eq_refl); exact R22).
  assert (E18 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 18
    = Z_to_bv 64 SB) by (rewrite (j_ew_reg _ _ 18 18%bv eq_refl); exact R18).
  assert (E32 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 32
    = Z_to_bv 64 (nth c L 0)) by exact (j_ew_extra _ _ 0 ltac:(unfold A_TEXT; lia)).
  assert (E33 : ew (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) 33
    = Z_to_bv 64 (nth (d - 1) L 0)) by exact (j_ew_extra _ _ 1 ltac:(unfold A_TEXT; lia)).
  revert HS SHOK HEI HA0 E21 E23 E22 E18 E32 E33.
  generalize (j_E regs1 [Z_to_bv 64 (nth c L 0); Z_to_bv 64 (nth (d - 1) L 0)]) as E0.
  intros E0 HS SHOK HEI HA0 E21 E23 E22 E18 E32 E33.
  pose proof (env_agree_refl 34 E0) as HAE.
  assert (KM : forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc x = rdW Wc memc x) by (intros; reflexivity).
  paj_run_tok RUN HS HJ SHOK Bspan. { kq_awr. }
  kq_after E0 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + exfalso.
    pose proof (kq_br_lt _ 23 (p + Z.of_nat d) 21 (p + Z.of_nat c) 2 true
      (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc) as X.
    apply Z.ltb_lt in X. lia.
  + clear Hc.
    (* the check of v[0] at s5 *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { unfold j4_Bx.
      rewrite (U_atom _ 18 SB (kq_ag_ew _ _ 18 _ HAE ltac:(lia) E18) ltac:(unfold SB; lia)).
      rewrite (U_atom _ 21 _ (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) ltac:(lia)).
      rewrite SB_SHADOW_OFF.
      lazymatch goal with |- range_addressable (YCbn.rd_of SEGS (mrestrict (w_H Wc) ?mm)) _ _ _ =>
        change (YCbn.rd_of SEGS (mrestrict (w_H Wc) mm)) with (aview SEGS (w_H Wc) mm) end.
      rewrite (ka_rd_ext (w_H Wc) memc _ KM).
      exact (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat c) 1 HRA
        ltac:(lia) ltac:(lia)). }
    { kq_awr. }
    kq_after E0 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* v[0] = '\'' *)
      pose proof (kq_br_eq_lit _ 32 (nth c L 0) 39 true (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
        ltac:(lia) ltac:(lia) Hc) as C39. clear Hc.
      paj_run_tok RUN HS HJ SHOK Bspan.
      { unfold j4_Bx.
        rewrite (U_atom _ 18 SB (kq_ag_ew _ _ 18 _ HAE ltac:(lia) E18) ltac:(unfold SB; lia)).
        rewrite (U_atom_off _ 23 _ (-1) (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) ltac:(lia) ltac:(lia)).
        rewrite SB_SHADOW_OFF.
        lazymatch goal with |- range_addressable (YCbn.rd_of SEGS (mrestrict (w_H Wc) ?mm)) _ _ _ =>
          change (YCbn.rd_of SEGS (mrestrict (w_H Wc) mm)) with (aview SEGS (w_H Wc) mm) end.
        rewrite (ka_rd_ext (w_H Wc) memc _ KM).
        refine (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) _ 1 HRA _ _); lia. }
      { kq_awr. }
      kq_after E0 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* v[vl - 1] = v[0]: the pair goes *)
         pose proof (kq_br_eq_at _ 33 (nth (d - 1) L 0) 32 (nth c L 0) true
           (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33) (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
           ltac:(lia) ltac:(lia) Hc) as CQ. clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
         kq_after E0 HAE KM.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE)
           ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
         pmkst HS.
         refine (CM _ _ _ (S c) (d - 1)%nat HJ KM HK ltac:(lia) _ _ _ _).
         ++ unfold ka_q. rewrite (proj2 (Nat.leb_le 2 (d - c)) ltac:(lia)), C39, CQ, orb_true_r. reflexivity.
         ++ rewrite N21. apply kq_den.
            rewrite (kq_U_seqz _ 21 (p + Z.of_nat c) 33 (nth (d - 1) L 0) 32 (nth c L 0)
              (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33)
              (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
            rewrite CQ. lia.
         ++ rewrite N23. apply kq_den.
            rewrite (U_atom_off _ 23 (p + Z.of_nat d) (-1) (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23)
              ltac:(lia) ltac:(lia)). lia.
         ++ rewrite N24. apply kq_den. refine (U_atom _ 22 _ (kq_ag_ew _ _ 22 _ HAE ltac:(lia) E22) _). lia.
      -- (* v[vl - 1] <> v[0]: nothing goes *)
         pose proof (kq_br_eq_at _ 33 (nth (d - 1) L 0) 32 (nth c L 0) false
           (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33) (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
           ltac:(lia) ltac:(lia) Hc) as CQ. clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
         kq_after E0 HAE KM.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE)
           ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
         pmkst HS.
         refine (CM _ _ _ c d HJ KM HK ltac:(lia) _ _ _ _).
         ++ unfold ka_q. rewrite CQ, andb_false_r. reflexivity.
         ++ rewrite N21. apply kq_den.
            rewrite (kq_U_seqz _ 21 (p + Z.of_nat c) 33 (nth (d - 1) L 0) 32 (nth c L 0)
              (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33)
              (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
            rewrite CQ. lia.
         ++ rewrite N23. apply kq_den. refine (U_atom _ 23 _ (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) _). lia.
         ++ rewrite N24. apply kq_den. refine (U_atom _ 22 _ (kq_ag_ew _ _ 22 _ HAE ltac:(lia) E22) _). lia.
    * (* v[0] <> '\'' *)
      pose proof (kq_br_eq_lit _ 32 (nth c L 0) 39 false (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
        ltac:(lia) ltac:(lia) Hc) as C39. clear Hc.
      paj_run_tok RUN HS HJ SHOK Bspan. { kq_awr. }
      kq_after E0 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* v[0] is not the double quote either: nothing goes *)
         pose proof (kq_br_ne_lit _ 32 (nth c L 0) 34 true (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
           ltac:(lia) ltac:(lia) Hc) as C34. apply negb_true_iff in C34. clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
         kq_after E0 HAE KM.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE)
           ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
         pmkst HS.
         refine (CM _ _ _ c d HJ KM HK ltac:(lia) _ _ _ _).
         ++ unfold ka_q. rewrite C34, C39. cbn [orb]. rewrite andb_false_r. reflexivity.
         ++ rewrite N21. apply kq_den. refine (U_atom _ 21 _ (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) _). lia.
         ++ rewrite N23. apply kq_den. refine (U_atom _ 23 _ (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) _). lia.
         ++ rewrite N24. apply kq_den. refine (U_atom _ 22 _ (kq_ag_ew _ _ 22 _ HAE ltac:(lia) E22) _). lia.
      -- (* v[0] is the double quote *)
         pose proof (kq_br_ne_lit _ 32 (nth c L 0) 34 false (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
           ltac:(lia) ltac:(lia) Hc) as C34. apply negb_false_iff in C34. clear Hc.
         paj_run_tok RUN HS HJ SHOK Bspan.
         { unfold j4_Bx.
           rewrite (U_atom _ 18 SB (kq_ag_ew _ _ 18 _ HAE ltac:(lia) E18) ltac:(unfold SB; lia)).
           rewrite (U_atom_off _ 23 _ (-1) (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) ltac:(lia) ltac:(lia)).
           rewrite SB_SHADOW_OFF.
           lazymatch goal with |- range_addressable (YCbn.rd_of SEGS (mrestrict (w_H Wc) ?mm)) _ _ _ =>
             change (YCbn.rd_of SEGS (mrestrict (w_H Wc) mm)) with (aview SEGS (w_H Wc) mm) end.
           rewrite (ka_rd_ext (w_H Wc) memc _ KM).
           refine (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) _ 1 HRA _ _); lia. }
         { kq_awr. }
         kq_after E0 HAE KM.
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ pose proof (kq_br_eq_at _ 33 (nth (d - 1) L 0) 32 (nth c L 0) true
              (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33) (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
              ltac:(lia) ltac:(lia) Hc) as CQ. clear Hc.
            paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
            kq_after E0 HAE KM.
            pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE)
              ltac:(vm_compute; reflexivity)) as HK.
            cbn [ms_regs restrict] in HK.
            kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
            pmkst HS.
            refine (CM _ _ _ (S c) (d - 1)%nat HJ KM HK ltac:(lia) _ _ _ _).
            ** unfold ka_q. rewrite (proj2 (Nat.leb_le 2 (d - c)) ltac:(lia)), C34, CQ. reflexivity.
            ** rewrite N21. apply kq_den.
               rewrite (kq_U_seqz _ 21 (p + Z.of_nat c) 33 (nth (d - 1) L 0) 32 (nth c L 0)
                 (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33)
                 (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
               rewrite CQ. lia.
            ** rewrite N23. apply kq_den.
               rewrite (U_atom_off _ 23 (p + Z.of_nat d) (-1) (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23)
                 ltac:(lia) ltac:(lia)). lia.
            ** rewrite N24. apply kq_den. refine (U_atom _ 22 _ (kq_ag_ew _ _ 22 _ HAE ltac:(lia) E22) _). lia.
         ++ pose proof (kq_br_eq_at _ 33 (nth (d - 1) L 0) 32 (nth c L 0) false
              (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33) (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32)
              ltac:(lia) ltac:(lia) Hc) as CQ. clear Hc.
            paj_run_to_tok RUNTO HS HJ SHOK Bspan KA_M. { kq_awr. }
            kq_after E0 HAE KM.
            pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ J4_KEPT HS (kq_ag32 _ _ _ _ HA0 HAE)
              ltac:(vm_compute; reflexivity)) as HK.
            cbn [ms_regs restrict] in HK.
            kreg HS (21%bv : bv 5) N21. kreg HS (23%bv : bv 5) N23. kreg HS (24%bv : bv 5) N24.
            pmkst HS.
            refine (CM _ _ _ c d HJ KM HK ltac:(lia) _ _ _ _).
            ** unfold ka_q. rewrite CQ, andb_false_r. reflexivity.
            ** rewrite N21. apply kq_den.
               rewrite (kq_U_seqz _ 21 (p + Z.of_nat c) 33 (nth (d - 1) L 0) 32 (nth c L 0)
                 (kq_ag_ew _ _ 21 _ HAE ltac:(lia) E21) (kq_ag_ew _ _ 33 _ HAE ltac:(lia) E33)
                 (kq_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
               rewrite CQ. lia.
            ** rewrite N23. apply kq_den. refine (U_atom _ 23 _ (kq_ag_ew _ _ 23 _ HAE ltac:(lia) E23) _). lia.
            ** rewrite N24. apply kq_den. refine (U_atom _ 22 _ (kq_ag_ew _ _ 22 _ HAE ltac:(lia) E22) _). lia.
Qed.

End e.
End f.
End d.

Print Assumptions ka_j4.
