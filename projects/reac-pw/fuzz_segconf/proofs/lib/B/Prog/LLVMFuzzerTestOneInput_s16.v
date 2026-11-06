(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 1644 of its 1700 lines of code are new or changed and 685 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segment S06 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput, K85338 -> K854d4 (0x85338 .. 0x854d0 with the
   slow blocks 0x85460 .. 0x854d0 and 0x85584 .. 0x85594, which no run enters): the last file turn's inlined m_cross
   (fuzz_segconf.c:296-310) after m_file(m, text, NULL), with its two m_refuse calls (0x853f0, 0x85424).
   THE CODE (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s, sha256 be3c0d79cc92, lines 352-454):
   0x85338 `bnez s5` (UBSan trap branch; s5 = M & 3 = 0 is K85338's), 136(s1) := f + 1, 128(s1) := (M + 0x2000) >> 3,
   s2 := SH(M + 0x2000), the shadow test of m->n and `lw` m->n, `blez` to 0x854d4; the loop head 0x85370 (trap
   branches 0x85374 `beq s6,33` and 0x8537c `bltu ~M, 256 i`, decided in the run by the facts i <= 31, 256 i <= 7936
   and ~M >= 2 ^ 64 - 1 - ceiling), the shadow tests and loads of role_set, role, model_set of m->seg[i]; the two
   arms (m_refuse then model_set = 0; m_refuse then role_set = 0, role = 0); the latch 0x85438 (m->n's shadow test,
   m->n reloaded, i, 256 i, the two pointers advanced, `blt s6,a0`). Every instrumented check (checks 9-16 of the
   defs) vanishes in the runs by a shadow entry (the 9 236-byte block m is addressable: AR's block and shadow laws);
   every trap branch is decided in the run (no split).
   THE PROOF. Three cut statements of this file: S6_LH_stmt (the loop head 0x85370, turn i), S6_LT_stmt (the latch
   0x85438 after turn i, the model already m_cross_seg of it) and S6_R_stmt lo ed (the returns lo = 0x853f4 / 0x85428
   of the two m_refuse calls, ed the entry's edit that follows). Each is proved from the next by the symbolic runner
   (paj_run_tok, SegPaLib) from a seed state; the loop is closed by downward induction on i (i < m->n <= 32,
   s6_heads), and m_refuse is taken by its contract (lib/B/Prog/m_refuse_c.v, image B's instance, the Section
   hypothesis MRF) through PaFx.cl_callSF and srr_after_callF; the model and encoding facts are the kit's
   (LLVMFuzzerTestOneInput_s16k.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaFx SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s16k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ===================================== the symbolic states ===================================== *)
(* the loop's listing offsets: the head 0x85370, the latch 0x85438, the returns of the two m_refuse calls *)
Definition LO_S6H : Z := 0x5b0.
Definition LO_S6T : Z := 0x678.
Definition LO_S6RR : Z := 0x634.
Definition LO_S6RM : Z := 0x668.
(* the allocation ceiling's range (YM05.CEIL_MIN / CEIL_MAX) *)
Definition S6_CMIN : Z := 140735332483072.
Definition S6_CMAX : Z := 140737479966720.
(* the shadow base the checks add: atom 33, the value of 200(s1); the shadow band *)
Definition s6x : sv := SOff 33 0.
Definition s6_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* SH(m + 0x2000) as the code forms it (s2), and SH(s8 + c) (s9 and s11 after the calls) *)
Definition s6_SH2 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0x2000) (SLit 3)) (SOff 33 0).
Definition s6_shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 c) (SLit 3)) (SOff 33 0).
(* atoms: the registers (sr_atoms), 32 m, 33 the shadow base, 34 ~m, 35 m->n, 37 role of m->seg[i] *)
Definition s6_extra (m n r : Z) : list word := map (Z_to_bv 64) [m; SHADOW_OFF; lt_not m; n; 0; r].
(* the frame slots the loop reads: 192 m, 200 the shadow base, 208 ~m, 216 &m->n *)
Definition s6_frame : YP09.region := YP09.mkRegion (Some 9%nat) 192 224 0 0
  [YP09.mkChunk 192 (CVal 8 (SOff 32 0)); YP09.mkChunk 200 (CVal 8 (SOff 33 0));
   YP09.mkChunk 208 (CVal 8 (SOff 34 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0x2000))].
(* m->n *)
Definition s6_nreg : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 35 0))].
(* m->seg[i] around s8 = m + 0x20 + 256 i: role (-16), role_set (-12), model_set (0) at the head, the two values
   pinned to literals; the stored words after the calls (write windows) *)
Definition s6_segL (rsv msv : Z) : YP09.region := YP09.mkRegion (Some 24%nat) (-16) 4 0 0
  [YP09.mkChunk (-16) (CVal 4 (SOff 37 0)); YP09.mkChunk (-12) (CVal 4 (SLit rsv));
   YP09.mkChunk 0 (CVal 4 (SLit msv))].
Definition s6_segR : YP09.region := YP09.mkRegion (Some 24%nat) (-16) (-8) (-16) (-8) [].
Definition s6_segM : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 4 [].
Definition s6_atoms : list (nat * afact) :=
  [(9%nat, mkAF S6_CMIN (2 ^ 47) 5); (21%nat, mkAF 0 7936 8); (22%nat, mkAF 0 31 0); (24%nat, mkAF 4128 S6_CMAX 4);
   (32%nat, mkAF 4096 S6_CMAX 4); (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF (2 ^ 64 - 1 - S6_CMAX) (2 ^ 64 - 1 - 4096) 0); (35%nat, mkAF 1 32 0)].
Definition s6_facts : facts := mkFacts s6_atoms [] [].
Definition s6_factsL : facts := mkFacts (s6_atoms ++ [(37%nat, mkAF 0 (2 ^ 31 - 1) 0)]) [] [].
(* registers: s10 = s8 - 16, s2 = SH(m + 0x2000); at the head and the latch a3 = the shadow base; after a call
   s9 = SH(s8 - 12) and s11 = SH(s8) *)
Definition s6_srB : list sv := sr_set (sr_set sr_atoms (26%bv : bv 5) (SOff 24 (-16))) (18%bv : bv 5) s6_SH2.
Definition s6_srH : list sv := sr_set s6_srB (13%bv : bv 5) (SOff 33 0).
Definition s6_srR : list sv := sr_set (sr_set s6_srB (25%bv : bv 5) (s6_shx (-12))) (27%bv : bv 5) (s6_shx 0).
(* the shadow entries: m->n's word, and m->seg[i]'s bytes [s8 - 16, s8 + 8) *)
Definition s6_SH : list shent := [mkSHE 32 0x2000 0x2008; mkSHE 24 (-16) 8].
(* the entry K85338: the slots the stretch reads (72 m + 0x20, 80 m + 0x10, 192 .. 216) and writes (128, 136);
   s10 = (m + 0x2000) >> 3, s5 = 0; m->n in [0, 32]; the shadow entry of m->n *)
Definition s6_eframe : YP09.region := YP09.mkRegion (Some 9%nat) 72 224 128 144
  [YP09.mkChunk 72 (CVal 8 (SOff 32 0x20)); YP09.mkChunk 80 (CVal 8 (SOff 32 0x10));
   YP09.mkChunk 192 (CVal 8 (SOff 32 0)); YP09.mkChunk 200 (CVal 8 (SOff 33 0));
   YP09.mkChunk 208 (CVal 8 (SOff 34 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0x2000))].
Definition s6_factsE : facts := mkFacts
  [(9%nat, mkAF S6_CMIN (2 ^ 47) 5); (32%nat, mkAF 4096 S6_CMAX 4); (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF (2 ^ 64 - 1 - S6_CMAX) (2 ^ 64 - 1 - 4096) 0); (35%nat, mkAF 0 32 0)] [] [].
Definition s6_srE : list sv :=
  sr_set (sr_set sr_atoms (26%bv : bv 5) (SAlu ALU_SRL (SOff 32 0x2000) (SLit 3))) (21%bv : bv 5) (SLit 0).
Definition s6_SHE : list shent := [mkSHE 32 0x2000 0x2008].

(* ===================================== values ===================================== *)
Lemma s6_U_shx : forall E (n : nat) c v, ew E n = Z_to_bv 64 v -> ew E 33 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 63 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 33 0)) = shadow_addr (v + c).
Proof.
intros E n c v Hn H33 Hv Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, H33.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + c)) by lia. rewrite (zcanon_small ((v + c) / 8)) by lia.
rewrite (zcanon_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
unfold shadow_addr. rewrite zcanon_small by (unfold SHADOW_OFF; lia). lia.
Qed.
Lemma s6_blt_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. pose proof (U_range E a). pose proof (U_range E b). cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E a)) with (Sg E a). change (bv_signed (sv_denot E b)) with (Sg E b).
rewrite !S_of_U. rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); unfold M64 in *; lia).
reflexivity.
Qed.
Lemma s6_bge_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. pose proof (U_range E a). pose proof (U_range E b). cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E a)) with (Sg E a). change (bv_signed (sv_denot E b)) with (Sg E b).
rewrite !S_of_U. rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); unfold M64 in *; lia).
reflexivity.
Qed.
Lemma s6_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma s6_reg_keep : forall (regs regs0 : bvmap 5 word) (rr : bv 5) E (n : nat),
  getr regs rr = sv_denot E (SOff n 0) -> ew E n = getr regs0 rr -> getr regs rr = getr regs0 rr.
Proof. intros regs regs0 rr E n H Hn. rewrite H. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma s6_all_disj : forall E r l, (forall rg, In rg l -> extent_disjoint E r rg) -> all_disjoint E r l.
Proof.
intros E r l. induction l as [|x l IH]; intros H; [exact I|]. cbn [all_disjoint].
split; [apply H; left; reflexivity | apply IH; intros rg Hrg; apply H; right; exact Hrg].
Qed.

(* a register of a state, as the symbolic state names it *)
Ltac s6_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac s6_atom := repeat (rewrite ew_ewset_other by lia); assumption.
Ltac s6_side := first [s6_atom | unfold SHADOW_OFF in *; lia].
Ltac s6_mdv x := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
  set (x := d) in *; clearbody x end.
(* a register the run kept: EEo names every register atom of the seed's environment *)
Ltac s6_kreg HS r :=
  let P := fresh "P" in s6_prraw HS r P; apply (s6_reg_keep _ _ _ _ _ P);
  repeat (rewrite ew_ewset_other by lia); match goal with EEo : forall (n : nat) (rr : bv 5), _ |- _ => apply EEo end;
  reflexivity.
Ltac s6_vreg HS r := let P := fresh "P" in s6_prraw HS r P; apply (s6_reg_U _ _ _ _ _ P).
Ltac s6_kg HS := lazymatch goal with |- getr _ ?rr = getr _ ?rr => s6_kreg HS rr end.
(* a run whose regions are all read-only left the memory as it was *)
Ltac s6_ro HF EM :=
  lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
    pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as EM end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition s6_E (regs : bvmap 5 word) (m n r : Z) : env := Eimg (Ereg regs (s6_extra m n r)).

Lemma s6_E_facts : forall regs m n r,
  (forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew (s6_E regs m n r) k = getr regs rr) /\
  ew (s6_E regs m n r) 32 = Z_to_bv 64 m /\ ew (s6_E regs m n r) 33 = Z_to_bv 64 SHADOW_OFF /\
  ew (s6_E regs m n r) 34 = Z_to_bv 64 (lt_not m) /\ ew (s6_E regs m n r) 35 = Z_to_bv 64 n /\
  ew (s6_E regs m n r) 37 = Z_to_bv 64 r.
Proof.
intros regs m n r. unfold s6_E. split; [|split; [|split; [|split; [|split]]]].
- intros k rr Hk. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 5).
Qed.

(* the registers of the loop's seeds *)
Lemma s6_regs_okB : forall regs m n r i,
  0 <= m -> m + 9236 <= 2 ^ 47 -> (i <= 31)%nat ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  regs_ok (s6_E regs m n r) s6_srB regs.
Proof.
intros regs m n r i Hm Hm2 Hi R24 R26 R18.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & _).
assert (E24 : ew (s6_E regs m n r) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
unfold s6_srB. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |] | discriminate |].
- rewrite R26. rewrite denot_lit_U. f_equal. rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) (-16) E24) by lia. lia.
- rewrite R18. rewrite denot_lit_U. f_equal. symmetry. unfold s6_SH2.
  rewrite (s6_U_shx _ 32 0x2000 m E32 E33) by lia. reflexivity.
Qed.
Lemma s6_regs_okH : forall regs m n r i,
  0 <= m -> m + 9236 <= 2 ^ 47 -> (i <= 31)%nat ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 13 = w64 SHADOW_OFF ->
  regs_ok (s6_E regs m n r) s6_srH regs.
Proof.
intros regs m n r i Hm Hm2 Hi R24 R26 R18 R13.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & _).
unfold s6_srH. apply regs_ok_pin; [exact (s6_regs_okB regs m n r i Hm Hm2 Hi R24 R26 R18) | discriminate |].
rewrite R13. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma s6_regs_okR : forall regs m n r i,
  0 <= m -> m + 9236 <= 2 ^ 47 -> (i <= 31)%nat ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs 25 = w64 (shadow_addr (m + 20 + 256 * Z.of_nat i)) ->
  getr regs 27 = w64 (shadow_addr (m + 32 + 256 * Z.of_nat i)) ->
  regs_ok (s6_E regs m n r) s6_srR regs.
Proof.
intros regs m n r i Hm Hm2 Hi R24 R26 R18 R25 R27.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & _).
assert (E24 : ew (s6_E regs m n r) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
unfold s6_srR. apply regs_ok_pin; [apply regs_ok_pin; [exact (s6_regs_okB regs m n r i Hm Hm2 Hi R24 R26 R18) | discriminate |]
  | discriminate |].
- rewrite R25. rewrite denot_lit_U. f_equal. symmetry. unfold s6_shx.
  rewrite (s6_U_shx _ 24 (-12) _ E24 E33) by lia. f_equal. lia.
- rewrite R27. rewrite denot_lit_U. f_equal. symmetry. unfold s6_shx.
  rewrite (s6_U_shx _ 24 0 _ E24 E33) by lia. f_equal. lia.
Qed.

(* the facts of the loop's seeds *)
Lemma s6_facts_ok : forall regs m n r i s1,
  getr regs 9 = w64 s1 -> S6_CMIN <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  getr regs 21 = w64 (256 * Z.of_nat i) -> getr regs 22 = w64 (Z.of_nat i) ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> (i <= 31)%nat ->
  4096 <= m -> m + 9236 <= S6_CMAX -> m mod 16 = 0 -> 1 <= n <= 32 ->
  facts_ok (s6_E regs m n r) s6_facts.
Proof.
intros regs m n r i s1 R9 Hs1 Hs1m R21 R22 R24 Hi Hm1 Hm2 Hm16 Hn.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & E34 & E35 & _).
split; [|split; [exact I | exact I]].
cbn [s6_facts s6_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (EEo 9%nat 9%bv eq_refl), (EEo 21%nat 21%bv eq_refl), (EEo 22%nat 22%bv eq_refl), (EEo 24%nat 24%bv eq_refl).
rewrite R9, R21, R22, R24, E32, E33, E34, E35. unfold w64, lt_not, S6_CMIN, S6_CMAX in *.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
assert (M1 : (m + 32 + 256 * Z.of_nat i) mod 2 ^ 4 = 0).
{ change (2 ^ 4) with 16. rewrite <- Z.add_assoc, Z.add_mod, Hm16 by lia.
  replace (32 + 256 * Z.of_nat i) with ((2 + 16 * Z.of_nat i) * 16) by lia. rewrite Z.mod_mul by lia. reflexivity. }
assert (M2 : (256 * Z.of_nat i) mod 2 ^ 8 = 0).
{ change (2 ^ 8) with 256. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
assert (M3 : m mod 2 ^ 4 = 0) by exact Hm16.
assert (M4 : s1 mod 2 ^ 5 = 0) by exact Hs1m.
rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | unfold SHADOW_OFF; lia].
Qed.
Lemma s6_facts_okL : forall regs m n r i s1,
  getr regs 9 = w64 s1 -> S6_CMIN <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  getr regs 21 = w64 (256 * Z.of_nat i) -> getr regs 22 = w64 (Z.of_nat i) ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> (i <= 31)%nat ->
  4096 <= m -> m + 9236 <= S6_CMAX -> m mod 16 = 0 -> 1 <= n <= 32 -> 0 <= r < 2 ^ 31 ->
  facts_ok (s6_E regs m n r) s6_factsL.
Proof.
intros regs m n r i s1 R9 Hs1 Hs1m R21 R22 R24 Hi Hm1 Hm2 Hm16 Hn Hr.
destruct (s6_facts_ok regs m n r i s1 R9 Hs1 Hs1m R21 R22 R24 Hi Hm1 Hm2 Hm16 Hn) as (HA & _).
destruct (s6_E_facts regs m n r) as (_ & _ & _ & _ & _ & E37).
split; [|split; [exact I | exact I]]. cbn [s6_factsL f_atoms].
cbn [s6_facts f_atoms] in HA. revert HA. unfold s6_atoms. cbn [app atoms_ok]. intros HA.
repeat match type of HA with _ /\ _ => let Ha := fresh "Ha" in destruct HA as [Ha HA] end.
repeat (split; [assumption|]). split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E37, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the seed of the loop's states: the frame slots and m->n, with seg_r the regions of m->seg[i] *)
Lemma s6_seed : forall (pc : Z) (sr : list sv) (G : facts) (segr : list YP09.region) (W : world SEGS) regs mem
  (s1 m n r : Z),
  regs_ok (s6_E regs m n r) sr regs -> facts_ok (s6_E regs m n r) G ->
  regions_wf segr = true ->
  Forall (YP09.region_ok SEGS (s6_E regs m n r) (mrestrict (w_H W) mem)) segr ->
  (forall rg, In rg segr -> extent_disjoint (s6_E regs m n r) s6_frame rg /\ extent_disjoint (s6_E regs m n r) s6_nreg rg) ->
  pairwise_disjoint (s6_E regs m n r) segr ->
  getr regs 9 = w64 s1 -> 0 <= m -> m + 0x2004 <= s1 + 192 -> s1 + 224 <= 2 ^ 64 -> 0 <= n < 2 ^ 32 ->
  rdword (rdW W mem) (s1 + 192) = Some m -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 208) = Some (lt_not m) -> rdword (rdW W mem) (s1 + 216) = Some (m + seg_spec.MC_N) ->
  rd32 (rdW W mem) (m + seg_spec.MC_N) n ->
  st_ok_pi SEGS VAL (s6_E regs m n r) (mkSS pc sr (s6_frame :: s6_nreg :: segr) None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc sr G segr W regs mem s1 m n r HR HG Hwf HRS HD HPD R9 Hm Hm2 Hs1 Hn S192 S200 S208 S216 HN.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & E34 & E35 & _).
remember (s6_E regs m n r) as E eqn:HE.
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
assert (U32 : bv_unsigned (ew E 32) = m) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [exact HR | | | | exact HG].
- cbn [regions_wf]. rewrite Hwf. vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|exact HRS]]; unfold YP09.region_ok, s6_frame, s6_nreg;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 192 8 (SOff 32 0) m); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S192).
    * apply (chunk_ok_val SEGS E _ s1 200 8 (SOff 33 0) SHADOW_OFF); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold SHADOW_OFF; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S200).
    * apply (chunk_ok_val SEGS E _ s1 208 8 (SOff 34 0) (lt_not m)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold lt_not; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S208).
    * apply (chunk_ok_val SEGS E _ s1 216 8 (SOff 32 0x2000) (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E32; unfold seg_spec.MC_N; rewrite unsigned_lit_small by lia; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold seg_spec.MC_N; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S216).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ m 0x2000 4 (SOff 35 0) n); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | lia |].
    exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ HN).
- cbn [pairwise_disjoint all_disjoint]. split; [split|split; [|exact HPD]].
  + unfold extent_disjoint, s6_frame, s6_nreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32. lia.
  + apply s6_all_disj. intros rg Hrg. exact (proj1 (HD rg Hrg)).
  + apply s6_all_disj. intros rg Hrg. exact (proj2 (HD rg Hrg)).
Qed.
(* the entry's registers, facts and seed *)
Lemma s6_regs_okE : forall regs m n r, 0 <= m -> m + 9236 <= 2 ^ 47 ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) -> getr regs 21 = w64 0 -> regs_ok (s6_E regs m n r) s6_srE regs.
Proof.
intros regs m n r Hm Hm2 R26 R21.
destruct (s6_E_facts regs m n r) as (EEo & E32 & _).
unfold s6_srE. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |] | discriminate |].
- rewrite R26. rewrite denot_lit_U. f_equal. symmetry.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, E32, unsigned_lit_small by lia.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_pos (m + 0x2000) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (m + 0x2000) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
  rewrite (zcanon_small (m + 8192)) by lia. rewrite zcanon_small by lia. unfold seg_spec.MC_N. reflexivity.
- rewrite R21. reflexivity.
Qed.
Lemma s6_facts_okE : forall regs m n r s1,
  getr regs 9 = w64 s1 -> S6_CMIN <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= m -> m + 9236 <= S6_CMAX -> m mod 16 = 0 -> 0 <= n <= 32 ->
  facts_ok (s6_E regs m n r) s6_factsE.
Proof.
intros regs m n r s1 R9 Hs1 Hs1m Hm1 Hm2 Hm16 Hn.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & E34 & E35 & _).
split; [|split; [exact I | exact I]].
cbn [s6_factsE f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (EEo 9%nat 9%bv eq_refl). rewrite R9, E32, E33, E34, E35. unfold w64, lt_not, S6_CMIN, S6_CMAX in *.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
assert (M3 : m mod 2 ^ 4 = 0) by exact Hm16.
assert (M4 : s1 mod 2 ^ 5 = 0) by exact Hs1m.
rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | unfold SHADOW_OFF; lia].
Qed.
Lemma s6_eseed : forall (W : world SEGS) regs mem (s1 m n : Z),
  regs_ok (s6_E regs m n 0) s6_srE regs -> facts_ok (s6_E regs m n 0) s6_factsE ->
  getr regs 9 = w64 s1 -> 0 <= m -> m + 0x2004 <= s1 + 72 -> s1 + 224 <= 2 ^ 64 -> 0 <= n < 2 ^ 32 ->
  (forall a, s1 + 128 <= a < s1 + 144 -> apresent (w_H W) mem a) ->
  rdword (rdW W mem) (s1 + 72) = Some (m + 0x20) -> rdword (rdW W mem) (s1 + 80) = Some (m + 0x10) ->
  rdword (rdW W mem) (s1 + 192) = Some m -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 208) = Some (lt_not m) -> rdword (rdW W mem) (s1 + 216) = Some (m + seg_spec.MC_N) ->
  rd32 (rdW W mem) (m + seg_spec.MC_N) n ->
  st_ok_pi SEGS VAL (s6_E regs m n 0) (mkSS LO_K85338 s6_srE [s6_eframe; s6_nreg] None s6_factsE)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85338)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m n HR HG R9 Hm Hm2 Hs1 Hn HP S72 S80 S192 S200 S208 S216 HN.
destruct (s6_E_facts regs m n 0) as (EEo & E32 & E33 & E34 & E35 & _).
remember (s6_E regs m n 0) as E eqn:HE.
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
assert (U32 : bv_unsigned (ew E 32) = m) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [exact HR | | | | exact HG].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold YP09.region_ok, s6_eframe, s6_nreg;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HP; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 72 8 (SOff 32 0x20) (m + 0x20));
        [cbn [sv_denot]; rewrite E32; rewrite unsigned_lit_small by lia; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S72).
    * apply (chunk_ok_val SEGS E _ s1 80 8 (SOff 32 0x10) (m + 0x10));
        [cbn [sv_denot]; rewrite E32; rewrite unsigned_lit_small by lia; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S80).
    * apply (chunk_ok_val SEGS E _ s1 192 8 (SOff 32 0) m); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S192).
    * apply (chunk_ok_val SEGS E _ s1 200 8 (SOff 33 0) SHADOW_OFF); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold SHADOW_OFF; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S200).
    * apply (chunk_ok_val SEGS E _ s1 208 8 (SOff 34 0) (lt_not m)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold lt_not; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S208).
    * apply (chunk_ok_val SEGS E _ s1 216 8 (SOff 32 0x2000) (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E32; unfold seg_spec.MC_N; rewrite unsigned_lit_small by lia; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold seg_spec.MC_N; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ S216).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ m 0x2000 4 (SOff 35 0) n); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | lia |].
    exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ HN).
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I]|split; [exact I | exact I]].
  unfold extent_disjoint, s6_eframe, s6_nreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the shadow entries of the loop's seeds *)
Lemma s6_shok : forall ly S (W : world SEGS) mem md regs m n r i,
  AR SEGS B ly S W mem md -> In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) -> (i <= 31)%nat ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) ->
  sh_ok SEGS s6x s6_SH (s6_E regs m n r) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs m n r i HAR Hin Hi R24.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hin) as (_ & Hm4096 & Hceil & Happ & _).
pose proof asan_consts as (C1 & _). unfold seg_spec.SEG_M_SIZE, req_size in *. cbn in Hceil, Happ.
assert (E24 : ew (s6_E regs m n r) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
unfold sh_ok, s6_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) mem _ s6x 32 m 9236 m 0x2000 0x2008).
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md m 9236); [exact HAR | exact Hin | lia | unfold req_size; cbn; lia].
  + unfold s6x. rewrite (U_atom _ 33 SHADOW_OFF E33) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite (U_atom _ 32 m E32) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem _ s6x 24 m 9236 (m + 32 + 256 * Z.of_nat i) (-16) 8).
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md m 9236); [exact HAR | exact Hin | lia | unfold req_size; cbn; lia].
  + unfold s6x. rewrite (U_atom _ 33 SHADOW_OFF E33) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite (U_atom _ 24 (m + 32 + 256 * Z.of_nat i) E24) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
Lemma s6_shokE : forall ly S (W : world SEGS) mem md regs m n r,
  AR SEGS B ly S W mem md -> In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) ->
  sh_ok SEGS s6x s6_SHE (s6_E regs m n r) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs m n r HAR Hin.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hin) as (_ & Hm4096 & Hceil & Happ & _).
pose proof asan_consts as (C1 & _). unfold seg_spec.SEG_M_SIZE, req_size in *. cbn in Hceil, Happ.
unfold sh_ok, s6_SHE. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem _ s6x 32 m 9236 m 0x2000 0x2008).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md m 9236); [exact HAR | exact Hin | lia | unfold req_size; cbn; lia].
- unfold s6x. rewrite (U_atom _ 33 SHADOW_OFF E33) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite (U_atom _ 32 m E32) by lia. reflexivity.
- lia.
- lia.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* ===================================== the loop's statements ===================================== *)
(* K854d4's slots (K85338's and 128 / 136, stored at 0x85344 / 0x8533c) *)
Definition s6_slots (cx : lcx) (c m : Z) (f : nat) : list (Z * Z) :=
  LT_L cx c m ++
    [(128, (m + seg_spec.MC_N) / 8); (136, Z.of_nat f + 1); (144, x_at cx f + x_np cx f); (152, x_np cx f);
     (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))].
(* what every point of the loop states but the registers of the turn and the model *)
Definition s6_lp (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (c m t : Z) (f : nat)
  : Prop :=
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) /\
  getr regs 23 = w64 t /\
  lt_slots cx (rdW W mem) (s6_slots cx c m f) /\
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) /\
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) /\
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f)) (s6_M0 (x_pl cx) f).
(* s6_lp but the slots *)
Definition s6_lp0 (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (c m t : Z) (f : nat)
  : Prop :=
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) /\
  getr regs 23 = w64 t /\
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) /\
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) /\
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f)) (s6_M0 (x_pl cx) f).
Lemma s6_lp0_of : forall cx ly S W regs mem md k acc c m t f,
  s6_lp cx ly S W regs mem md k acc c m t f -> s6_lp0 cx ly S W regs mem md k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f (A1 & A2 & A3 & A4 & A5 & _ & A7 & A8 & A9).
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A7 (conj A8 A9))))))).
Qed.
Lemma s6_lp_of0 : forall cx ly S W regs mem md k acc c m t f,
  s6_lp0 cx ly S W regs mem md k acc c m t f -> lt_slots cx (rdW W mem) (s6_slots cx c m f) ->
  s6_lp cx ly S W regs mem md k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f (A1 & A2 & A3 & A4 & A5 & A7 & A8 & A9) A6.
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 A9)))))))).
Qed.
(* the loop's head 0x85370, turn i < m->n: s5 = 256 i, s6 = i, s8 = m + 0x20 + 256 i, s10 = m + 0x10 + 256 i,
   s2 = SH(m + 0x2000), a3 = the shadow base; m holds the table after i passes *)
Definition S6_LH_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  s6_lp cx ly S W regs mem md k acc c m t f ->
  (i < length (SegModel.mc_seg (s6_M0 (x_pl cx) f)))%nat ->
  getr regs 13 = w64 SHADOW_OFF -> getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs 21 = w64 (256 * Z.of_nat i) -> getr regs 22 = w64 (Z.of_nat i) ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  sa_mconf (rdW W mem) m (s6_MI (x_pl cx) f i) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S6H) regs mem md) (lt_post B MT cx).
(* the latch 0x85438 after turn i: the registers of turn i, m holds the table after i + 1 passes *)
Definition S6_LT_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  s6_lp cx ly S W regs mem md k acc c m t f ->
  (i < length (SegModel.mc_seg (s6_M0 (x_pl cx) f)))%nat ->
  getr regs 13 = w64 SHADOW_OFF -> getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs 21 = w64 (256 * Z.of_nat i) -> getr regs 22 = w64 (Z.of_nat i) ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  sa_mconf (rdW W mem) m (s6_MI (x_pl cx) f (Datatypes.S i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S6T) regs mem md) (lt_post B MT cx).
(* the two returns of m_refuse(m, 0) inside turn i: s9 = SH(m + 0x14 + 256 i), s11 = SH(m + 0x20 + 256 i); m holds
   m_refuse's table, and the turn is the one whose edit follows (role = role_set = 0 at 0x853f4, from the call at
   0x853f0; model_set = 0 at 0x85428, from the call at 0x85424) *)
Definition s6_rp (cx : lcx) ly S W regs mem md k acc (c m t : Z) (f i : nat) : Prop :=
  lt_base B MT cx /\ sa_frm0 /\ Z.of_nat f + 1 = x_nf cx /\
  s6_lp cx ly S W regs mem md k acc c m t f /\
  (i < length (SegModel.mc_seg (s6_M0 (x_pl cx) f)))%nat /\
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) /\
  getr regs 21 = w64 (256 * Z.of_nat i) /\ getr regs 22 = w64 (Z.of_nat i) /\
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) /\ getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) /\
  getr regs 25 = w64 (shadow_addr (m + 20 + 256 * Z.of_nat i)) /\
  getr regs 27 = w64 (shadow_addr (m + 32 + 256 * Z.of_nat i)) /\
  sa_mconf (rdW W mem) m (SegModel.m_refuse (s6_MI (x_pl cx) f i) 0 false).
(* the return of m_refuse at lo (LO_S6RR, edit ms_drop_role / LO_S6RM, edit ms_drop_model) *)
Definition S6_R_stmt (lo : Z) (ed : SegModel.mseg -> SegModel.mseg) (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  s6_rp cx ly S W regs mem md k acc c m t f i ->
  SegModel.m_cross_seg (s6_MI (x_pl cx) f i) i =
    SegModel.m_upd (SegModel.m_refuse (s6_MI (x_pl cx) f i) 0 false) i ed ->
  SRr SEGS W (cfg_at SEGS (BASE + lo) regs mem md) (lt_post B MT cx).
End e.
End f.
End d.

Section lta. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Definition S6_LHA (B : asyms) (MT : ameter_ops) (f i : nat) : Prop := forall fx1 : YK11.FPState, S6_LH_stmt (fx := fx1) B MT f i.
Definition S6_LTA (B : asyms) (MT : ameter_ops) (f i : nat) : Prop := forall fx1 : YK11.FPState, S6_LT_stmt (fx := fx1) B MT f i.
Definition S6_RA (B : asyms) (MT : ameter_ops) lo ed (f i : nat) : Prop :=
  forall fx1 : YK11.FPState, S6_R_stmt (fx := fx1) B MT lo ed f i.
End lta.

Section dp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fp.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ep.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the numbers a loop point gives *)
Lemma s6_nums0 : forall cx ly S W regs mem md k acc c m t f,
  lt_base B MT cx -> s6_lp0 B MT cx ly S W regs mem md k acc c m t f ->
  AR SEGS B ly S W mem md /\ In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) /\
  4096 <= m /\ m + 9236 <= alloc_ceiling /\ m mod 16 = 0 /\
  getr regs 9 = w64 (x_s1 cx) /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_sp0 cx - 383 <= x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0.
Proof.
intros cx ly S W regs mem md k acc c m t f HB HLP.
destruct HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _).
destruct HLP as ((HFR & _) & _ & (Hmin & Hm4 & Hm16 & _) & _).
destruct HFR as (HJ & _ & _ & _ & _ & R9 & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok SEGS B) ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as (_ & _ & Hceil & _).
unfold seg_spec.SEG_M_SIZE, req_size in Hceil. cbn in Hceil.
assert (HST : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HST in Hslo0.
unfold x_s1, x_sp0, LT_FRAME in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 352) 32 ltac:(lia)) as M32.
assert (Ms : (spZ (x_regs cx) - 352 - (spZ (x_regs cx) - 352) mod 32) mod 32 = 0).
{ rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
split; [exact HAR|]. split; [exact Hmin|]. split; [exact Hm4|]. split; [exact Hceil|]. split; [exact Hm16|].
split; [exact R9|]. split; [lia|]. split; [exact Hal0|]. split; [lia|]. exact Ms.
Qed.
Lemma s6_nums : forall cx ly S W regs mem md k acc c m t f,
  lt_base B MT cx -> s6_lp B MT cx ly S W regs mem md k acc c m t f ->
  AR SEGS B ly S W mem md /\ In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) /\
  4096 <= m /\ m + 9236 <= alloc_ceiling /\ m mod 16 = 0 /\
  getr regs 9 = w64 (x_s1 cx) /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_sp0 cx - 383 <= x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0.
Proof.
intros cx ly S W regs mem md k acc c m t f HB HLP.
exact (s6_nums0 cx ly S W regs mem md k acc c m t f HB (s6_lp0_of B MT _ _ _ _ _ _ _ _ _ _ _ _ _ HLP)).
Qed.

(* a loop point's facts at a later state of the same allocator state and memory: the journal and six registers *)
Lemma s6_lp_move : forall cx ly S W regs mem md k acc c m t f (regs' : bvmap 5 word) md',
  s6_lp B MT cx ly S W regs mem md k acc c m t f ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 23 = getr regs 23 ->
  s6_lp B MT cx ly S W regs' mem md' k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f regs' md' HLP HJ' P2 P3 P4 P8 P9 P23.
destruct HLP as ((HF & HI & HBl & HBu) & H1 & H2 & H3 & R23 & Hsl & Hrc & Hst & Hcnt).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & Hrest).
split; [|split; [exact H1|split; [exact H2|split; [exact H3|split; [rewrite P23; exact R23|]]]]].
- split; [|split; [exact HI|split; [exact HBl|exact HBu]]].
  split; [exact HJ'|]. rewrite P2, P3, P4, P8, P9. exact (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 Hrest))))).
- exact (conj Hsl (conj Hrc (conj Hst Hcnt))).
Qed.

(* the counters after m_cross: the model's own bound before it, one refusal a segment *)
Lemma s6_cnt_cross : forall f rc0 mc0, lt_cnt (Datatypes.S f) rc0 mc0 ->
  SegModel.mc_refused mc0 <= Z.of_nat (Datatypes.S f) * 65535 -> (length (SegModel.mc_seg mc0) <= 32)%nat ->
  lt_cnt (Datatypes.S f) rc0 (SegModel.m_cross mc0).
Proof.
intros f rc0 mc0 (H1 & H2 & H3 & H4 & H5 & H6) HR HL.
rewrite s6_all. destruct (s6_cnt mc0 (length (SegModel.mc_seg mc0))) as (G & O & R).
unfold lt_cnt. rewrite G, O. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* the slots of a loop point *)
Lemma s6_slot : forall cx rd c m f o v, lt_slots cx rd (s6_slots cx c m f) -> In (o, v) (s6_slots cx c m f) ->
  rdword rd (x_s1 cx + o) = Some v.
Proof. intros cx rd c m f o v H Hin. exact (H o v Hin). Qed.
Ltac s6_in := unfold s6_slots, LT_L; cbn [app In]; repeat (first [left; reflexivity | right]).

(* ---- the latch 0x85438 .. 0x85458: check 16 (m->n's word, its shadow entry), m->n, i + 1, 256 (i + 1), the
   two pointers + 256, then blt s6, a0: to the head of turn i + 1 or, i + 1 = m->n, out of the loop by the j at
   0x8545c to K854d4 ---- *)
Lemma s6_latch : forall f i, S6_LHA B MT f (Datatypes.S i) -> LTA_K854d4 B MT f -> S6_LT_stmt B MT f i.
Proof.
intros f i HLH HX cx ly S W regs mem md k acc c m t HB HFRM Hnf HLP Hi R13 R18 R21 R22 R24 R26 HMC.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof HLP as ((HFR & _) & _ & _ & _ & R23 & Hsl & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & _ & _ & _ & _ & _ & _ & S200 & _).
set (M0 := s6_M0 (x_pl cx) f) in *.
set (n := Z.of_nat (length (SegModel.mc_seg M0))).
pose proof (s6_mconf_len _ _ _ HMC) as HL32. unfold s6_MI in HL32. rewrite s6_len in HL32. fold M0 in HL32.
assert (Hi31 : (i <= 31)%nat) by lia.
assert (Hn : 1 <= n <= 32) by (unfold n; lia).
pose proof (s6_rd_n _ _ _ HMC) as HN. unfold s6_MI in HN. rewrite s6_len in HN. fold M0 n in HN.
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
unfold S6_CMIN, S6_CMAX in *.
pose proof (s6_seed LO_S6T s6_srH s6_facts [] W regs mem (x_s1 cx) m n 0
  (s6_regs_okH regs m n 0 i ltac:(lia) ltac:(lia) Hi31 R24 R26 R18 R13)
  (s6_facts_ok regs m n 0 i (x_s1 cx) R9 ltac:(unfold S6_CMIN; lia) Hs1m R21 R22 R24 Hi31 Hm4 ltac:(unfold S6_CMAX; lia) Hm16 Hn)
  eq_refl (Forall_nil _) (fun rg H => match H with end) I R9 ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) ltac:(lia)
  ltac:(lia) S192 S200 S208 S216 HN) as HS.
pose proof (s6_shok B ly S W mem md regs m n 0 i HAR Hmin Hi31 R24) as SHOK.
destruct (s6_E_facts regs m n 0) as (EEo & E32 & E33 & E34 & E35 & _).
assert (HEI : img_env VAL A_LIM (s6_E regs m n 0)) by (unfold s6_E; apply Eimg_env).
remember (s6_E regs m n 0) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = Z_to_bv 64 (256 * Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
unfold cfg_at.
(* 0x85438 .. 0x85458: the shadow of m->n (its check vanishes), m->n, the increments; then blt s6, a0 *)
paj_run_tok RUN HS HJ SHOK s6_span.
{ awr_ok_tac. }
s6_mdv mdv1.
s6_ro HF EM. clear HF HFr HG.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s6_span.
- (* i + 1 < m->n: back to the head, turn i + 1 *)
  assert (U22 : U E (SOff 22 1) = Z.of_nat i + 1) by (rewrite (U_atom_off _ 22 (Z.of_nat i) 1) by s6_side; reflexivity).
  assert (U35 : U E (SOff 35 0) = n) by (rewrite (U_atom _ 35 n) by s6_side; reflexivity).
  rewrite s6_blt_U, U22, U35 in Hc by (rewrite ?U22, ?U35; lia). apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6H.
  { awr_ok_tac. }
  s6_mdv mdv.
  s6_ro HF EM2. clear HF HFr HG.
  pmkst HS. rewrite EM2, EM in *.
  refine (HLH fx cx ly S W (ms_regs ms) mem mdv k acc c m t HB HFRM Hnf _ _ _ _ _ _ _ _ _).
  + apply (s6_lp_move cx ly S W regs mem md k acc c m t f (ms_regs ms) mdv HLP HJ); s6_kg HS.
  + unfold n, M0 in *. lia.
  + s6_vreg HS (13%bv : bv 5). rewrite (U_atom _ 33 SHADOW_OFF) by s6_side. reflexivity.
  + s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
  + s6_vreg HS (21%bv : bv 5). rewrite (U_atom_off _ 21 (256 * Z.of_nat i) 256) by s6_side. lia.
  + s6_vreg HS (22%bv : bv 5). rewrite (U_atom_off _ 22 (Z.of_nat i) 1) by s6_side. lia.
  + s6_vreg HS (24%bv : bv 5). rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) 256) by s6_side. lia.
  + s6_vreg HS (26%bv : bv 5). rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) 240) by s6_side. lia.
  + exact HMC.
- (* i + 1 = m->n: out of the loop, m holds m_cross of m_file's table *)
  assert (U22 : U E (SOff 22 1) = Z.of_nat i + 1) by (rewrite (U_atom_off _ 22 (Z.of_nat i) 1) by s6_side; reflexivity).
  assert (U35 : U E (SOff 35 0) = n) by (rewrite (U_atom _ 35 n) by s6_side; reflexivity).
  rewrite s6_blt_U, U22, U35 in Hc by (rewrite ?U22, ?U35; lia). apply Z.ltb_ge in Hc.
  assert (HSI : Datatypes.S i = length (SegModel.mc_seg M0)) by (unfold n in Hc; lia).
  paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_K854d4.
  { awr_ok_tac. }
  s6_mdv mdv.
  s6_ro HF EM2. clear HF HFr HG.
  pmkst HS. rewrite EM2, EM in *.
  assert (HLP2 : s6_lp B MT cx ly S W (ms_regs ms) mem mdv k acc c m t f)
    by (apply (s6_lp_move cx ly S W regs mem md k acc c m t f (ms_regs ms) mdv HLP HJ); s6_kg HS).
  destruct HLP2 as (HC2 & Hc2 & Hm2 & Ht2 & R23' & Hsl2 & Hrc2 & Hst2 & Hcnt2).
  refine (HX fx cx ly S W (ms_regs ms) mem mdv k acc c m t HB HFRM Hnf HC2 Hc2 Hm2 Ht2 _ R23' Hsl2 Hrc2 _ Hst2 _).
  + s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
  + change (sa_mconf (rdW W mem) m (SegModel.m_cross (s6_M0 (x_pl cx) f))).
    unfold M0 in HSI. rewrite s6_all, <- HSI. exact HMC.
  + apply s6_cnt_cross; [exact Hcnt2 | exact (proj2 (s6_M0_refused (x_pl cx) f)) | exact HL32].
Qed.

(* ===================================== facts kept outside the m block ===================================== *)
Lemma s6_pw_perm : forall {X} (R : X -> X -> Prop) l l', (forall x y, R x y -> R y x) ->
  pairwise R l -> Permutation l l' -> pairwise R l'.
Proof.
intros X R l l' Hs Hp HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2].
- exact I.
- destruct Hp as [Hf Hp]. split; [|exact (IH Hp)].
  apply Forall_forall. intros z Hz. rewrite Forall_forall in Hf. apply Hf.
  exact (Permutation_in z (Permutation_sym HP) Hz).
- destruct Hp as [Hfy [Hfx Hp]]. inversion Hfy as [|? ? Hyx Hfy']; subst.
  split; [constructor; [exact (Hs _ _ Hyx) | exact Hfx]|]. split; [exact Hfy' | exact Hp].
- exact (IH2 (IH1 Hp)).
Qed.
Lemma s6_pw_app : forall {X} (R : X -> X -> Prop) l1 l2 x y, pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|a l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as [Hf Hp]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
(* the three harness blocks: m is none of the entry's blocks and lies apart from c and t *)
Lemma s6_blk_sep : forall ly S (W : world SEGS) mem md bl0 t nt m c,
  AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) ([(t, nt); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ++ bl0) -> 0 <= nt ->
  (m + seg_spec.SEG_M_SIZE <= c \/ c + seg_spec.SEG_C_SIZE <= m) /\ (m + seg_spec.SEG_M_SIZE <= t \/ t + nt <= m) /\
  ~ In (m, seg_spec.SEG_M_SIZE) bl0.
Proof.
intros ly S W mem md bl0 t nt m c HAR HP Hnt.
assert (Hin : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
pose proof (s6_pw_perm zdisjoint _ _ ltac:(intros x y [H|H]; [right|left]; exact H) Hpw
  (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b))) HP)) as Hpw2.
cbn [map app pairwise fst snd] in Hpw2.
destruct Hpw2 as [Ht [Hm _]].
inversion Ht as [|? ? Htm Ht']; subst. inversion Hm as [|? ? Hmc Hm']; subst.
pose proof (req_size_pos nt Hnt) as [_ Hreq].
assert (RM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (RC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity.
unfold zdisjoint in Htm, Hmc. cbn [fst snd] in Htm, Hmc. rewrite RM in Htm, Hmc. rewrite RC in Hmc.
unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE. split; [lia|]. split; [lia|].
intros Hb. rewrite Forall_forall in Hm'.
assert (Hx : In (m, req_size seg_spec.SEG_M_SIZE) (map (fun b : Z * Z => (fst b, req_size (snd b))) bl0))
  by (apply in_map_iff; exists (m, seg_spec.SEG_M_SIZE); split; [reflexivity | exact Hb]).
specialize (Hm' _ Hx). unfold zdisjoint in Hm'. cbn [fst snd] in Hm'. rewrite RM in Hm'. lia.
Qed.

(* an image byte (at or above 0x10000, below the image's end) of a state is the same byte of the next state *)
Definition s6_imgk (rd rd' : reader) : Prop := forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a.
Lemma s6_img_rng : forall q n x, sa_img SEGS B q n -> q <= x < q + n -> 0x10000 <= x < kImgEnd.
Proof. intros q n x H Hx. destruct (H x Hx) as (Hi & _). exact (pa_img_range x Hi). Qed.
Lemma s6_rdword_k : forall (rd rd' : reader) a, s6_imgk rd rd' -> 0x10000 <= a -> a + 8 <= kImgEnd ->
  rdword rd' a = rdword rd a.
Proof. intros rd rd' a Hk H1 H2. apply rdword_ext. intros j Hj. apply Hk. lia. Qed.
Lemma s6_lit_k : forall H mem H' mem' a s, s6_imgk (aview SEGS H mem) (aview SEGS H' mem') ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H' mem') a s.
Proof.
intros H mem H' mem' a s Hk (Ha & ((Hzs & Hn0) & Htl) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrt | exact Himg]]].
split; [split; [|exact Hn0]|].
- intros i Hi. rewrite Hk; [apply Hzs; exact Hi|]. apply (s6_img_rng a (Z.of_nat (length s) + 1)); [exact Himg|].
  rewrite length_app in Hi. cbn [length] in Hi. lia.
- apply sa_tail_of_romtail. exact Hrt.
Qed.
Lemma s6_img_k : forall cx H mem H' mem', s6_imgk (aview SEGS H mem) (aview SEGS H' mem') ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H' mem').
Proof.
intros cx H mem H' mem' Hk (Hro & Hh & Hgi).
pose proof (fun x s => s6_lit_k H mem H' mem' x s Hk) as HL.
split; [|split].
- intros a Hin Hown Herr. rewrite Hk; [exact (Hro a Hin Hown Herr)|].
  destruct Hin as [(sg & Hsg & _ & Hr)|Hr].
  + apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- destruct Hh as (HM & HMi & HFZ & HRC & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) &
    (Hg1 & g & Hg2) & HP & HRT & HL1 & HD1 & HD2 & HD3).
  split; [intros q Hq; rewrite Hk; [exact (HM q Hq) | apply (s6_img_rng mod40A 8); [exact HMi | lia]]|].
  split; [exact HMi|].
  split; [intros s Hs; destruct (HFZ s Hs) as [H1 H2]; exact (conj (HL _ _ H1) H2)|].
  split; [intros s Hs; destruct (HRC s Hs) as [H1 H2]; exact (conj (HL _ _ H1) H2)|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl). exists tp.
    split; [|exact (HL _ _ Hl)]. rewrite (s6_rdword_k _ _ _ Hk); [exact Htp | |];
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_N, catA, kImgEnd in *; lia. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl). exists wp.
    split; [|exact (HL _ _ Hl)]. rewrite (s6_rdword_k _ _ _ Hk); [exact Hwp' | |]; unfold wordsA, kImgEnd; lia. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi q Hq. rewrite Hk; [exact (Hrr i Hi q Hq)|].
    unfold rolesA, kImgEnd; lia. }
  split.
  { split; [rewrite (s6_rdword_k _ _ _ Hk); [exact Hg1 | |]; unfold gotwA, kImgEnd; lia|].
    exists g. rewrite (s6_rdword_k _ _ _ Hk); [exact Hg2 | |]; unfold guardA, kImgEnd; lia. }
  exact (conj HP (conj HRT (conj HL1 (conj HD1 (conj HD2 HD3))))).
- intros q Hq. rewrite Hk; [exact (Hgi q Hq)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.

(* a loop point's facts but the slots at a later state: the journal, the blocks a permutation of the old ones, the
   meter, six registers, and every byte outside the m block, the callee's window below s1 and the slots 128 .. 144
   as it was *)
Lemma s6_lp_gen : forall cx ly S W regs mem md k acc c m t f ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  lt_base B MT cx -> s6_lp0 B MT cx ly S W regs mem md k acc c m t f ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 23 = getr regs 23 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (m <= a < m + seg_spec.SEG_M_SIZE) -> ~ (x_s1 cx - STK_m_refuse <= a < x_s1 cx) ->
     ~ (x_s1 cx + 128 <= a < x_s1 cx + 144) -> rdW W2 mem2 a = rdW W mem a) ->
  s6_lp0 B MT cx ly2 S2 W2 regs2 mem2 md2 k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f ly2 S2 W2 regs2 mem2 md2 HB HLP HJ2 HP HML P2 P3 P4 P8 P9 P23 KEEP.
destruct (s6_nums0 cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof asan_consts as (C1 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & HFR0 & _).
pose proof HPRE0 as (HAR0 & _).
destruct HLP as ((HF & HI & HBl & HBu) & Hc & Hm & Ht & R23 & Hrc & Hst & Hcnt).
destruct HF as (HJ & R2 & R3 & R4 & R8 & _ & Hsv & H0 & H8 & H16 & HFL & S200 & Hzs & S184).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof HJ2 as (HAR2 & _).
assert (HST : STK_m_refuse = 8240) by reflexivity.
(* the block m against the image, c, t and the frame *)
pose proof (blk_off_imgP B ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as Hoff.
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as (_ & _ & _ & Happ & _).
unfold off_img, seg_spec.SEG_M_SIZE, req_size in Hoff, Happ. cbn in Hoff, Happ.
destruct Ht as (Htin & Ht4 & Ht16 & Htaddr). destruct Hc as (Hcin & Hc4 & Hc16 & Hcaddr).
destruct Hm as (Hmin' & _ & _ & Hmaddr).
assert (Htn : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
destruct (s6_blk_sep ly S W mem md (x_bl0 B cx) t (x_tn cx f) m c HAR HBl ltac:(lia)) as (Hmc' & Hmt & _).
unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in Hmc', Hmt.
destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR Hcin) as (_ & _ & Hcceil & _).
destruct (al_blocks _ _ LAWS ly S W mem md t (x_tn cx f) HAR Htin) as (_ & _ & Htceil & _).
unfold seg_spec.SEG_C_SIZE, req_size in Hcceil. cbn in Hcceil.
assert (Htreq : req_size (x_tn cx f) = x_tn cx f) by (unfold req_size; destruct (Z.eqb_spec (x_tn cx f) 0); lia).
rewrite Htreq in Htceil.
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (al_sep _ _ LAWS ly S W mem md HAR) as (Hsep & HfrF).
rewrite Forall_forall in HfrF. pose proof (HfrF _ Hin3) as (HF4 & HFc). cbn [fst snd] in HF4, HFc.
pose proof (s6_pw_app zdisjoint _ _ (m, req_size seg_spec.SEG_M_SIZE) (frame_addr ly LT_FCLS (x_fpos cx), fs_frame_bytes LT_FCLS) Hsep
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hmin)
  (in_map (fun f0 : Z * Z => (frame_addr ly (fst f0) (snd f0), fs_frame_bytes (fst f0))) _ _ Hin3)) as HmF.
destruct (al_layout _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) ly HAR0 Hly) as (_ & Hfa & _).
assert (EFR : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr; apply Hfa).
rewrite EFR in HF4, HFc, HmF.
assert (FB : fs_frame_bytes LT_FCLS = 512) by reflexivity. rewrite FB in HFc, HmF.
unfold zdisjoint, seg_spec.SEG_M_SIZE, req_size in HmF. cbn [fst snd] in HmF. cbn in HmF.
assert (Hsh : SHADOW_OFF <= x_sh cx /\ x_sh cx + 36 <= SHADOW_OFF + 2 ^ 44).
{ unfold x_sh, shadow_addr. pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (x_fr cx) 8 (2 ^ 44 - 8) ltac:(lia) ltac:(unfold S6_CMAX in *; lia)). lia. }
(* a byte away from m, from the callee's window and from the slots 128 .. 144 is kept *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> (a < m \/ m + 9236 <= a) -> (a < x_s1 cx - 8240 \/ x_s1 cx + 144 <= a) ->
  rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha H1 H2; apply KEEP; [exact Ha | unfold seg_spec.SEG_M_SIZE; lia | rewrite HST; lia | lia]).
assert (KW : forall a, 0 <= a -> (a + 8 <= m \/ m + 9236 <= a) -> (a + 8 <= x_s1 cx - 8240 \/ x_s1 cx + 144 <= a) ->
  a + 8 <= 2 ^ 64 -> rdword (rdW W2 mem2) a = rdword (rdW W mem) a).
{ intros a H0' H1 H2 H3. apply rdword_ext. intros j Hj. apply K2; lia. }
assert (HIMG : s6_imgk (rdW W mem) (rdW W2 mem2)).
{ intros a Ha. apply K2; unfold kImgEnd in *; [lia | lia | unfold S6_CMIN in *; lia]. }
unfold s6_lp0.
split; [|split; [|split; [|split; [|split; [rewrite P23; exact R23|split; [|split; [|exact Hcnt]]]]]]].
- split; [|split; [exact (s6_img_k cx _ _ _ _ HIMG HI)|split]].
  + split; [exact HJ2|]. rewrite P2, P3, P4, P8, P9.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
    split.
    { intros i r Hi. rewrite KW; [exact (Hsv i r Hi) | | | |];
        assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence);
        change (length LT_SAVED) with 13%nat in Hi13; unfold x_sp0 in *; lia. }
    split; [rewrite KW; [exact H0 | lia | lia | lia | lia]|].
    split; [rewrite KW; [exact H8 | lia | lia | lia | lia]|].
    split; [rewrite KW; [exact H16 | lia | lia | lia | lia]|].
    split; [rewrite KW; [exact HFL | unfold LT_FLAGW; lia | unfold LT_FLAGW; lia | unfold LT_FLAGW; lia | unfold LT_FLAGW; lia]|].
    split; [rewrite KW; [exact S200 | lia | lia | lia | lia]|].
    split; [|rewrite KW; [exact S184 | lia | lia | lia | lia]].
    intros i Hi. rewrite lt_fsh_len in Hi. rewrite K2; [exact (Hzs i ltac:(rewrite lt_fsh_len; exact Hi)) | | |];
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, S6_CMIN in *; lia.
  + exact (Permutation_trans HP HBl).
  + destruct HBu as (B1 & B2 & B3 & _ & B5 & B6). exact (conj B1 (conj B2 (conj B3 (conj HML (conj B5 B6))))).
- split; [exact (Permutation_in _ (Permutation_sym HP) Hcin)|]. split; [exact Hc4|]. split; [exact Hc16|].
  destruct Hcaddr as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  assert (Hc2 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP) Hcin).
  split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 c seg_spec.SEG_C_SIZE); [exact HAR2 | exact Hc2 | lia | unfold req_size; cbn; lia]|].
  intros _. destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 c seg_spec.SEG_C_SIZE HAR2 Hc2) as [_ Hv]. exact Hv.
- split; [exact (Permutation_in _ (Permutation_sym HP) Hmin)|]. split; [exact Hm4|]. split; [exact Hm16|].
  destruct Hmaddr as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  assert (Hm2 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP) Hmin).
  split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 m seg_spec.SEG_M_SIZE); [exact HAR2 | exact Hm2 | lia | unfold req_size; cbn; lia]|].
  intros _. destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 m seg_spec.SEG_M_SIZE HAR2 Hm2) as [_ Hv]. exact Hv.
- split; [exact (Permutation_in _ (Permutation_sym HP) Htin)|]. split; [exact Ht4|]. split; [exact Ht16|].
  destruct Htaddr as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  assert (Ht2 : In (t, x_tn cx f) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP) Htin).
  split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 t (x_tn cx f)); [exact HAR2 | exact Ht2 | lia | rewrite Htreq; lia]|].
  intros _. destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 t (x_tn cx f) HAR2 Ht2) as [_ Hv]. rewrite Htreq in Hv. exact Hv.
- destruct Hrc as (bs & HBs & Henc). exists bs. split; [|exact Henc].
  destruct Henc as (Hlen & _). unfold seg_spec.SEG_C_SIZE in Hlen.
  intros i Hi. rewrite K2; [exact (HBs i Hi) | lia | lia | lia].
- destruct Hst as ((Hzs2 & Hn0) & _). split; [split; [|exact Hn0]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. unfold x_tn, seg_spec.seg_txt_n in Htceil, Hmt.
    rewrite K2; [exact (Hzs2 i ltac:(rewrite length_app; cbn [length]; lia)) | lia | lia | lia].
  + intros x Hx.
    assert (Ht2 : In (t, x_tn cx f) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP) Htin).
    apply (YG0d_tail.AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 t (x_tn cx f)
      (t + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) x HAR2 Ht2);
      [rewrite Htreq; unfold x_tn, seg_spec.seg_txt_n; lia | lia].
Qed.
(* the slots' offsets *)
Lemma s6_slots_off : forall cx c m f o v, In (o, v) (s6_slots cx c m f) -> 16 <= o <= 216.
Proof.
intros cx c m f o v Hin.
assert (HO : forallb (fun ov => (16 <=? fst ov) && (fst ov <=? 216)) (s6_slots cx c m f) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HO (o, v) Hin) as Ho. cbn [fst] in Ho.
apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2. lia.
Qed.
(* a loop point's facts at a later state whose bytes outside the m block and the callee's window are the old ones *)
Lemma s6_lp_genL : forall cx ly S W regs mem md k acc c m t f ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  lt_base B MT cx -> s6_lp B MT cx ly S W regs mem md k acc c m t f ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 23 = getr regs 23 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (m <= a < m + seg_spec.SEG_M_SIZE) -> ~ (x_s1 cx - STK_m_refuse <= a < x_s1 cx) ->
     rdW W2 mem2 a = rdW W mem a) ->
  s6_lp B MT cx ly2 S2 W2 regs2 mem2 md2 k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f ly2 S2 W2 regs2 mem2 md2 HB HLP HJ2 HP HML P2 P3 P4 P8 P9 P23 KEEP.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
apply s6_lp_of0.
- apply (s6_lp_gen cx ly S W regs mem md k acc c m t f ly2 S2 W2 regs2 mem2 md2 HB
    (s6_lp0_of B MT _ _ _ _ _ _ _ _ _ _ _ _ _ HLP) HJ2 HP HML P2 P3 P4 P8 P9 P23).
  intros a Ha H1 H2 _. exact (KEEP a Ha H1 H2).
- pose proof HLP as (_ & _ & _ & _ & _ & Hsl & _).
  intros o v Hin. pose proof (s6_slots_off cx c m f o v Hin) as Ho.
  rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) (x_s1 cx + o)); [exact (Hsl o v Hin)|].
  intros j Hj. apply KEEP; unfold seg_spec.SEG_M_SIZE, S6_CMIN in *; lia.
Qed.

(* ===================================== the m_refuse calls ===================================== *)
(* the walk's hypotheses: the meter's set_fs law, the listing's entries, m_refuse's contract (image B's copy of
   the image-A owner's FINAL text, lib/B/Prog/m_refuse_c.v) *)
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog.
Hypothesis MRF : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.

Lemma s6_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Ltac s6_pg HP := lazymatch goal with |- getr _ ?rr = _ =>
  let z := eval vm_compute in (bv_unsigned rr) in
  rewrite (s6_pres _ _ rr z HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) end.
(* m_refuse's writes lie in the block *)
Lemma s6_wfp : forall m mc a, inFP (m_refuse_W m mc) a -> m <= a < m + 9236.
Proof.
intros m mc a (r & Hr & Ha). unfold m_refuse_W in Hr.
destruct (Z.of_nat (length (SegModel.mc_kept mc)) <? 8) eqn:E8.
- apply Z.ltb_lt in E8. cbn [app In] in Hr.
  unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_NKEPT, seg_spec.MC_REFUSED in *.
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [fst snd] in Ha; lia |]). destruct Hr.
- cbn [app In] in Hr. destruct Hr as [Hr | []]. subst r. cbn [fst snd] in Ha.
  unfold seg_spec.MC_REFUSED in Ha. lia.
Qed.

(* the call m_refuse(m, 0) of turn i (0x853f0 / 0x85424), returning at lo with m holding m_refuse's table *)
Lemma s6_call : forall lo ed f i cx ly S W regs mem md k acc c m t,
  S6_RA B MT lo ed f i -> 0 <= lo < 0x2000 -> lo mod 2 = 0 ->
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  s6_lp B MT cx ly S W regs mem md k acc c m t f ->
  (i < length (SegModel.mc_seg (s6_M0 (x_pl cx) f)))%nat ->
  getr regs 1 = Z_to_bv 64 (BASE + lo) -> getr regs 10 = w64 m -> getr regs 11 = w64 0 ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs 21 = w64 (256 * Z.of_nat i) -> getr regs 22 = w64 (Z.of_nat i) ->
  getr regs 24 = w64 (m + 32 + 256 * Z.of_nat i) -> getr regs 26 = w64 (m + 16 + 256 * Z.of_nat i) ->
  getr regs 25 = w64 (shadow_addr (m + 20 + 256 * Z.of_nat i)) ->
  getr regs 27 = w64 (shadow_addr (m + 32 + 256 * Z.of_nat i)) ->
  sa_mconf (rdW W mem) m (s6_MI (x_pl cx) f i) ->
  SegModel.m_cross_seg (s6_MI (x_pl cx) f i) i =
    SegModel.m_upd (SegModel.m_refuse (s6_MI (x_pl cx) f i) 0 false) i ed ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_m_refuse)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros lo ed f i cx ly S W regs mem md k acc c m t HKA Hlo Hlo2 HB Hfrm Hnf HLP Hi
  R1 R10 R11 R18 R21 R22 R24 R26 R25 R27 HMC Hed.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HB as (HPRE0 & HAP0 & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HLP as ((HF & HI & HBL & HBUD) & HHc & HHm & HHt & R23 & HSL & HRC & HST & HCNT).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HBUD as (Bk & Brem & Bev & B4 & _).
pose proof HI as (HRO & HIMG & _).
pose proof HIMG as (_ & _ & Hfz & _ & _ & _ & _ & _ & Hssp & _).
destruct lits_incl as (_ & HMRI & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof (ltoi_callee_stks STK_m_refuse
  ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; right; right; right; left; reflexivity)) as (HSI0 & HSI1).
unfold LTOI_FRAME_MAX in HSI1.
pose proof HHm as (HMin & _ & _ & HMad).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
destruct (s6_blk_sep ly S W mem md (x_bl0 B cx) t (x_tn cx f) m c HAR HBL
  ltac:(unfold x_tn, seg_spec.seg_txt_n; lia)) as (_ & _ & HMn).
(* the frame chain at the call's sp: s0 = SP0, the stack from S1 to the top present *)
assert (HRD : astack_rd ly (rdW W mem) (x_s1 cx)).
{ apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HAP0).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch1 & Hch).
assert (Hsp' : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0) by lia.
assert (Hch' : achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs) ch1).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact Hch. }
assert (Hraw : YK0s.ret_ok (getr regs 1)) by (rewrite R1; apply ret_ok_codeptr_v; lia).
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)) by (rewrite R1, unsigned_lit_small by lia; lia).
(* m_refuse_pre at this site *)
set (mc := s6_MI (x_pl cx) f i) in *.
assert (HMR : SegModel.mc_refused mc + 1 < 2 ^ 32).
{ pose proof (s6_cnt (s6_M0 (x_pl cx) f) i) as (_ & _ & Hr).
  pose proof (s6_M0_refused (x_pl cx) f) as Hr0. pose proof (s6_nfiles_range (x_pl cx)) as Hn4.
  pose proof (s6_mconf_len _ _ _ HMC) as HL. unfold mc, s6_MI in HL. rewrite s6_len in HL.
  unfold x_nf in Hnf. unfold mc, s6_MI. lia. }
assert (HPRE : m_refuse_pre SEGS B ly S (rdW W mem) seg_litA_fz gotwA guardA m 0 mc false).
{ unfold m_refuse_pre.
  split; [lia|]. split; [exact Hm16|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HMin | lia]|].
  split; [exact HMad|]. split; [exact HMC|].
  split.
  { intros x Hx. apply (YG0d_tail.AR_block_word_vis SEGS B ly S W mem md m seg_spec.SEG_M_SIZE
      (m + seg_spec.SEG_M_SIZE - 1) x HAR HMin); rewrite ?HRM; unfold seg_spec.SEG_M_SIZE in *; lia. }
  split; [lia|]. split; [exact HMR|]. split; [exact Hfrm|]. split; [exact Hssp|].
  intros x Hx. exact (proj1 (Hfz x (HMRI x Hx))). }
assert (HEV : st_nev S + EV_m_refuse <= EV_MAX) by (unfold EV_m_refuse; lia).
(* the call *)
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_m_refuse)) STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k
    STK_m_refuse (m_refuse_W m mc) EV_m_refuse (x_s1 cx - x_sp0 cx) (getr regs 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       sa_mconf (aview SEGS (w_H W') mem') m (SegModel.m_refuse mc 0 false) /\
       sa_kept SEGS W mem W' mem' regs STK_m_refuse
         (fun a =>
          (Z.of_nat (length (SegModel.mc_kept mc)) < 8 /\
           seg_spec.kept_addr m (length (SegModel.mc_kept mc)) <= a <
           seg_spec.kept_addr m (length (SegModel.mc_kept mc)) + seg_spec.MC_KEPT_LEN) \/
          (Z.of_nat (length (SegModel.mc_kept mc)) < 8 /\ m + seg_spec.MC_NKEPT <= a < m + seg_spec.MC_NKEPT + 4) \/
          m + seg_spec.MC_REFUSED <= a < m + seg_spec.MC_REFUSED + 4) /\
       sa_noalloc B ly S ly' S')
    HJ Hsp' Hal ltac:(lia) HSI0 ltac:(lia) ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0)
    eq_refl Hraw Hra4 Hch').
  - intros HPRE1. eapply SRr_mono.
    + exact (MRF fx ly S W regs mem md ch1 m 0 mc false HPRE1 HRO R10 ltac:(lia) R11 HPRE HEV).
    + intros W3 c3 _ H3. exact H3.
  - intros a Ha. right. exists m, seg_spec.SEG_M_SIZE. split; [exact HMin|]. split; [exact HMn|].
    rewrite HRM. pose proof (s6_wfp m mc a Ha). unfold seg_spec.SEG_M_SIZE. lia. }
(* the return at lo *)
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle Hfx (HJ2 & HJc & HP & HMC2 & HKP & (HPm & -> & (fsf & ->))).
replace (k + EV_m_refuse) with k in HJ2 by (unfold EV_m_refuse; lia).
replace (getr regs 1) with (Z_to_bv 64 (BASE + lo)) by (rewrite R1; reflexivity).
apply (HKA fx1 cx ly (set_fs fsf S) W2 regs2 mem2 md2 k acc c m t); [|exact Hed].
unfold s6_rp.
split; [exact HB|]. split; [exact (fxrel_frm0 fx fx1 Hfrm Hfx)|]. split; [exact Hnf|].
split.
{ apply (s6_lp_genL cx ly S W regs mem md k acc c m t f ly (set_fs fsf S) W2 regs2 mem2 md2 HB HLP HJ2 HPm
    (mo_le_set_fs_r MT MTFL _ _ fsf _ B4)).
  - s6_pg HP. reflexivity.
  - s6_pg HP. reflexivity.
  - s6_pg HP. reflexivity.
  - s6_pg HP. reflexivity.
  - s6_pg HP. reflexivity.
  - s6_pg HP. reflexivity.
  - intros a Ha H1 H2. apply HKP; [exact Ha | |].
    + unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. exact H2.
    + intros HE. apply H1. unfold seg_spec.SEG_M_SIZE.
      unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_NKEPT, seg_spec.MC_REFUSED in HE.
      lia. }
split; [exact Hi|].
split; [s6_pg HP; exact R18|].
split; [s6_pg HP; exact R21|].
split; [s6_pg HP; exact R22|].
split; [s6_pg HP; exact R24|].
split; [s6_pg HP; exact R26|].
split; [s6_pg HP; exact R25|].
split; [s6_pg HP; exact R27|].
exact HMC2.
Qed.

(* ===================================== the regions of m->seg[i] ===================================== *)
(* a write window of m->seg[i] (based at s8 = m + 0x20 + 256 i) *)
Lemma s6_win24 : forall E (W : world SEGS) mem md ly S m i s1 lo hi,
  AR SEGS B ly S W mem md -> In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) ->
  bv_unsigned (ew E 24) = m + 32 + 256 * Z.of_nat i -> bv_unsigned (ew E 9) = s1 -> bv_unsigned (ew E 32) = m ->
  (i <= 31)%nat -> -32 <= lo -> lo <= hi -> hi <= 4 -> 0 <= m -> m + 9236 <= s1 ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 24%nat) lo hi lo hi []) /\
  extent_disjoint E s6_frame (YP09.mkRegion (Some 24%nat) lo hi lo hi []) /\
  extent_disjoint E s6_nreg (YP09.mkRegion (Some 24%nat) lo hi lo hi []).
Proof.
intros E W mem md ly S m i s1 lo hi HAR Hin U24 U9 U32 Hi Hlo Hlh Hhi Hm0 Hms.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR Hin) as (_ & _ & Hceil & _ & Hpres & _).
pose proof asan_consts as (C1 & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite HRM in Hpres, Hceil.
split; [|split].
- unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (m + 32 + 256 * Z.of_nat i + o) ltac:(lia))).
- unfold extent_disjoint, s6_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U9. lia.
- unfold extent_disjoint, s6_nreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U32. lia.
Qed.
(* the head's region: role (atom 37), role_set, model_set *)
Lemma s6_segL_ok : forall E (W : world SEGS) mem md ly S m i s1 r (rs ms : bool),
  AR SEGS B ly S W mem md -> In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) ->
  bv_unsigned (ew E 24) = m + 32 + 256 * Z.of_nat i -> bv_unsigned (ew E 9) = s1 -> bv_unsigned (ew E 32) = m ->
  ew E 37 = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
  (i <= 31)%nat -> 0 <= m -> m + 9236 <= s1 ->
  rd32 (rdW W mem) (m + 256 * Z.of_nat i + 16) r ->
  rd32 (rdW W mem) (m + 256 * Z.of_nat i + 20) (seg_spec.b2z rs) ->
  rd32 (rdW W mem) (m + 256 * Z.of_nat i + 32) (seg_spec.b2z ms) ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) (s6_segL (seg_spec.b2z rs) (seg_spec.b2z ms)) /\
  extent_disjoint E s6_frame (s6_segL (seg_spec.b2z rs) (seg_spec.b2z ms)) /\
  extent_disjoint E s6_nreg (s6_segL (seg_spec.b2z rs) (seg_spec.b2z ms)).
Proof.
intros E W mem md ly S m i s1 r rs ms HAR Hin U24 U9 U32 E37 Hr Hi Hm0 Hms R16 R20 R32.
assert (Hb : forall b : bool, 0 <= seg_spec.b2z b < 2 ^ 32) by (intros [|]; cbn; lia).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR Hin) as (_ & _ & Hceil & _).
pose proof asan_consts as (C1 & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite HRM in Hceil.
split; [|split].
- unfold YP09.region_ok, s6_segL. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ _ (-16) 4 (SOff 37 0) r);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    replace (m + 32 + 256 * Z.of_nat i + -16) with (m + 256 * Z.of_nat i + 16) by lia.
    exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ R16).
  + apply (chunk_ok_val SEGS E _ _ (-12) 4 (SLit (seg_spec.b2z rs)) (seg_spec.b2z rs));
      [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact (Hb rs) | cbn; lia |].
    replace (m + 32 + 256 * Z.of_nat i + -12) with (m + 256 * Z.of_nat i + 20) by lia.
    exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ R20).
  + apply (chunk_ok_val SEGS E _ _ 0 4 (SLit (seg_spec.b2z ms)) (seg_spec.b2z ms));
      [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact (Hb ms) | cbn; lia |].
    replace (m + 32 + 256 * Z.of_nat i + 0) with (m + 256 * Z.of_nat i + 32) by lia.
    exact (PaLibF.val_mem_of_rd32 SEGS _ _ _ _ R32).
- unfold extent_disjoint, s6_frame, s6_segL. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U9. lia.
- unfold extent_disjoint, s6_nreg, s6_segL. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U32. lia.
Qed.
(* a word the run stored 0 into, through the ASan view *)
Lemma s6_chunk0 : forall (W : world SEGS) E ss (ms : machine_state) idx rg p off a,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) idx = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 4 (SLit 0))) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  rd32 (rdW W (ms_mem ms)) (a + off) 0.
Proof.
intros W E ss ms idx rg p off a HS Hi Hb Hc Ha.
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) idx rg p off 4 (SLit 0) a 0 HS Hi Hb Hc Ha
  eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV. change (N.to_nat 4) with 4%nat in HV.
intros k Hk. unfold aview. rewrite (HV k Hk). cbn [option_map]. f_equal.
assert (L : le_byte 0 4 k = 0)
  by (unfold le_byte; rewrite Z.mod_0_l by (cbn; lia); rewrite Z.shiftr_0_l; reflexivity).
assert (L2 : YO0f.le_byte 0 4 k = 0)
  by (unfold YO0f.le_byte; rewrite Z.mod_0_l by (cbn; lia); rewrite Z.shiftr_0_l; reflexivity).
rewrite L, L2. reflexivity.
Qed.
Ltac s6_z HS idx off :=
  let HSo := fresh "HSo" in pose proof HS as HSo; try unfold st_ok_pi in HSo;
  lazymatch type of HSo with st_ok _ _ ?ss _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss) idx) in
    lazymatch l with Some ?rg =>
      apply (s6_chunk0 _ _ ss _ idx rg 24%nat off _ HSo);
      [vm_compute; reflexivity | reflexivity | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | ]
    end end.

(* ---- the return 0x853f4 of the call at 0x853f0: check 13 (role_set's shadow, s9), role_set := 0, check 14 (role's
   shadow, SH(s10)), a3 reloaded, role := 0, j 0x85438 ---- *)
Lemma s6_retR : forall f i, S6_LT_stmt B MT f i -> S6_R_stmt B MT LO_S6RR SegModel.ms_drop_role f i.
Proof.
intros f i HLT cx ly S W regs mem md k acc c m t
  (HB & Hfrm & Hnf & HLP & Hi & R18 & R21 & R22 & R24 & R26 & R25 & R27 & HMC) Hed.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof HLP as ((HFR & _ & HBL & HBUD) & _ & _ & _ & R23 & Hsl & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & _ & _ & _ & _ & _ & _ & S200 & _).
pose proof HBUD as (_ & _ & _ & B4 & _).
destruct (s6_blk_sep ly S W mem md (x_bl0 B cx) t (x_tn cx f) m c HAR HBL
  ltac:(unfold x_tn, seg_spec.seg_txt_n; lia)) as (_ & _ & HMn).
set (M0 := s6_M0 (x_pl cx) f) in *.
set (mc := s6_MI (x_pl cx) f i) in *.
set (n := Z.of_nat (length (SegModel.mc_seg M0))).
pose proof (s6_mconf_len _ _ _ HMC) as HL32. rewrite s6_refuse_seg in HL32. unfold mc, s6_MI in HL32.
rewrite s6_len in HL32. fold M0 in HL32.
assert (Hi31 : (i <= 31)%nat) by lia.
assert (Hn : 1 <= n <= 32) by (unfold n; lia).
pose proof (s6_rd_n _ _ _ HMC) as HN. rewrite s6_refuse_seg in HN. unfold mc, s6_MI in HN. rewrite s6_len in HN.
fold M0 n in HN.
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
destruct (s6_E_facts regs m n 0) as (EEo & E32 & E33 & E34 & E35 & _).
assert (E24 : ew (s6_E regs m n 0) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i))
  by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (U24 : bv_unsigned (ew (s6_E regs m n 0) 24) = m + 32 + 256 * Z.of_nat i)
  by (rewrite E24; apply unsigned_lit_small; unfold S6_CMAX in *; lia).
assert (U9 : bv_unsigned (ew (s6_E regs m n 0) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; unfold S6_CMIN in *; lia).
assert (U32 : bv_unsigned (ew (s6_E regs m n 0) 32) = m) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HSI : (i < length (SegModel.mc_seg (SegModel.m_refuse mc 0 false)))%nat)
  by (rewrite s6_refuse_seg; unfold mc, s6_MI; rewrite s6_len; exact Hi).
destruct (s6_win24 (s6_E regs m n 0) W mem md ly S m i (x_s1 cx) (-16) (-8) HAR Hmin U24 U9 U32 Hi31
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold S6_CMIN in *; lia)) as (WOK & WD1 & WD2).
unfold S6_CMIN, S6_CMAX in *.
pose proof (s6_seed LO_S6RR s6_srR s6_facts [s6_segR] W regs mem (x_s1 cx) m n 0
  (s6_regs_okR regs m n 0 i ltac:(lia) ltac:(lia) Hi31 R24 R26 R18 R25 R27)
  (s6_facts_ok regs m n 0 i (x_s1 cx) R9 ltac:(unfold S6_CMIN; lia) Hs1m R21 R22 R24 Hi31 Hm4
    ltac:(unfold S6_CMAX; lia) Hm16 Hn)
  ltac:(vm_compute; reflexivity) ltac:(constructor; [exact WOK | constructor])
  ltac:(intros rg [<- | []]; exact (conj WD1 WD2))
  ltac:(cbn; tauto) R9 ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) ltac:(lia)
  ltac:(lia) S192 S200 S208 S216 HN) as HS.
pose proof (s6_shok B ly S W mem md regs m n 0 i HAR Hmin Hi31 R24) as SHOK.
assert (HEI : img_env VAL A_LIM (s6_E regs m n 0)) by (unfold s6_E; apply Eimg_env).
remember (s6_E regs m n 0) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = Z_to_bv 64 (256 * Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
unfold cfg_at.
(* 0x853f4 .. 0x85418: the two shadow tests vanish (s6_SH), the two stores of 0, j 0x85438 *)
paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6T.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_gen; [reflexivity | exact U24 | |];
        [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; left;
          exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin|]; split; [exact HMn|];
          unfold req_size, seg_spec.SEG_M_SIZE; cbn; lia | ] ]. }
s6_mdv mdv.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (m + 256 * Z.of_nat i + 16 <= a < m + 256 * Z.of_nat i + 24) ->
    rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha Hn'; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => m + 256 * Z.of_nat i + 16 <= a < m + 256 * Z.of_nat i + 24) Hfr);
      [ intros b wlo whi a' Hin Hrr; cbn [windows map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
        repeat (destruct Hin as [Hq0 | Hin];
          [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U24 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn' ]) end.
assert (Z16 : rd32 (rdW W (ms_mem ms)) (m + 256 * Z.of_nat i + 16) 0).
{ replace (m + 256 * Z.of_nat i + 16) with (m + 32 + 256 * Z.of_nat i + -16) by lia. s6_z HS 2%nat (-16). exact U24. }
assert (Z20 : rd32 (rdW W (ms_mem ms)) (m + 256 * Z.of_nat i + 20) 0).
{ replace (m + 256 * Z.of_nat i + 20) with (m + 32 + 256 * Z.of_nat i + -12) by lia. s6_z HS 2%nat (-12). exact U24. }
pmkst HS.
refine (HLT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m t HB Hfrm Hnf _ Hi _ _ _ _ _ _ _).
- apply (s6_lp_genL cx ly S W regs mem md k acc c m t f ly S W (ms_regs ms) (ms_mem ms) mdv HB HLP HJ
    (Permutation_refl _) B4); try s6_kg HS.
  intros a Ha H1 _. apply KEEP; [exact Ha|]. unfold seg_spec.SEG_M_SIZE in H1. lia.
- s6_vreg HS (13%bv : bv 5). rewrite (U_atom _ 33 SHADOW_OFF) by s6_side. reflexivity.
- s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
- s6_vreg HS (21%bv : bv 5). rewrite (U_atom _ 21 (256 * Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (22%bv : bv 5). rewrite (U_atom _ 22 (Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (24%bv : bv 5). rewrite (U_atom _ 24 (m + 32 + 256 * Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (26%bv : bv 5). rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) (-16)) by s6_side. lia.
- unfold s6_MI. rewrite s6_step. fold (s6_MI (x_pl cx) f i). fold mc. rewrite Hed.
  apply (s6_store_drop_role (rdW W mem) (rdW W (ms_mem ms)) m _ i HMC HSI); [|exact Z16 | exact Z20].
  intros x Hx Hn'. apply KEEP; [lia | exact Hn'].
Qed.
(* ---- the return 0x85428 of the call at 0x85424: check 15 (model_set's shadow, s11), model_set := 0, a3 reloaded,
   on to 0x85438 ---- *)
Lemma s6_retM : forall f i, S6_LT_stmt B MT f i -> S6_R_stmt B MT LO_S6RM SegModel.ms_drop_model f i.
Proof.
intros f i HLT cx ly S W regs mem md k acc c m t
  (HB & Hfrm & Hnf & HLP & Hi & R18 & R21 & R22 & R24 & R26 & R25 & R27 & HMC) Hed.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof HLP as ((HFR & _ & HBL & HBUD) & _ & _ & _ & R23 & Hsl & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & _ & _ & _ & _ & _ & _ & S200 & _).
pose proof HBUD as (_ & _ & _ & B4 & _).
destruct (s6_blk_sep ly S W mem md (x_bl0 B cx) t (x_tn cx f) m c HAR HBL
  ltac:(unfold x_tn, seg_spec.seg_txt_n; lia)) as (_ & _ & HMn).
set (M0 := s6_M0 (x_pl cx) f) in *.
set (mc := s6_MI (x_pl cx) f i) in *.
set (n := Z.of_nat (length (SegModel.mc_seg M0))).
pose proof (s6_mconf_len _ _ _ HMC) as HL32. rewrite s6_refuse_seg in HL32. unfold mc, s6_MI in HL32.
rewrite s6_len in HL32. fold M0 in HL32.
assert (Hi31 : (i <= 31)%nat) by lia.
assert (Hn : 1 <= n <= 32) by (unfold n; lia).
pose proof (s6_rd_n _ _ _ HMC) as HN. rewrite s6_refuse_seg in HN. unfold mc, s6_MI in HN. rewrite s6_len in HN.
fold M0 n in HN.
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
destruct (s6_E_facts regs m n 0) as (EEo & E32 & E33 & E34 & E35 & _).
assert (E24 : ew (s6_E regs m n 0) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i))
  by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (U24 : bv_unsigned (ew (s6_E regs m n 0) 24) = m + 32 + 256 * Z.of_nat i)
  by (rewrite E24; apply unsigned_lit_small; unfold S6_CMAX in *; lia).
assert (U9 : bv_unsigned (ew (s6_E regs m n 0) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; unfold S6_CMIN in *; lia).
assert (U32 : bv_unsigned (ew (s6_E regs m n 0) 32) = m) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HSI : (i < length (SegModel.mc_seg (SegModel.m_refuse mc 0 false)))%nat)
  by (rewrite s6_refuse_seg; unfold mc, s6_MI; rewrite s6_len; exact Hi).
destruct (s6_win24 (s6_E regs m n 0) W mem md ly S m i (x_s1 cx) 0 4 HAR Hmin U24 U9 U32 Hi31
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold S6_CMIN in *; lia)) as (WOK & WD1 & WD2).
unfold S6_CMIN, S6_CMAX in *.
pose proof (s6_seed LO_S6RM s6_srR s6_facts [s6_segM] W regs mem (x_s1 cx) m n 0
  (s6_regs_okR regs m n 0 i ltac:(lia) ltac:(lia) Hi31 R24 R26 R18 R25 R27)
  (s6_facts_ok regs m n 0 i (x_s1 cx) R9 ltac:(unfold S6_CMIN; lia) Hs1m R21 R22 R24 Hi31 Hm4
    ltac:(unfold S6_CMAX; lia) Hm16 Hn)
  ltac:(vm_compute; reflexivity) ltac:(constructor; [exact WOK | constructor])
  ltac:(intros rg [<- | []]; exact (conj WD1 WD2))
  ltac:(cbn; tauto) R9 ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) ltac:(lia)
  ltac:(lia) S192 S200 S208 S216 HN) as HS.
pose proof (s6_shok B ly S W mem md regs m n 0 i HAR Hmin Hi31 R24) as SHOK.
assert (HEI : img_env VAL A_LIM (s6_E regs m n 0)) by (unfold s6_E; apply Eimg_env).
remember (s6_E regs m n 0) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = Z_to_bv 64 (256 * Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
unfold cfg_at.
(* 0x85428 .. 0x85434: the shadow test vanishes (s6_SH), the store of 0, a3 reloaded *)
paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6T.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_gen; [reflexivity | exact U24 | |];
        [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; left;
          exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin|]; split; [exact HMn|];
          unfold req_size, seg_spec.SEG_M_SIZE; cbn; lia | ] ]. }
s6_mdv mdv.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (m + 256 * Z.of_nat i + 32 <= a < m + 256 * Z.of_nat i + 36) ->
    rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha Hn'; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => m + 256 * Z.of_nat i + 32 <= a < m + 256 * Z.of_nat i + 36) Hfr);
      [ intros b wlo whi a' Hin Hrr; cbn [windows map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
        repeat (destruct Hin as [Hq0 | Hin];
          [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U24 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn' ]) end.
assert (Z32 : rd32 (rdW W (ms_mem ms)) (m + 256 * Z.of_nat i + 32) 0).
{ replace (m + 256 * Z.of_nat i + 32) with (m + 32 + 256 * Z.of_nat i + 0) by lia. s6_z HS 2%nat 0. exact U24. }
pmkst HS.
refine (HLT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m t HB Hfrm Hnf _ Hi _ _ _ _ _ _ _).
- apply (s6_lp_genL cx ly S W regs mem md k acc c m t f ly S W (ms_regs ms) (ms_mem ms) mdv HB HLP HJ
    (Permutation_refl _) B4); try s6_kg HS.
  intros a Ha H1 _. apply KEEP; [exact Ha|]. unfold seg_spec.SEG_M_SIZE in H1. lia.
- s6_vreg HS (13%bv : bv 5). rewrite (U_atom _ 33 SHADOW_OFF) by s6_side. reflexivity.
- s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
- s6_vreg HS (21%bv : bv 5). rewrite (U_atom _ 21 (256 * Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (22%bv : bv 5). rewrite (U_atom _ 22 (Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (24%bv : bv 5). rewrite (U_atom _ 24 (m + 32 + 256 * Z.of_nat i)) by s6_side. reflexivity.
- s6_vreg HS (26%bv : bv 5). rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) (-16)) by s6_side. lia.
- unfold s6_MI. rewrite s6_step. fold (s6_MI (x_pl cx) f i). fold mc. rewrite Hed.
  apply (s6_store_drop_model (rdW W mem) (rdW W (ms_mem ms)) m _ i HMC HSI); [|exact Z32].
  intros x Hx Hn'. apply KEEP; [lia | exact Hn'].
Qed.

(* the two ends of a head run: on to the latch with the table unchanged (the goal left: the model), or into the call
   of m_refuse returning at lo (the goal left: the model equation) *)
Ltac s6_out_latch HS HJ :=
  lazymatch goal with HLT : S6_LT_stmt _ _ ?f ?i, HB : lt_base _ _ ?cx, HLP : s6_lp _ _ _ ?ly ?S ?W ?regs ?mem ?md ?k ?acc ?c ?m ?t _,
    Hfrm : sa_frm0, Hnf : Z.of_nat _ + 1 = x_nf _, Hi : (_ < length _)%nat |- SRr _ _ {| cfg_ms := mkst _ _ _ _; cfg_model := ?mdv |} _ =>
  refine (HLT cx ly S W (ms_regs _) mem mdv k acc c m t HB Hfrm Hnf _ Hi _ _ _ _ _ _ _);
  [ apply (s6_lp_move cx ly S W regs mem md k acc c m t f _ mdv HLP HJ); s6_kg HS
  | s6_vreg HS (13%bv : bv 5); rewrite (U_atom _ 33 SHADOW_OFF) by s6_side; reflexivity
  | s6_vreg HS (18%bv : bv 5); unfold s6_SH2; rewrite (s6_U_shx _ 32 0x2000 m) by s6_side; reflexivity
  | s6_vreg HS (21%bv : bv 5); rewrite (U_atom _ 21 (256 * Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (22%bv : bv 5); rewrite (U_atom _ 22 (Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (24%bv : bv 5); rewrite (U_atom _ 24 (m + 32 + 256 * Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (26%bv : bv 5); rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) (-16)) by s6_side; lia
  | unfold s6_MI; rewrite s6_step; fold (s6_MI (x_pl cx) f i) ] end.
Ltac s6_out_call lo ed HRx HS HJ HMC :=
  rewrite (SIGP SS_m_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  replace (seg_af SS_m_refuse) with AF_m_refuse by (vm_compute; reflexivity);
  lazymatch goal with HB : lt_base _ _ ?cx, HLP : s6_lp _ _ _ ?ly ?S ?W ?regs ?mem ?md ?k ?acc ?c ?m ?t ?f,
    Hfrm : sa_frm0, Hnf : Z.of_nat _ + 1 = x_nf _, Hi : (?i < length _)%nat |- SRr _ _ {| cfg_ms := mkst _ _ _ _; cfg_model := ?mdv |} _ =>
  apply (s6_call lo ed f i cx ly S W _ mem mdv k acc c m t HRx ltac:(cbv [LO_S6RR LO_S6RM]; lia) eq_refl HB Hfrm Hnf);
  [ apply (s6_lp_move cx ly S W regs mem md k acc c m t f _ mdv HLP HJ); s6_kg HS
  | exact Hi
  | let P := fresh "P" in s6_prraw HS (1%bv : bv 5) P; rewrite P; cbn [sv_denot];
    match goal with H : img_env _ _ _ |- _ => rewrite (H 240%nat ltac:(unfold A_TEXT, A_LIM; lia)) end;
    reflexivity
  | s6_vreg HS (10%bv : bv 5); rewrite (U_atom _ 32 m) by s6_side; reflexivity
  | s6_vreg HS (11%bv : bv 5); rewrite U_SLit; reflexivity
  | s6_vreg HS (18%bv : bv 5); unfold s6_SH2; rewrite (s6_U_shx _ 32 0x2000 m) by s6_side; reflexivity
  | s6_vreg HS (21%bv : bv 5); rewrite (U_atom _ 21 (256 * Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (22%bv : bv 5); rewrite (U_atom _ 22 (Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (24%bv : bv 5); rewrite (U_atom _ 24 (m + 32 + 256 * Z.of_nat i)) by s6_side; reflexivity
  | s6_vreg HS (26%bv : bv 5); rewrite (U_atom_off _ 24 (m + 32 + 256 * Z.of_nat i) (-16)) by s6_side; lia
  | s6_vreg HS (25%bv : bv 5); rewrite (s6_U_shx _ 24 (-12) (m + 32 + 256 * Z.of_nat i)) by s6_side; f_equal; lia
  | s6_vreg HS (27%bv : bv 5); rewrite (s6_U_shx _ 24 0 (m + 32 + 256 * Z.of_nat i)) by s6_side; f_equal; lia
  | exact HMC
  | ] end.
(* ===================================== the head ===================================== *)
(* seqz(role - 4): the box test of c:300 *)
Lemma s6_U_box : forall E r, ew E 37 = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
  U E (SAlu ALU_SLTU (SOff 37 (-4)) (SLit 1)) = if r =? 4 then 1 else 0.
Proof.
intros E r E37 Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, E37, unsigned_lit_small by lia.
assert (Z1 : zcanon 1 = 1) by reflexivity. rewrite Z1.
assert (Hc : (zcanon (r + -4) <? 1) = (r =? 4)).
{ unfold zcanon, M64. destruct (Z.eqb_spec r 4) as [->|Hne]; [reflexivity|].
  destruct (Z_lt_le_dec r 4).
  - rewrite <- (Z.mod_unique (r + -4) (2 ^ 64) (-1) (r + -4 + 2 ^ 64)) by lia. apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. }
rewrite Hc. destruct (r =? 4); reflexivity.
Qed.
(* a branch on the box value, decided *)
Ltac s6_bx Hc E37 Hr :=
  rewrite branch_eq_U in Hc; repeat rewrite (U_SAlu _ ALU_AND) in Hc; repeat rewrite (U_SAlu _ ALU_OR) in Hc;
  rewrite (s6_U_box _ _ E37 Hr) in Hc; rewrite ?U_SLit in Hc.

Lemma s6_head : forall f i, S6_LT_stmt B MT f i -> S6_RA B MT LO_S6RR SegModel.ms_drop_role f i ->
  S6_RA B MT LO_S6RM SegModel.ms_drop_model f i -> S6_LH_stmt B MT f i.
Proof.
intros f i HLT HRR HRM cx ly S W regs mem md k acc c m t HB Hfrm Hnf HLP Hi R13 R18 R21 R22 R24 R26 HMC.
destruct (s6_nums cx ly S W regs mem md k acc c m t f HB HLP)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof HLP as ((HFR & _ & HBL & HBUD) & _ & _ & _ & R23 & Hsl & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & _ & _ & _ & _ & _ & _ & S200 & _).
set (M0 := s6_M0 (x_pl cx) f) in *.
set (mc := s6_MI (x_pl cx) f i) in *.
set (n := Z.of_nat (length (SegModel.mc_seg M0))).
pose proof (s6_mconf_len _ _ _ HMC) as HL32. unfold mc, s6_MI in HL32. rewrite s6_len in HL32. fold M0 in HL32.
assert (Hi31 : (i <= 31)%nat) by lia.
assert (Hn : 1 <= n <= 32) by (unfold n; lia).
pose proof (s6_rd_n _ _ _ HMC) as HN. unfold mc, s6_MI in HN. rewrite s6_len in HN. fold M0 n in HN.
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)) by (apply (s6_slot cx _ c m f); [exact Hsl | s6_in]).
assert (Hi' : (i < length (SegModel.mc_seg mc))%nat) by (unfold mc, s6_MI; rewrite s6_len; exact Hi).
destruct (s6_rd_role _ m mc i HMC Hi') as (Hr & RR16).
pose proof (s6_rd_role_set _ m mc i HMC Hi') as RR20.
pose proof (s6_rd_model_set _ m mc i HMC Hi') as RR32. clear Hi'.
set (r := SegModel.ms_role (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) in *.
destruct (s6_E_facts regs m n r) as (EEo & E32 & E33 & E34 & E35 & E37).
assert (E24 : ew (s6_E regs m n r) 24 = Z_to_bv 64 (m + 32 + 256 * Z.of_nat i))
  by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (U24 : bv_unsigned (ew (s6_E regs m n r) 24) = m + 32 + 256 * Z.of_nat i)
  by (rewrite E24; apply unsigned_lit_small; unfold S6_CMAX in *; lia).
assert (U9 : bv_unsigned (ew (s6_E regs m n r) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; unfold S6_CMIN in *; lia).
assert (U32 : bv_unsigned (ew (s6_E regs m n r) 32) = m) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Hr' : 0 <= r < 2 ^ 31) by lia.
destruct (s6_segL_ok (s6_E regs m n r) W mem md ly S m i (x_s1 cx) r
  (SegModel.ms_role_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d))
  (SegModel.ms_model_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d))
  HAR Hmin U24 U9 U32 E37 Hr' Hi31 ltac:(lia) ltac:(unfold S6_CMIN in *; lia) RR16 RR20 RR32) as (LOK & LD1 & LD2).
unfold S6_CMIN, S6_CMAX in *.
pose proof (s6_seed LO_S6H s6_srH s6_factsL
  [s6_segL (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)))
     (seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)))]
  W regs mem (x_s1 cx) m n r
  (s6_regs_okH regs m n r i ltac:(lia) ltac:(lia) Hi31 R24 R26 R18 R13)
  (s6_facts_okL regs m n r i (x_s1 cx) R9 ltac:(unfold S6_CMIN; lia) Hs1m R21 R22 R24 Hi31 Hm4
    ltac:(unfold S6_CMAX; lia) Hm16 Hn Hr')
  ltac:(destruct (SegModel.ms_role_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)),
          (SegModel.ms_model_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)); vm_compute; reflexivity)
  ltac:(constructor; [exact LOK | constructor])
  ltac:(intros rg [<- | []]; exact (conj LD1 LD2))
  ltac:(cbn; tauto) R9 ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) ltac:(lia)
  ltac:(lia) S192 S200 S208 S216 HN) as HS.
pose proof (s6_shok B ly S W mem md regs m n r i HAR Hmin Hi31 R24) as SHOK.
assert (HEI : img_env VAL A_LIM (s6_E regs m n r)) by (unfold s6_E; apply Eimg_env).
remember (s6_E regs m n r) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = Z_to_bv 64 (256 * Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
unfold cfg_at.
destruct (SegModel.ms_role_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) eqn:ERS;
  destruct (SegModel.ms_model_set (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) eqn:EMS.
- (* role_set 1, model_set 1: a2 = box; box = 0 drops the model (call at 0x85424), box = 1 goes to the latch *)
  paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
  s6_mdv mdv1. s6_ro HF EM1. clear HF HFr HG. rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK s6_span.
  + assert (HBX : (r =? 4) = false)
      by (s6_bx Hc E37 Hr'; destruct (r =? 4); [vm_compute in Hc; discriminate | reflexivity]).
    paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
    s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM, EM1 in *.
    s6_out_call LO_S6RM SegModel.ms_drop_model HRM HS HJ HMC.
    fold mc. rewrite (s6_seg_11 mc i ERS EMS).
    replace (SegModel.ms_role (nth i (SegModel.mc_seg mc) SegModel.mseg_d) =? 4) with false by (symmetry; exact HBX).
    reflexivity.
  + assert (HBX : (r =? 4) = true)
      by (s6_bx Hc E37 Hr'; destruct (r =? 4); [reflexivity | vm_compute in Hc; discriminate]).
    clear Hc. paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
    s6_mdv mdv2. s6_ro HF EM2. clear HF HFr HG. rename ms into ms2.
    psrr_branch_tok RUN BR HS SHOK s6_span.
    * paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6T. { awr_ok_tac. }
      s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM, EM2, EM1 in *.
      s6_out_latch HS HJ.
      fold mc. rewrite (s6_seg_11 mc i ERS EMS).
      replace (SegModel.ms_role (nth i (SegModel.mc_seg mc) SegModel.mseg_d) =? 4) with true by (symmetry; exact HBX).
      exact HMC.
    * exfalso. s6_bx Hc E37 Hr'. rewrite HBX in Hc. vm_compute in Hc. discriminate.
- (* role_set 1, model_set 0: a2 = 1; box = 1 drops the role (call at 0x853f0), box = 0 goes to the latch *)
  paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
  s6_mdv mdv1. s6_ro HF EM1. clear HF HFr HG. rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK s6_span.
  + exfalso. s6_bx Hc E37 Hr'. destruct (r =? 4); vm_compute in Hc; discriminate.
  + clear Hc. paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
    s6_mdv mdv2. s6_ro HF EM2. clear HF HFr HG. rename ms into ms2.
    psrr_branch_tok RUN BR HS SHOK s6_span.
    * assert (HBX : (r =? 4) = false)
        by (s6_bx Hc E37 Hr'; destruct (r =? 4); [vm_compute in Hc; discriminate | reflexivity]).
      paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6T. { awr_ok_tac. }
      s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM, EM2, EM1 in *.
      s6_out_latch HS HJ.
      fold mc. rewrite (s6_seg_10 mc i ERS EMS).
      replace (SegModel.ms_role (nth i (SegModel.mc_seg mc) SegModel.mseg_d) =? 4) with false by (symmetry; exact HBX).
      exact HMC.
    * assert (HBX : (r =? 4) = true)
        by (s6_bx Hc E37 Hr'; destruct (r =? 4); [reflexivity | vm_compute in Hc; discriminate]).
      paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
      s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM, EM2, EM1 in *.
      s6_out_call LO_S6RR SegModel.ms_drop_role HRR HS HJ HMC.
      fold mc. rewrite (s6_seg_10 mc i ERS EMS).
      replace (SegModel.ms_role (nth i (SegModel.mc_seg mc) SegModel.mseg_d) =? 4) with true by (symmetry; exact HBX).
      reflexivity.
- (* role_set 0, model_set 1: the model dropped (call at 0x85424) *)
  paj_run_tok RUN HS HJ SHOK s6_span. { awr_ok_tac. }
  s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM in *.
  s6_out_call LO_S6RM SegModel.ms_drop_model HRM HS HJ HMC.
  exact (s6_seg_01 mc i ERS EMS).
- (* role_set 0, model_set 0: nothing, to the latch *)
  paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6T. { awr_ok_tac. }
  s6_mdv mdv. s6_ro HF EM. clear HF HFr HG. pmkst HS. rewrite EM in *.
  s6_out_latch HS HJ.
  fold mc. rewrite (s6_seg_00 mc i ERS EMS). exact HMC.
Qed.

(* ===================================== the entry K85338 ===================================== *)
Lemma s6_chunk_word : forall (W : world SEGS) E ss (ms : machine_state) idx rg p off e a v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) idx = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  U E e = v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (a + off) = Some v.
Proof.
intros W E ss ms idx rg p off e a v HS Hi Hb Hc Ha HU Hv.
assert (He : sv_denot E e = Z_to_bv 64 v) by (apply bv_eq; rewrite unsigned_lit_small by lia; exact HU).
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) idx rg p off 8 e a v HS Hi Hb Hc Ha He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV.
exact (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms) (a + off) v HV Hv).
Qed.
Ltac s6_w HS idx off :=
  let HSo := fresh "HSo" in pose proof HS as HSo; try unfold st_ok_pi in HSo;
  lazymatch type of HSo with st_ok _ _ ?ss _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss) idx) in
    lazymatch l with Some ?rg =>
      let cs := eval vm_compute in (YP09.r_chunks rg) in
      lazymatch cs with context [YP09.mkChunk off (CVal 8 ?e)] =>
        apply (s6_chunk_word _ _ ss _ idx rg 9%nat off e _ _ HSo);
        [vm_compute; reflexivity | reflexivity | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | | | ]
      end end end.
Lemma s6_mconf_xfer : forall (rd rd' : reader) m mc, sa_mconf rd m mc ->
  (forall x, m <= x < m + 9236 -> rd' x = rd x) -> sa_mconf rd' m mc.
Proof.
intros rd rd' m mc (bs & HB & E) HK. exists bs. split; [|exact E].
pose proof E as (L & _). unfold seg_spec.SEG_M_SIZE in L.
intros j Hj. rewrite HK by lia. exact (HB j Hj).
Qed.
Lemma s6_LTL_off : forall cx c m o v, In (o, v) (LT_L cx c m) -> o + 8 <= 128 \/ 144 <= o.
Proof.
intros cx c m o v Hin.
assert (HO : forallb (fun ov => (fst ov + 8 <=? 128) || (144 <=? fst ov)) (LT_L cx c m) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HO (o, v) Hin) as Ho. cbn [fst] in Ho.
apply orb_prop in Ho as [Ho | Ho]; [left; apply Z.leb_le in Ho; exact Ho | right; apply Z.leb_le in Ho; exact Ho].
Qed.
(* the entry runs: the frame window 128 .. 144 based at s1 (atom 9) is the only write window *)
Ltac s6_awrE U9 :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | lazymatch goal with cx : lcx |- _ =>
        apply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
        [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] end ].
Ltac s6_keepE U9 m0 KEEP :=
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m1), cx : lcx, W : world _ |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 128 <= a < x_s1 cx + 144) ->
    rdW W m1 a = rdW W m0 a)
  by (intros a Ha Hn'; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => x_s1 cx + 128 <= a < x_s1 cx + 144) Hfr);
      [ intros b wlo whi a' Hin Hrr; cbn [windows map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
        repeat (destruct Hin as [Hq0 | Hin];
          [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn' ]) end.

(* ---- K85338 .. 0x8536c: the trap 0x85338 (s5 = M & 3 = 0: not taken), 136(s1) := f + 1, 128(s1) := (m + 0x2000)
   >> 3, s2 := SH(m + 0x2000), check 9 (m->n's shadow), m->n, blez to K854d4 (m->n = 0: m_cross of no segment), else
   s5 = s6 = 0, s8 = m + 0x20, s10 = m + 0x10 and the head of turn 0 ---- *)
Lemma s6_entry : forall f, S6_LH_stmt B MT f 0 -> LT_K854d4_stmt B MT f -> LT_K85338_stmt B MT f.
Proof.
intros f HLH HX cx ly S W regs mem md k acc c m t HB Hfrm Hnf HC HHc HHm HHt R21 R23 R25 R26 HSL HRC HMC HST HCNT.
assert (HLP0 : s6_lp0 B MT cx ly S W regs mem md k acc c m t f)
  by exact (conj HC (conj HHc (conj HHm (conj HHt (conj R23 (conj HRC (conj HST HCNT))))))).
destruct (s6_nums0 cx ly S W regs mem md k acc c m t f HB HLP0)
  as (HAR & Hmin & Hm4 & Hmc & Hm16 & R9 & Hsp & Hsp16 & Hs1 & Hs1m).
pose proof alloc_ceiling_value as [HAC _].
pose proof HC as (HFR & _ & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & _ & _ & _ & _ & _ & _ & S200 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HBUD as (_ & _ & _ & B4 & _).
set (M0 := s6_M0 (x_pl cx) f).
change (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) with M0 in HMC.
set (n := Z.of_nat (length (SegModel.mc_seg M0))).
pose proof (s6_mconf_len _ _ _ HMC) as HL32.
assert (Hn : 0 <= n <= 32) by (unfold n; lia).
pose proof (s6_rd_n _ _ _ HMC) as HN. fold n in HN.
assert (HK : forall o v, In (o, v) (LT_L cx c m) -> rdword (rdW W mem) (x_s1 cx + o) = Some v)
  by (intros o v Hin; apply HSL; apply in_or_app; left; exact Hin).
assert (S72 : rdword (rdW W mem) (x_s1 cx + 72) = Some (m + 0x20))
  by (apply HK; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S80 : rdword (rdW W mem) (x_s1 cx + 80) = Some (m + 0x10))
  by (apply HK; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m)
  by (apply HK; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m))
  by (apply HK; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HK; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
destruct (s6_E_facts regs m n 0) as (EEo & E32 & E33 & E34 & E35 & _).
assert (U9 : bv_unsigned (ew (s6_E regs m n 0) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; unfold S6_CMIN in *; lia).
unfold S6_CMIN, S6_CMAX in *.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof (s6_eseed W regs mem (x_s1 cx) m n (s6_regs_okE regs m n 0 ltac:(lia) ltac:(lia) R26 R21)
  (s6_facts_okE regs m n 0 (x_s1 cx) R9 ltac:(unfold S6_CMIN; lia) Hs1m Hm4 ltac:(unfold S6_CMAX; lia) Hm16 Hn)
  R9 ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) ltac:(lia) ltac:(lia) (fun a Ha => Hpres a ltac:(lia))
  S72 S80 S192 S200 S208 S216 HN) as HS.
pose proof (s6_shokE B ly S W mem md regs m n 0 HAR Hmin) as SHOK.
assert (HEI : img_env VAL A_LIM (s6_E regs m n 0)) by (unfold s6_E; apply Eimg_env).
remember (s6_E regs m n 0) as E eqn:HE. clear HE.
assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat f + 1)) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
unfold cfg_at.
(* the two stored words, as the runs' chunks hold them *)
assert (UW128 : U E (SAlu ALU_SRL (SOff 32 8192) (SLit 3)) = (m + seg_spec.MC_N) / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, E32, unsigned_lit_small by lia.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_pos (m + 0x2000) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (m + 0x2000) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
  rewrite (zcanon_small (m + 8192)) by lia. rewrite zcanon_small by lia. unfold seg_spec.MC_N. reflexivity. }
assert (RW128 : 0 <= (m + seg_spec.MC_N) / 8 < 2 ^ 64).
{ pose proof (Z.div_pos (m + seg_spec.MC_N) 8 ltac:(unfold seg_spec.MC_N; lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (m + seg_spec.MC_N) 8 (m + seg_spec.MC_N) ltac:(lia) ltac:(unfold seg_spec.MC_N; lia)).
  unfold seg_spec.MC_N in *. lia. }
assert (UW136 : U E (SOff 25 0) = Z.of_nat f + 1).
{ pose proof (s6_nfiles_range (x_pl cx)) as Hn4. unfold x_nf in Hnf.
  rewrite (U_atom _ 25 (Z.of_nat f + 1)) by s6_side. reflexivity. }
assert (RW136 : 0 <= Z.of_nat f + 1 < 2 ^ 64)
  by (pose proof (s6_nfiles_range (x_pl cx)) as Hn4; unfold x_nf in Hnf; lia).
(* the loop facts at a later state whose only moved bytes are the two stored words *)
assert (HPOST : forall (regs2 : bvmap 5 word) mem2 md2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 128 <= a < x_s1 cx + 144) -> rdW W mem2 a = rdW W mem a) ->
  rdword (rdW W mem2) (x_s1 cx + 128) = Some ((m + seg_spec.MC_N) / 8) ->
  rdword (rdW W mem2) (x_s1 cx + 136) = Some (Z.of_nat f + 1) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 23 = getr regs 23 ->
  s6_lp B MT cx ly S W regs2 mem2 md2 k acc c m t f /\ sa_mconf (rdW W mem2) m M0).
{ intros regs2 mem2 md2 KP Q128 Q136 HJ2 P2 P3 P4 P8 P9 P23. split.
  - apply s6_lp_of0.
    + apply (s6_lp_gen cx ly S W regs mem md k acc c m t f ly S W regs2 mem2 md2 HB HLP0 HJ2
        (Permutation_refl _) B4 P2 P3 P4 P8 P9 P23).
      intros a Ha _ _ H3. exact (KP a Ha H3).
    + intros o v Hin. unfold s6_slots in Hin. apply in_app_or in Hin as [Hin | Hin].
      * pose proof (s6_LTL_off cx c m o v Hin) as Ho.
        assert (Ho2 : 16 <= o <= 216)
          by (apply (s6_slots_off cx c m f o v); unfold s6_slots; apply in_or_app; left; exact Hin).
        rewrite (rdword_ext (rdW W mem) (rdW W mem2) (x_s1 cx + o)); [exact (HK o v Hin)|].
        intros j Hj. apply KP; lia.
      * cbn [In] in Hin.
        destruct Hin as [Hq | [Hq | Hin]]; [injection Hq as <- <-; exact Q128 | injection Hq as <- <-; exact Q136 |].
        assert (Hin' : In (o, v) (LT_L cx c m ++
            [(144, x_at cx f + x_np cx f); (152, x_np cx f); (160, x_n1 cx f);
             (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))])) by (apply in_or_app; right; exact Hin).
        assert (Ho : 144 <= o <= 176)
          by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia |]); destruct Hin).
        rewrite (rdword_ext (rdW W mem) (rdW W mem2) (x_s1 cx + o)); [exact (HSL o v Hin')|].
        intros j Hj. apply KP; lia.
  - apply (s6_mconf_xfer (rdW W mem)); [exact HMC | intros x Hx; apply KP; lia]. }
(* 0x85338 .. 0x8535c: the stores of 136 and 128, check 9, m->n *)
paj_run_tok RUN HS HJ SHOK s6_span.
{ s6_awrE U9. }
s6_mdv mdv1.
s6_keepE U9 mem KEEP1.
rename ms into ms1.
assert (U0 : U E (SLit 0) = 0) by reflexivity.
assert (U35 : U E (SOff 35 0) = n) by (rewrite (U_atom _ 35 n) by s6_side; reflexivity).
psrr_branch_tok RUN BR HS SHOK s6_span.
- (* m->n <= 0: no segment, to K854d4 *)
  assert (Hn0 : n = 0).
  { rewrite s6_bge_U, U0, U35 in Hc by (rewrite ?U0, ?U35; lia).
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_K854d4.
  { s6_awrE U9. }
  s6_mdv mdv. s6_keepE U9 (ms_mem ms1) KEEP2.
  assert (Q128 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 128) = Some ((m + seg_spec.MC_N) / 8))
    by (s6_w HS 0%nat 128; [exact U9 | exact UW128 | exact RW128]).
  assert (Q136 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 136) = Some (Z.of_nat f + 1))
    by (s6_w HS 0%nat 136; [exact U9 | exact UW136 | exact RW136]).
  destruct (HPOST (ms_regs ms) (ms_mem ms) mdv
    (fun a Ha Hn' => eq_trans (KEEP2 a Ha Hn') (KEEP1 a Ha Hn')) Q128 Q136 HJ) as (HLP2 & HMC2);
    try s6_kg HS.
  pmkst HS.
  destruct HLP2 as (HC2 & Hc2 & Hm2 & Ht2 & R23' & Hsl2 & Hrc2 & Hst2 & Hcnt2).
  refine (HX cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m t HB Hfrm Hnf HC2 Hc2 Hm2 Ht2 _ R23' Hsl2 Hrc2 _ Hst2 _).
  + s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
  + change (sa_mconf (rdW W (ms_mem ms)) m (SegModel.m_cross M0)).
    rewrite s6_all. replace (length (SegModel.mc_seg M0)) with 0%nat by (unfold n in Hn0; lia). exact HMC2.
  + apply s6_cnt_cross; [exact Hcnt2 | exact (proj2 (s6_M0_refused (x_pl cx) f)) | exact HL32].
- (* m->n > 0: to the head of turn 0 *)
  assert (Hn1 : 1 <= n).
  { rewrite s6_bge_U, U0, U35 in Hc by (rewrite ?U0, ?U35; lia).
    apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK s6_span LO_S6H.
  { s6_awrE U9. }
  s6_mdv mdv. s6_keepE U9 (ms_mem ms1) KEEP2.
  assert (Q128 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 128) = Some ((m + seg_spec.MC_N) / 8))
    by (s6_w HS 0%nat 128; [exact U9 | exact UW128 | exact RW128]).
  assert (Q136 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 136) = Some (Z.of_nat f + 1))
    by (s6_w HS 0%nat 136; [exact U9 | exact UW136 | exact RW136]).
  destruct (HPOST (ms_regs ms) (ms_mem ms) mdv
    (fun a Ha Hn' => eq_trans (KEEP2 a Ha Hn') (KEEP1 a Ha Hn')) Q128 Q136 HJ) as (HLP2 & HMC2);
    try s6_kg HS.
  pmkst HS.
  refine (HLH cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m t HB Hfrm Hnf HLP2 _ _ _ _ _ _ _ HMC2).
  + unfold n, M0 in Hn1. lia.
  + s6_vreg HS (13%bv : bv 5). rewrite (U_atom _ 33 SHADOW_OFF) by s6_side. reflexivity.
  + s6_vreg HS (18%bv : bv 5). unfold s6_SH2. rewrite (s6_U_shx _ 32 0x2000 m) by s6_side. reflexivity.
  + s6_vreg HS (21%bv : bv 5). rewrite U_SLit. reflexivity.
  + s6_vreg HS (22%bv : bv 5). rewrite U_SLit. reflexivity.
  + s6_vreg HS (24%bv : bv 5). rewrite (U_atom_off _ 32 m 0x20) by s6_side. lia.
  + s6_vreg HS (26%bv : bv 5). rewrite (U_atom_off _ 32 m 0x10) by s6_side. lia.
Qed.
End ep.
End fp.
End dp.

(* ===================================== the segment ===================================== *)
(* the loop's points of every turn, by downward induction on the turn (i < m->n <= 32), each at every FP state: the
   latch of turn i from the head of turn i + 1 and K854d4, the two returns from the latch, the head from the three *)
Section dc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fc.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section ec.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog.
Hypothesis MRF : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.

Lemma s6_heads : forall f, LTA_K854d4 B MT f -> forall i, S6_LHA B MT f i.
Proof.
intros f HX.
assert (H : forall d i, (32 - d <= i)%nat -> S6_LHA B MT f i).
{ induction d as [|d IH]; intros i Hi fx1.
  - intros cx ly S W regs mem md k acc c m t HB Hfrm Hnf HLP Hlt R13 R18 R21 R22 R24 R26 HMC. exfalso.
    pose proof (s6_mconf_len _ _ _ HMC) as HL. unfold s6_MI in HL. rewrite s6_len in HL. lia.
  - destruct (Nat.le_gt_cases (32 - d) i) as [Hle | Hgt]; [exact (IH i Hle fx1)|].
    assert (HN : S6_LHA B MT f (Datatypes.S i)) by (apply IH; lia).
    pose proof (fun fx2 : YK11.FPState => s6_latch (fx := fx2) B MT f i HN HX) as HLT.
    exact (s6_head (fx := fx1) B MT MTFL SIGP MRF f i (HLT fx1)
      (fun fx2 => s6_retR (fx := fx2) B MT f i (HLT fx2))
      (fun fx2 => s6_retM (fx := fx2) B MT f i (HLT fx2))). }
intros i. apply (H 32%nat i). lia.
Qed.

(* S06 0x85338 .. 0x854d0: the inlined m_cross loop with its m_refuse calls *)
Theorem lt_seg_S06 : lt_seg_S06_stmt B MT.
Proof.
unfold lt_seg_S06_stmt. intros f HX.
exact (s6_entry B MT f (s6_heads f HX 0%nat fx) (HX fx)).
Qed.
End ec.
End fc.
End dc.
