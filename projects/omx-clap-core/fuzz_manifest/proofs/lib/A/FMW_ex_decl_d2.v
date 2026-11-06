(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 373 of its 419 lines of code are new or changed and 221 lines of the source are left out. *)
(* G4.ExDecl.DeclD2B: expected's name loop at D2 (0x813dc..0x81430, fuzz_manifest.c:149) on fm.asan: dseg_D2.
   One iteration from D2 at j: the byte c at p1 + j (a1) is decided on its value alone (a closed valuation over the
   256 byte values): a name byte loads the next byte (checked at a0 + s5 + 1, loaded at 1(s4 + s5), both
   text + p1 + j + 1, one atom by the alias fact) and re-enters D2 at j + 1; NUL or a space exits through 0x814d0 to
   EX_L at i + 1 (decl = DNone); ':' goes to D3 with p2 = p1 + j. The loop closes by strong induction on
   |text| - (p1 + j). Pattern after FMW_plain.v (pl_loop, pl_cls_*, tactics) and G3's FMW_rd_pp.v (the alias fact,
   the closed byte decisions pp_nok_all, a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the symbolic state at D2 (0x813dc): registers are their own atoms (sr_atoms); a5 = ':' and a6 = EX_MASK1
   pinned as literals, s4 (register 20) pinned to a0's atom 10 (both text + p1); s9 (register 25) holds the shadow
   base; a1 (atom 11) = the byte at p1 + j. Extra atoms: 32 = text + p1 + j (a0 + s5 by the alias), 33 = the next
   byte (at 32 + 1, read only on the name path), 34 = text (the F + 0x58 slot, read by the exit 0x814d0) ---- *)
Definition D2_Bx : sv := SOff 25 0.
Definition D2_Bspan : Z * Z := EX_Bspan.
Definition d2_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 15%bv (SLit 58)) 16%bv (SLit EX_MASK1)) 20%bv (SOff 10 0).
Definition d2_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x58 0x60 0x58 0x58 [YP09.mkChunk 0x58 (CVal 8 (SOff 34 0))].
Definition d2_byte : YP09.region :=
  YP09.mkRegion (Some 32%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition d2_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 255 0); (25%nat, mkAF FW_SB FW_SB 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 16) 0); (33%nat, mkAF 0 255 0)] []
    [(SAlu ALU_ADD (SOff 10 0) (SOff 21 0), SOff 32 0)].
(* the name case (the byte at p1 + j is a name byte, so the next one is in the string) and the exit case *)
Definition ss_D2n : sstate := mkSS EX_D2 d2_regs [d2_frame; d2_byte] None d2_facts.
Definition ss_D2x : sstate := mkSS EX_D2 d2_regs [d2_frame] None d2_facts.
Definition SH_D2n : list shent := [mkSHE 32 1 2].
Definition SH_D2x : list shent := [].
Definition d2_extra (q cn t : Z) : list word := [Z_to_bv 64 q; Z_to_bv 64 cn; Z_to_bv 64 t].

(* ---- the three class branches (0x813e0 bltu a5, a1; 0x813ec bnez (mask >> a1) & 1; 0x813f0 beq a1, a5) as the
   walk stops at them, decided on the byte c alone: a closed valuation with c at atom 11 ---- *)
Definition d2_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition d2_Ec (c : Z) : env := ewset d2_E00 11 (Z_to_bv 64 c).
Definition d2_D (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (d2_Ec c) a) (sv_denot (d2_Ec c) b).
Definition d2_c255 : sv := SAlu ALU_AND (SOff 11 0) (SLit 255).
Definition d2_msk : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit EX_MASK1) d2_c255) (SLit 1).
Definition d2_dgt (c : Z) : bool := d2_D BC_LTU (SLit 58) d2_c255 c.
Definition d2_dmk (c : Z) : bool := d2_D BC_NE d2_msk (SLit 0) c.
Definition d2_deq (c : Z) : bool := d2_D BC_EQ d2_c255 (SLit 58) c.
Definition d2_cls (c : Z) : bool :=
  implb (d2_dgt c) (ManifestModel.name_ok c) &&
  implb (negb (d2_dgt c) && d2_dmk c) (negb (ManifestModel.name_ok c) && negb (c =? 58)) &&
  implb (negb (d2_dgt c) && negb (d2_dmk c) && d2_deq c) (c =? 58) &&
  implb (negb (d2_dgt c) && negb (d2_dmk c) && negb (d2_deq c)) (ManifestModel.name_ok c).
Lemma d2_cls_all : forall c, 0 <= c < 256 -> d2_cls c = true.
Proof.
  intros c Hc.
  assert (H : forallb d2_cls (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Lemma d2_D_of : forall E c cnd a b, ew E 11 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 11) a = true -> sv_atoms_in (Nat.eqb 11) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = d2_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold d2_D.
  assert (HA : env_agree_on (Nat.eqb 11) E (d2_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold d2_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
Ltac d2_cls_tac c Hc :=
  intros; pose proof (d2_cls_all c Hc) as X; unfold d2_cls in X;
  repeat match goal with H : d2_dgt c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : d2_dmk c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : d2_deq c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X.
Lemma d2_c_gt : forall c, 0 <= c < 256 -> d2_dgt c = true -> ManifestModel.name_ok c = true.
Proof. intros c Hc. d2_cls_tac c Hc. destruct (ManifestModel.name_ok c); [reflexivity | discriminate X]. Qed.
Lemma d2_c_mk : forall c, 0 <= c < 256 -> d2_dgt c = false -> d2_dmk c = true ->
  ManifestModel.name_ok c = false /\ c <> 58.
Proof.
  intros c Hc. d2_cls_tac c Hc.
  destruct (ManifestModel.name_ok c); [discriminate X|]. split; [reflexivity|].
  destruct (c =? 58) eqn:E; [discriminate X | apply Z.eqb_neq in E; exact E].
Qed.
Lemma d2_c_eq : forall c, 0 <= c < 256 -> d2_dgt c = false -> d2_dmk c = false -> d2_deq c = true -> c = 58.
Proof. intros c Hc. d2_cls_tac c Hc. destruct (c =? 58) eqn:E; [apply Z.eqb_eq in E; exact E | discriminate X]. Qed.
Lemma d2_c_nm : forall c, 0 <= c < 256 -> d2_dgt c = false -> d2_dmk c = false -> d2_deq c = false ->
  ManifestModel.name_ok c = true.
Proof. intros c Hc. d2_cls_tac c Hc. destruct (ManifestModel.name_ok c); [reflexivity | discriminate X]. Qed.

(* ---- the walk's tactics (after FMW_plain.v fw_reg / pl_av / pl_dec / pl_mk / pl_g) ---- *)
Ltac d2_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac d2_g HS :=
  lazymatch goal with |- getr _ ?r = _ => d2_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac d2_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
Ltac d2_dec HS E11 c Hc :=
  let H11 := fresh "H11" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H11 : ew Ex 11 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E11) end;
  erewrite (d2_D_of _ _ _ _ _ H11) in Hc by reflexivity; clear H11.
Ltac d2_mkst HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma d2_w64_add : forall x k, Z_to_bv 64 (bv_unsigned (w64 x) + k) = w64 (x + k).
Proof.
  intros x k. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- the entry lemmas: st_ok of ss_D2n / ss_D2x from dat_D2 ---- *)
Lemma d2_regs_ok : forall regs ex, getr regs 15 = w64 58 -> getr regs 16 = w64 EX_MASK1 ->
  getr regs 20 = getr regs 10 -> regs_ok (Ereg regs ex) d2_regs regs.
Proof.
  intros regs ex R15 R16 R20. unfold d2_regs.
  repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..]; cbn [sv_denot];
    first [ exact R15 | exact R16
          | rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_nat regs ex 10 10%bv eq_refl); exact R20 ].
Qed.

Lemma d2_facts_ok : forall E F c q cn,
  bv_unsigned (ew E 2) = F -> 2 ^ 46 <= F <= 2 ^ 47 -> F mod 16 = 0 ->
  bv_unsigned (ew E 11) = c -> 0 <= c < 256 -> bv_unsigned (ew E 25) = SHADOW_OFF ->
  bv_unsigned (ew E 32) = q -> 4096 <= q <= 2 ^ 47 - 16 -> bv_unsigned (ew E 33) = cn -> 0 <= cn < 256 ->
  bv_unsigned (ew E 10) + bv_unsigned (ew E 21) = q ->
  facts_ok E d2_facts.
Proof.
  intros E F c q cn U2 HF HF16 U11 Hc U25 U32 Hq U33 Hcn Ua.
  split; [|split; [exact I|]].
  - cbn [f_atoms atoms_ok d2_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U11, U25, U32, U33. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold FW_SB, SHADOW_OFF. repeat split; lia.
  - cbn [f_alias d2_facts alias_ok]. split; [|exact I]. apply U_inj.
    pose proof (bv_unsigned_in_range 64 (ew E 10)) as R10. pose proof (bv_unsigned_in_range 64 (ew E 21)) as R21.
    change (bv_modulus 64) with (2 ^ 64) in R10, R21.
    rewrite (U_add_off_atom E 10 0 21 0) by (unfold M64; lia).
    rewrite U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma d2_frame_ok : forall E m F t, bv_unsigned (ew E 2) = F -> ew E 34 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 ->
  0 <= F -> F + 0x60 <= 2 ^ 64 -> val_mem tfibsegs m (F + 0x58) 8 t -> region_ok tfibsegs E m d2_frame.
Proof.
  intros E m F t U2 E34 Ht HF0 HF1 V58. unfold region_ok, d2_frame.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ F 0x58 8 (SOff 34 0) t);
    [cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact V58].
Qed.

Lemma d2_byte_ok : forall E m q cn, bv_unsigned (ew E 32) = q -> ew E 33 = Z_to_bv 64 cn -> 0 <= cn < 256 ->
  0 <= q -> q + 2 <= 2 ^ 64 -> val_mem tfibsegs m (q + 1) 1 cn -> region_ok tfibsegs E m d2_byte.
Proof.
  intros E m q cn U32 E33 Hcn Hq0 Hq1 Vn. unfold region_ok, d2_byte.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ q 1 1 (SOff 33 0) cn);
    [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact Vn].
Qed.

(* the entry state of one iteration: the name case carries the next byte (text + p1 + j + 1, in the string because
   the byte at p1 + j is not the NUL) and its shadow entry; the exit case only the F + 0x58 slot. Atom 33 is the
   byte at p1 + j + 1 in both (0 past the NUL, unused there) *)
Lemma d2_entry : forall cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3,
  dat_D2 B cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 -> (p1 + j <= length (cx_tb cx))%nat ->
  st_ok tfibsegs (Ereg regs3 (d2_extra (cx_t cx + Z.of_nat (p1 + j)) (MM.byte_at (cx_tb cx) (p1 + S j)) (cx_t cx)))
    (if MM.name_ok (MM.byte_at (cx_tb cx) (p1 + j)) then ss_D2n else ss_D2x)
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D2) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs D2_Bx (if MM.name_ok (MM.byte_at (cx_tb cx) (p1 + j)) then SH_D2n else SH_D2x)
    (Ereg regs3 (d2_extra (cx_t cx + Z.of_nat (p1 + j)) (MM.byte_at (cx_tb cx) (p1 + S j)) (cx_t cx)))
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D2) mem3 (seg_rom tfibsegs)))).
Proof.
  intros cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 HD Hpj.
  destruct HD as ((HB & HC & HSL & _ & _ & _ & _ & _) & _ & _ & R11 & R10 & R20 & _ & R21 & _ & _ & _ & _ & _ & _
    & R15 & R16).
  pose proof HC as (_ & _ & _ & R2 & _ & _ & R25 & _ & _ & Ct & _).
  pose proof Ct as (_ & _ & _ & _ & Ham & HRA & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HSL as (_ & _ & _ & _ & _ & _ & _ & S58 & _).
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (p1 + j) Ct Hpj) as (_ & Hc).
  set (c := MM.byte_at (cx_tb cx) (p1 + j)) in *.
  set (cn := MM.byte_at (cx_tb cx) (p1 + S j)) in *.
  assert (Hcn : 0 <= cn < 256).
  { destruct (Nat.le_gt_cases (p1 + S j) (length (cx_tb cx))) as [H|H].
    - exact (proj2 (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (p1 + S j) Ct H)).
    - assert (E0 : cn = 0) by (unfold cn; apply expected_m.byte_at_ge; lia). rewrite E0. lia. }
  set (q := cx_t cx + Z.of_nat (p1 + j)) in *.
  assert (Eq : q = cx_t cx + Z.of_nat (p1 + j)) by reflexivity.
  set (E := Ereg regs3 (d2_extra q cn (cx_t cx))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
    by (intros n r Hn; apply ew_Ereg_nat; exact Hn).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = cx_t cx + Z.of_nat p1)
    by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E 11) = c)
    by (rewrite (EE 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = Z.of_nat j)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 q) by exact (ew_Ereg_extra regs3 _ 0).
  assert (E33 : ew E 33 = Z_to_bv 64 cn) by exact (ew_Ereg_extra regs3 _ 1).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx)) by exact (ew_Ereg_extra regs3 _ 2).
  assert (U32 : bv_unsigned (ew E 32) = q) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = cn) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HR : regs_ok E d2_regs regs3)
    by (apply d2_regs_ok; [exact R15 | exact R16 | rewrite R20, R10; reflexivity]).
  assert (HG : facts_ok E d2_facts) by (apply (d2_facts_ok E (cx_F cx) c q cn); first [assumption | lia]).
  assert (HFR : region_ok tfibsegs E (mrestrict (w_H W3) mem3) d2_frame)
    by (apply (d2_frame_ok E _ (cx_F cx) (cx_t cx) U2 E34); first [exact S58 | lia]).
  rewrite restrict_mkst_fx.
  destruct (MM.name_ok c) eqn:Hnm; cbv beta iota.
  - assert (Hlt : (p1 + j < length (cx_tb cx))%nat).
    { destruct (Nat.lt_ge_cases (p1 + j) (length (cx_tb cx))) as [H|H]; [exact H|]. exfalso.
      assert (E0 : c = 0) by (unfold c; apply expected_m.byte_at_ge; exact H). rewrite E0 in Hnm. discriminate Hnm. }
    pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (p1 + S j) Ct ltac:(lia)) as (Vn & _).
    split.
    + unfold ss_D2n. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d2_extra q cn (cx_t cx))) with E.
      * exact HR.
      * vm_compute. reflexivity.
      * apply Forall_cons; [exact HFR|]. apply Forall_cons; [|apply Forall_nil].
        apply (d2_byte_ok E _ q cn U32 E33 Hcn); [lia | lia |].
        replace (q + 1) with (cx_t cx + Z.of_nat (p1 + S j)) by lia. exact Vn.
      * apply pairwise_disjoint_of_extents. unfold d2_frame, d2_byte, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
      * exact HG.
    + constructor; [|constructor].
      apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E D2_Bx 32 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
        q 1 2 HRA).
      * unfold D2_Bx. apply U_atom; [rewrite (EE 25%nat 25%bv eq_refl); exact R25 | unfold SHADOW_OFF; lia].
      * apply U_atom; [exact E32 | lia].
      * lia.
      * lia.
      * intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
  - split; [|constructor].
    unfold ss_D2x. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d2_extra q cn (cx_t cx))) with E.
    + exact HR.
    + vm_compute. reflexivity.
    + apply Forall_cons; [exact HFR | apply Forall_nil].
    + apply pairwise_disjoint_of_extents. unfold d2_frame, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
    + exact HG.
Qed.

(* a run that writes nothing keeps the cut's common facts *)
Lemma d2_ddcom_kept : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dd_com B cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 22 = getr regs3 22 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 8 = getr regs3 8 ->
  dd_com B cx i d f ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi) HJ AV
    Q2 Q3 Q4 Q25 Q22 Q18 Q8.
  pose proof (dd_bounds B cx HB) as (_ & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _). assert (FS : STK_expected = 8432) by reflexivity.
  split; [exact HB|].
  split; [apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ); try assumption;
          intros a Ha _ _ _; exact (AV a Ha)|].
  split; [apply (dd_slots_kept B cx W3 mem3 mem4 d HB HSL); intros a Ha; apply AV; lia|].
  split; [rewrite Q22; exact R22|]. split; [rewrite Q18; exact R18|]. split; [rewrite Q8; exact R8|].
  split; [exact HSC | exact Hi].
Qed.

Lemma d2_at_L : forall cx i d f f' ly3 S3 W3 regs mem md,
  dd_com B cx i d f ly3 S3 W3 regs mem md -> ex_scan cx (S i) d f' ->
  getr regs 23 = w64 (cx_t cx) -> getr regs 19 = w64 (Z.of_nat (S i)) -> getr regs 9 = w64 64 ->
  getr regs 15 = w64 58 -> getr regs 16 = w64 EX_MASK1 ->
  ex_at_L B cx (S i) d f' ly3 S3 W3 regs mem md.
Proof.
  intros cx i d f f' ly3 S3 W3 regs mem md (HB & HC & HSL & R22 & R18 & R8 & _ & _) Hs R23 R19 R9 R15 R16.
  exact (conj HB (conj HC (conj HSL (conj (conj R23 (conj R22 (conj R18 R8))) (conj Hs (conj R19 (conj R9
    (conj R15 R16)))))))).
Qed.

(* closing a register goal after a run: the register's atom value at the cut (G-hypotheses), plus an offset *)
Ltac d2_fin :=
  match goal with G : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite G end;
  rewrite ?d2_w64_add; unfold w64; first [reflexivity | f_equal; lia].

Hypothesis SD3 : dseg_D3 B.

Lemma d2_loop : forall r cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3,
  (length (cx_tb cx) - (p1 + j) = r)%nat ->
  ex_seg_L_from B cx i -> dat_D2 B cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D2 regs3 mem3 md3) (ex_post B cx).
Proof.
  induction r as [r IH] using lt_wf_ind.
  intros cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 Hr HL HD. subst r.
  pose proof LAWS as HLW. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HD as (HDC & HP1 & Hj & R11 & R10 & R20 & R14 & R21 & R24 & R19 & R9 & R23 & R27 & R26 & R15 & R16).
  pose proof HDC as (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi).
  pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  pose proof HP1 as ((Hh & Ha1 & Hsp) & Ep1).
  assert (Hpj : (p1 + j <= length (cx_tb cx))%nat).
  { assert (H0 : (i + a1 < length (cx_tb cx))%nat).
    { destruct (Nat.lt_ge_cases (i + a1) (length (cx_tb cx))) as [H|H]; [exact H|].
      rewrite expected_m.byte_at_ge in Hsp by exact H. discriminate Hsp. }
    pose proof (dm_cw_le MM.is_space (cx_tb cx) (i + a1)).
    pose proof (dm_cw_le MM.name_ok (cx_tb cx) p1). lia. }
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (p1 + j) Ct Hpj) as (_ & Hc255).
  pose proof (d2_entry cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 HD Hpj) as (HS & SHOK).
  remember (Ereg regs3 (d2_extra (cx_t cx + Z.of_nat (p1 + j)) (MM.byte_at (cx_tb cx) (p1 + S j)) (cx_t cx)))
    as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 (MM.byte_at (cx_tb cx) (p1 + S j)))
    by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  clear HE.
  assert (E11 : ew E 11 = Z_to_bv 64 (MM.byte_at (cx_tb cx) (p1 + j)))
    by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (G10 : ew E 10 = w64 (cx_t cx + Z.of_nat p1)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (G14 : ew E 14 = w64 (Z.of_nat i)) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
  assert (G21 : ew E 21 = w64 (Z.of_nat j)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
  assert (G24 : ew E 24 = w64 (1 + Z.of_nat j)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
  assert (G19 : ew E 19 = w64 (cx_t cx + 1 + Z.of_nat j)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (G9 : ew E 9 = w64 (cx_t cx + 1 + Z.of_nat j)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (G23 : ew E 23 = w64 (cx_t cx + 2 + Z.of_nat p1 + Z.of_nat j))
    by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (G27 : ew E 27 = w64 (cx_t cx + 2 + Z.of_nat p1 + Z.of_nat j))
    by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (G26 : ew E 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat p1 - Z.of_nat j))
    by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  set (c := MM.byte_at (cx_tb cx) (p1 + j)) in *.
  unfold cfg_at. change (w64 EX_D2) with (Z_to_bv 64 EX_D2).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D2) mem3 (seg_rom tfibsegs))) in HJ.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  destruct (MM.name_ok c) eqn:Hnm; cbv beta iota in HS, SHOK.
  - (* a name byte: the next one is loaded, back to D2 at j + 1 *)
    assert (Hlt : (p1 + j < length (cx_tb cx))%nat).
    { destruct (Nat.lt_ge_cases (p1 + j) (length (cx_tb cx))) as [H|H]; [exact H|]. exfalso.
      assert (E0 : c = 0) by (unfold c; apply expected_m.byte_at_ge; exact H). rewrite E0 in Hnm. discriminate Hnm. }
    aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan.
    { awr_ok_tac. }
    d2_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
    { d2_dec HS E11 c Hc. clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK D2_Bspan EX_D2; [awr_ok_tac|]. d2_av W3 mem3. d2_mkst HS.
      eapply (IH (length (cx_tb cx) - (p1 + S j))%nat ltac:(lia) cx i d f a1 p1 (S j) ly3 S3 W3 _ _ _ eq_refl HL).
      unfold dat_D2.
      split; [apply (d2_ddcom_kept cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HDC HJ AV); d2_g HS; apply EE; reflexivity|].
      split; [exact HP1|].
      split; [exact (dm_cw_next MM.name_ok (cx_tb cx) p1 j dm_name0 Hj Hnm)|].
      do 11 (split; [d2_g HS; d2_fin|]).
      split; [d2_g HS; reflexivity | d2_g HS; reflexivity]. }
    { d2_dec HS E11 c Hc. rename Hc into D1.
      aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan; [awr_ok_tac|]. d2_av W3 mem3.
      srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
      { d2_dec HS E11 c Hc. exfalso. destruct (d2_c_mk c Hc255 D1 Hc) as [Hf _]. rewrite Hnm in Hf. discriminate Hf. }
      { d2_dec HS E11 c Hc. rename Hc into D2.
        aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan; [awr_ok_tac|]. d2_av W3 mem3.
        srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
        { d2_dec HS E11 c Hc. exfalso. pose proof (d2_c_eq c Hc255 D1 D2 Hc) as E58.
          rewrite E58 in Hnm. discriminate Hnm. }
        { d2_dec HS E11 c Hc. clear Hc.
          aj_run_to_tok EX_tbl_ok HS HJ SHOK D2_Bspan EX_D2; [awr_ok_tac|]. d2_av W3 mem3. d2_mkst HS.
          eapply (IH (length (cx_tb cx) - (p1 + S j))%nat ltac:(lia) cx i d f a1 p1 (S j) ly3 S3 W3 _ _ _ eq_refl HL).
          unfold dat_D2.
          split; [apply (d2_ddcom_kept cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HDC HJ AV); d2_g HS; apply EE;
                  reflexivity|].
          split; [exact HP1|].
          split; [exact (dm_cw_next MM.name_ok (cx_tb cx) p1 j dm_name0 Hj Hnm)|].
          do 11 (split; [d2_g HS; d2_fin|]).
          split; [d2_g HS; reflexivity | d2_g HS; reflexivity]. } } }
  - (* NUL, a space or ':': the name ends at p2 = p1 + j *)
    assert (Hp2 : (p1 + j = p1 + MM.count_while MM.name_ok (skipn p1 (cx_tb cx)))%nat)
      by (rewrite (dm_cw_exact MM.name_ok (cx_tb cx) p1 j Hj Hnm); reflexivity).
    aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan.
    { awr_ok_tac. }
    d2_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
    { d2_dec HS E11 c Hc. exfalso. pose proof (d2_c_gt c Hc255 Hc) as X. rewrite Hnm in X. discriminate X. }
    { d2_dec HS E11 c Hc. rename Hc into D1.
      aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan; [awr_ok_tac|]. d2_av W3 mem3.
      srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
      { (* NUL or a space: 0x814d0, EX_L at i + 1 with decl = DNone *)
        d2_dec HS E11 c Hc. destruct (d2_c_mk c Hc255 D1 Hc) as [_ Hc58]. clear Hc.
        pose proof (dm_decl_colon (cx_tb cx) i (i + a1) p1 (p1 + j) Hh Hsp Ep1 Hp2 Hc58) as Hdn.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK D2_Bspan EX_L; [awr_ok_tac|]. d2_av W3 mem3. d2_mkst HS.
        apply (HL (S i) d (pred f) ly3 S3 W3 _ _ _ (Nat.lt_succ_diag_r i)).
        eapply (d2_at_L cx i d f (pred f) ly3 S3 W3 _ _ _).
        all: first [ exact (dd_scan_none cx i d f HSC Hi Hdn)
                   | apply (d2_ddcom_kept cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HDC HJ AV); d2_g HS; apply EE;
                     reflexivity
                   | d2_g HS; first [reflexivity | d2_fin] ]. }
      { d2_dec HS E11 c Hc. rename Hc into D2.
        aj_run_tok EX_tbl_ok HS HJ SHOK D2_Bspan; [awr_ok_tac|]. d2_av W3 mem3.
        srr_branch_tok EX_tbl_ok HS SHOK D2_Bspan.
        { (* ':': D3 with p2 = p1 + j, no space skipped yet *)
          d2_dec HS E11 c Hc. pose proof (d2_c_eq c Hc255 D1 D2 Hc) as E58. clear Hc.
          aj_run_to_tok EX_tbl_ok HS HJ SHOK D2_Bspan EX_D3; [awr_ok_tac|]. d2_av W3 mem3. d2_mkst HS.
          eapply (SD3 cx i d f a1 p1 (p1 + j)%nat 0%nat ly3 S3 W3 _ _ _ HL).
          unfold dat_D3.
          split; [apply (d2_ddcom_kept cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HDC HJ AV); d2_g HS; apply EE;
                  reflexivity|].
          split; [unfold dm_p2; split; [exact HP1|]; split; [exact Hp2 | exact E58]|].
          split; [lia|].
          do 9 (split; [d2_g HS; d2_fin|]).
          split; [d2_g HS; reflexivity | d2_g HS; reflexivity]. }
        { d2_dec HS E11 c Hc. exfalso. pose proof (d2_c_nm c Hc255 D1 D2 Hc) as X. rewrite Hnm in X.
          discriminate X. } } }
Qed.

Theorem decl_D2_holds : dseg_D2 B.
Proof.
  intros cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 HL HD.
  exact (d2_loop _ cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 eq_refl HL HD).
Qed.
End W.

Print Assumptions decl_D2_holds.
