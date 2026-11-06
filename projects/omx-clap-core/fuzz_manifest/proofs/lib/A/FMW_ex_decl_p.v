(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 334 of its 382 lines of code are new or changed and 219 lines of the source are left out. *)
(* G4.ExDecl.DeclPB: ex_seg_P (FMW_ex_base.v:177) on fm.asan, from EX_P (0x81344, fuzz_manifest.c:142-147).
   s4 = text + i + a1 = text + p0 (p0 = i + a1, the end of the head word), the instrumented load of text[p0], the
   ex_space decision (0x81360 bgeu c - 9 >=u 5, 0x81440 beq c ' '). Not a space: 0x81444 -> 0x814dc s3 += 1 -> EX_L at
   i + 1 (ManifestModel.decl = DNone, dm_decl_sp). A space: 0x81364..0x8137c (a1 = i + a1, a0 = text + p0,
   s7 = s11 = text + 2 + p0, s10 = uri - text - 2 - p0) -> D1 (0x81380) with k = 0 (dseg_D1).
   The symbolic state at EX_P: registers are their own atoms (sr_atoms), the scan's constants pinned (after
   FMW_ex_head_d.v hd_pins), s9 (register 25) is the shadow base; extra atoms 32 = uri - text - 2 (the slot F+0x38),
   33 = text + 2 (F+0x48), 34 = text[p0], 35 = text + p0 (the alias of s4 + a1, after FMW_ex_head_d.v ss_L). *)
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

(* ---- a head ends inside the text (copied from fm's lib/Prog/expected_ml.v ci_len, head_le) ---- *)
Lemma p_ci_len : forall a b, ManifestModel.ci_eqb a b = true -> length a = length b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ H]. rewrite (IH b H). reflexivity.
Qed.

Lemma p_head_le : forall t i p0, ManifestModel.head t i = Some p0 -> (p0 <= length t)%nat.
Proof.
  intros t i p0 H. unfold ManifestModel.head in H.
  destruct ((ManifestModel.byte_at t i =? 64) &&
            ManifestModel.zl_eqb (firstn 6 (skipn (S i) t)) ManifestModel.prefix_lc) eqn:E1.
  - injection H as <-. apply andb_true_iff in E1 as [_ E1]. apply ManifestModel.zl_eqb_eq in E1.
    apply (f_equal (@length Z)) in E1. rewrite length_firstn, length_skipn in E1.
    change (length ManifestModel.prefix_lc) with 6%nat in E1. lia.
  - destruct (ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc) eqn:E2; cbn [andb] in H;
      [|discriminate].
    apply p_ci_len in E2. rewrite length_firstn, length_skipn in E2.
    change (length ManifestModel.prefix_lc) with 6%nat in E2.
    destruct i as [|i']; [|destruct (ManifestModel.is_space (ManifestModel.byte_at t i'))]; try discriminate;
      injection H as <-; lia.
Qed.

(* ---- register values as 64-bit words ---- *)
Lemma p_den_off : forall E n c x, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
  intros E n c x H. cbn [sv_denot]. rewrite H, unsigned_lit. apply Z_to_bv64_eq_mod.
  unfold zcanon, M64. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma p_den_add : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zalu64_sound. unfold zalu64. cbn [zalu_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma p_den_sub : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_SUB a b) = Z_to_bv 64 (x - y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zalu64_sound. unfold zalu64. cbn [zalu_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma p_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma p_den_mul : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SMd M_MUL a b) = Z_to_bv 64 (x * y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zmd64_sound. unfold zmd64. cbn [zmd_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zmult_mod. reflexivity.
Qed.

(* ---- the symbolic state at EX_P ---- *)
Definition P_Bx : sv := SOff 25 0.
Definition P_Bspan : Z * Z := EX_Bspan.
(* s0 = ' ', s1 = '@', a5 = ':', a6 = the mask, s2 = 5, s6 = 6 (FMW_ex_head_d.v hd_pins) *)
Definition p_pins (sr : list sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr
    8%bv (SLit 32)) 9%bv (SLit 64)) 15%bv (SLit 58)) 16%bv (SLit EX_MASK1)) 18%bv (SLit 5)) 22%bv (SLit 6).
Definition p_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x38 0x50 0x38 0x38
    [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 33 0))].
Definition p_byte : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition ss_P : sstate :=
  mkSS EX_P (p_pins sr_atoms) [p_frame; p_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF FW_SB FW_SB 0); (34%nat, mkAF 0 255 0);
              (35%nat, mkAF 4096 (2 ^ 47 - 16) 0)] []
       [(SAlu ALU_ADD (SOff 20 0) (SOff 11 0), SOff 35 0)]).
Definition SH_P : list shent := [mkSHE 35 0 1].
Definition p_extra (u t c q : Z) : list word := [Z_to_bv 64 (u - t - 2); Z_to_bv 64 (t + 2); Z_to_bv 64 c; Z_to_bv 64 q].

(* ---- the ex_space decision on the byte alone (closed valuation with c at atom 34, after FMW_plain.v pl_D) ---- *)
Definition p_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition p_Ec (c : Z) : env := ewset p_E00 34 (Z_to_bv 64 c).
Definition p_D (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (p_Ec c) a) (sv_denot (p_Ec c) b).
Lemma p_D_of : forall E c cnd a b, ew E 34 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 34) a = true -> sv_atoms_in (Nat.eqb 34) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = p_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold p_D.
  assert (HA : env_agree_on (Nat.eqb 34) E (p_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold p_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
Lemma p_cls : forall g : Z -> bool, forallb g (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c < 256 -> g c = true.
Proof.
  intros g H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Definition p_a1 : sv := SOff 34 (-9).
Definition p_b1 : sv := SLit 5.
Definition p_a2 : sv := SOff 34 0.
Definition p_b2 : sv := SLit 32.
Lemma p_cls_sp1 : forall c, 0 <= c < 256 -> p_D BC_GEU p_a1 p_b1 c = false -> ManifestModel.is_space c = true.
Proof.
  intros c Hc H1.
  pose proof (p_cls (fun z => p_D BC_GEU p_a1 p_b1 z || ManifestModel.is_space z) ltac:(vm_compute; reflexivity) c Hc)
    as X.
  cbv beta in X. rewrite H1 in X. exact X.
Qed.
Lemma p_cls_sp2 : forall c, 0 <= c < 256 -> p_D BC_GEU p_a1 p_b1 c = true -> p_D BC_EQ p_a2 p_b2 c = true ->
  ManifestModel.is_space c = true.
Proof.
  intros c Hc H1 H2.
  pose proof (p_cls (fun z => negb (p_D BC_GEU p_a1 p_b1 z) || negb (p_D BC_EQ p_a2 p_b2 z) ||
    ManifestModel.is_space z) ltac:(vm_compute; reflexivity) c Hc) as X.
  cbv beta in X. rewrite H1, H2 in X. exact X.
Qed.
Lemma p_cls_sp3 : forall c, 0 <= c < 256 -> p_D BC_GEU p_a1 p_b1 c = true -> p_D BC_EQ p_a2 p_b2 c = false ->
  ManifestModel.is_space c = false.
Proof.
  intros c Hc H1 H2.
  pose proof (p_cls (fun z => negb (p_D BC_GEU p_a1 p_b1 z) || p_D BC_EQ p_a2 p_b2 z ||
    negb (ManifestModel.is_space z)) ltac:(vm_compute; reflexivity) c Hc) as X.
  cbv beta in X. rewrite H1, H2 in X. cbn [negb orb] in X. apply Bool.negb_true_iff in X. exact X.
Qed.

(* ---- walk tactics (after FMW_ex_head.v hd_reg / hd_av / hd_mk, FMW_plain.v pl_dec) ---- *)
Ltac p_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac p_av W mem1 :=
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
Ltac p_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac p_g HS := lazymatch goal with |- getr _ ?r = _ => p_reg HS r end.
Ltac p_dec HS E34 c Hc :=
  let H34 := fresh "H34" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H34 : ew Ex 34 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E34) end;
  erewrite (p_D_of _ _ _ _ _ H34) in Hc by reflexivity; clear H34.
Ltac p_ew := cbn [ew ewset Nat.eqb]; eassumption.
Ltac p_val :=
  lazymatch goal with
  | |- sv_denot _ (SAlu ALU_ADD _ _) = _ => eapply p_den_add; [p_val | p_val]
  | |- sv_denot _ (SAlu ALU_SUB _ _) = _ => eapply p_den_sub; [p_val | p_val]
  | |- sv_denot _ (SMd M_MUL _ _) = _ => eapply p_den_mul; [p_val | p_val]
  | |- sv_denot _ (SOff _ _) = _ => eapply p_den_off; p_ew
  | |- sv_denot _ (SLit _) = _ => apply p_den_lit
  end.
Ltac p_rv EE :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => reflexivity
  | |- sv_denot _ (SOff _ 0) = getr _ _ =>
      cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity
  | |- sv_denot _ _ = w64 _ => unfold w64; etransitivity; [p_val | apply Z_to_bv64_eq_mod; f_equal; lia]
  end.
Ltac p_regs HS EE := p_g HS; p_rv EE.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD1 : dseg_D1 B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the entry: st_ok of ss_P and the shadow entry of text[p0] from ex_at_P (after FMW_ex_head_e.v hd_L_entry) ---- *)
Lemma P_entry : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3,
  ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) (MM.byte_at (cx_tb cx) (i + a1))
      (cx_t cx + Z.of_nat (i + a1)))) ss_P
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_P) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs P_Bx SH_P (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) (MM.byte_at (cx_tb cx) (i + a1))
      (cx_t cx + Z.of_nat (i + a1)))) (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HA.
  destruct HA as (HB & HC & HSL & HSR & HSC & Hi & Hh & Ha1 & R19 & R20 & R11 & R9 & R15 & R16).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _).
  destruct HSL as (_ & _ & _ & S38 & _ & S48 & _).
  destruct HSR as (R23 & R22 & R18 & R8).
  pose proof (p_head_le _ _ _ Hh) as Hp0.
  destruct (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i + a1) HCt Hp0) as [Vc Hcr].
  pose proof HCt as (_ & _ & _ & _ & Ham & HRA & _).
  rewrite restrict_mkst_fx.
  set (c := MM.byte_at (cx_tb cx) (i + a1)) in *.
  set (E := Ereg regs3 (p_extra (cx_u cx) (cx_t cx) c (cx_t cx + Z.of_nat (i + a1)))).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U20 : bv_unsigned (ew E 20) = cx_t cx + Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E 11) = Z.of_nat a1)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 11 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_u cx - cx_t cx - 2)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx + 2)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (E35 : ew E 35 = Z_to_bv 64 (cx_t cx + Z.of_nat (i + a1))) by (subst E; exact (ew_Ereg_extra regs3 _ 3)).
  assert (U35 : bv_unsigned (ew E 35) = cx_t cx + Z.of_nat (i + a1)) by (rewrite E35; apply unsigned_lit_small; lia).
  split.
  - unfold ss_P. apply (entry_st_ok_full tfibsegs);
      change (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) c (cx_t cx + Z.of_nat (i + a1)))) with E.
    + unfold p_pins.
      repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
        cbn [sv_denot]; first [exact R8 | exact R9 | exact R15 | exact R16 | exact R18 | exact R22].
    + vm_compute. reflexivity.
    + unfold p_frame, p_byte. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x38 8 (SOff 32 0) ((cx_u cx - cx_t cx - 2) mod 2 ^ 64)).
           ++ cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply Z_to_bv64_eq_mod.
              rewrite Z.mod_mod by lia. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
           ++ cbn. lia.
           ++ exact S38.
        -- apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x48 8 (SOff 33 0) (cx_t cx + 2)).
           ++ cbn [sv_denot]. rewrite E33, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
           ++ cbn. lia.
           ++ exact S48.
      * rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (cx_t cx + Z.of_nat (i + a1)) 0 1 (SOff 34 0) c);
          [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        rewrite Z.add_0_r. exact Vc.
    + apply pairwise_disjoint_of_extents. unfold p_frame, p_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U2, U25, U34, U35. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold FW_SB, SHADOW_OFF. repeat split; first [exact HFm | lia].
      * cbn [f_alias alias_ok]. split; [|exact I]. cbn [sv_denot].
        rewrite U20, U11, U35, !Z.add_0_r. rewrite alu_add_small by (unfold M64; lia). f_equal. lia.
  - unfold sh_ok, SH_P. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E P_Bx 35 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
      (cx_t cx + Z.of_nat (i + a1)) 0 1).
    + exact HRA.
    + unfold P_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 35 _ E35). lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

(* ---- the exits ---- *)
(* not a space: EX_L at i + 1 (the declaration at i is DNone) *)
Lemma p_exit_L : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_seg_L_from B cx i -> ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  MM.is_space (MM.byte_at (cx_tb cx) (i + a1)) = false ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 23 = getr regs3 23 ->
  getr regs4 22 = w64 6 -> getr regs4 18 = w64 5 -> getr regs4 8 = w64 32 ->
  getr regs4 19 = w64 (Z.of_nat (S i)) -> getr regs4 9 = w64 64 -> getr regs4 15 = w64 58 ->
  getr regs4 16 = w64 EX_MASK1 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs4 mem4 md4) (ex_post B cx).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HLf HA Hsp HJ4 AV
    Q2 Q3 Q4 Q25 Q23 Q22 Q18 Q8 Q19 Q9 Q15 Q16.
  pose proof HA as (HB & HC & HSL & HSR & HSC & Hi & Hh & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  apply (HLf (S i) d (pred f) ly3 S3 W3 regs4 mem4 md4); [lia|].
  split; [exact HB|].
  split.
  { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4);
      [intros a Ha _ _ _; apply AV; exact Ha | exact Q2 | exact Q3 | exact Q4 | exact Q25]. }
  split; [apply (dd_slots_kept B cx W3 mem3 mem4 d HB HSL); intros a Ha; apply AV; lia|].
  split.
  { destruct HSR as (R23 & _). split; [rewrite Q23; exact R23|].
    split; [exact Q22|]. split; [exact Q18 | exact Q8]. }
  split; [exact (dd_scan_none cx i d f HSC Hi (dm_decl_sp _ _ (i + a1) Hh Hsp))|].
  split; [exact Q19|]. split; [exact Q9|]. split; [exact Q15 | exact Q16].
Qed.

(* a space: D1 with k = 0 *)
Lemma p_exit_D1 : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_seg_L_from B cx i -> ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  MM.is_space (MM.byte_at (cx_tb cx) (i + a1)) = true ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 22 = w64 6 -> getr regs4 18 = w64 5 -> getr regs4 8 = w64 32 ->
  getr regs4 10 = w64 (cx_t cx + Z.of_nat (i + a1)) -> getr regs4 20 = w64 (cx_t cx + Z.of_nat (i + a1)) ->
  getr regs4 23 = w64 (cx_t cx + 2 + Z.of_nat (i + a1)) -> getr regs4 27 = w64 (cx_t cx + 2 + Z.of_nat (i + a1)) ->
  getr regs4 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat (i + a1)) ->
  getr regs4 19 = w64 (Z.of_nat i) -> getr regs4 9 = w64 64 -> getr regs4 15 = w64 58 ->
  getr regs4 16 = w64 EX_MASK1 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D1 regs4 mem4 md4) (ex_post B cx).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HLf HA Hsp HJ4 AV
    Q2 Q3 Q4 Q25 Q22 Q18 Q8 Q10 Q20 Q23 Q27 Q26 Q19 Q9 Q15 Q16.
  pose proof HA as (HB & HC & HSL & HSR & HSC & Hi & Hh & Ha1 & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  apply (SD1 cx i d f a1 0%nat ly3 S3 W3 regs4 mem4 md4 HLf).
  unfold dat_D1. rewrite !Nat.add_0_r.
  split.
  { split; [exact HB|].
    split.
    { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4);
        [intros a Ha _ _ _; apply AV; exact Ha | exact Q2 | exact Q3 | exact Q4 | exact Q25]. }
    split; [apply (dd_slots_kept B cx W3 mem3 mem4 d HB HSL); intros a Ha; apply AV; lia|].
    split; [exact Q22|]. split; [exact Q18|]. split; [exact Q8|]. split; [exact HSC | exact Hi]. }
  split; [split; [exact Hh|]; split; [exact Ha1 | exact Hsp]|].
  split; [lia|].
  split; [exact Q10|]. split; [exact Q20|]. split; [exact Q23|]. split; [exact Q27|]. split; [exact Q26|].
  split; [exact Q19|]. split; [exact Q9|]. split; [exact Q15 | exact Q16].
Qed.

(* ---- the walk ---- *)
Theorem decl_P_holds : ex_seg_P B.
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HLf HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HA as (HB & HC & HSL & HSR & HSC & Hi & Hh & Ha1 & R19 & R20 & R11 & R9 & R15 & R16).
  pose proof HC as (HJ & _ & _ & Rsp & Rgp & Rtp & R25 & _ & _ & HCt & _).
  pose proof HSR as (R23 & R22 & R18 & R8).
  pose proof (p_head_le _ _ _ Hh) as Hp0.
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i + a1) HCt Hp0) as (_ & Hcr).
  destruct (P_entry cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HA) as [HS SHOK].
  set (c := MM.byte_at (cx_tb cx) (i + a1)) in *.
  remember (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) c (cx_t cx + Z.of_nat (i + a1)))) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_u cx - cx_t cx - 2)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx + 2)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (cx_t cx + Z.of_nat (i + a1))) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 3)).
  assert (X11 : ew E 11 = Z_to_bv 64 (Z.of_nat a1)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (X19 : ew E 19 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (X23 : ew E 23 = Z_to_bv 64 (cx_t cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  clear HE.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_P) mem3 (seg_rom tfibsegs))) in HJ, SHOK.
  unfold cfg_at. change (w64 EX_P) with (Z_to_bv 64 EX_P).
  aj_run_tok EX_tbl_ok HS HJ SHOK P_Bspan.
  { awr_ok_tac. }
  p_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK P_Bspan.
  - (* 0x81360 bgeu taken: c is not in 9..13; 0x81440 beq c ' ' next *)
    p_dec HS E34 c Hc. rename Hc into D1.
    aj_run_tok EX_tbl_ok HS HJ SHOK P_Bspan; [awr_ok_tac|]. p_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK P_Bspan.
    + (* c = ' ': a space, 0x81364 .. D1 *)
      p_dec HS E34 c Hc.
      pose proof (p_cls_sp2 c Hcr D1 Hc) as Hsp. clear D1 Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_D1; [awr_ok_tac|]. p_av W3 mem3.
      p_mk HS.
      eapply (p_exit_D1 cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HLf HA Hsp HJ AV);
        p_regs HS EE.
    + (* not a space: 0x81444 -> 0x814dc s3 += 1 -> EX_L *)
      p_dec HS E34 c Hc.
      pose proof (p_cls_sp3 c Hcr D1 Hc) as Hsp. clear D1 Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_L; [awr_ok_tac|]. p_av W3 mem3.
      p_mk HS.
      eapply (p_exit_L cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HLf HA Hsp HJ AV);
        p_regs HS EE.
  - (* 0x81360 bgeu not taken: 9 <= c <= 13, a space, 0x81364 .. D1 *)
    p_dec HS E34 c Hc.
    pose proof (p_cls_sp1 c Hcr Hc) as Hsp. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_D1; [awr_ok_tac|]. p_av W3 mem3.
    p_mk HS.
    eapply (p_exit_D1 cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HLf HA Hsp HJ AV);
      p_regs HS EE.
Qed.
End W.

Print Assumptions decl_P_holds.
