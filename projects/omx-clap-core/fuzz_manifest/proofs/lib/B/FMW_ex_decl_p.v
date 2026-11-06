(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 334 of its 382 lines of code are new or changed and 219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_decl_p.v, with its module paths, module names, addresses and numbers changed; 102 of its 305 lines of code are new or changed and 179 lines of the source are left out. *)
(* G4.ExDecl, IMAGE B: ex_seg_P's first piece, from EX_P (0x814cc, fuzz_manifest.c:142-147) on fm.asan-ubsan.
   B twin of lib/A/FMW_ex_decl_p.v (06d82004dc3); B's code (fm_b_expected_iface.out lines 162-172, 224-227):
   0x814cc s4 = s5 + a0 = text + i + a1 = text + p0, the instrumented load of text[p0], 0x814e8 `bgeu c - 9, s3 (= 5)`
   and 0x815c4 `beq c, s11 (= ' ')` decide ManifestModel.is_space. Not a space: 0x815c8 j EX_NEXT 0x81694 with s7 = i
   (ManifestModel.decl = DNone, dm_decl_sp; dseg_N). A space: 0x814ec..0x814fc (a0 = text + p0, a2 = a0 + 1,
   s8 = a0 + 2, s10 = ld F+0x60 - a0 = uri - 2 - text - p0) -> D1 (0x81500) with k = 0 (dseg_D1).
   The symbolic state at EX_P: registers are their own atoms (sr_atoms), s3 = 5 and s11 = ' ' pinned, s9 (register 25)
   the shadow base; extra atoms 32 = uri - 2 (the slot F+0x60), 33 = text[p0], 34 = text + p0 (the alias of s5 + a0). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- a head ends inside the text (copied from fm's lib/Prog/expected_ml.v ci_len, head_le, as A's file does) ---- *)
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

(* ---- the symbolic state at EX_P ---- *)
Definition P_Bx : sv := SOff 25 0.
Definition P_Bspan : Z * Z := EX_Bspan.
(* s3 = 5, s11 = ' ' (ex_sregs) *)
Definition p_pins (sr : list sv) : list sv := sr_set (sr_set sr 19%bv (SLit 5)) 27%bv (SLit 32).
Definition p_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x60 0x68 0x60 0x60 [YP09.mkChunk 0x60 (CVal 8 (SOff 32 0))].
Definition p_byte : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ss_P : sstate :=
  mkSS EX_P (p_pins sr_atoms) [p_frame; p_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 0 255 0);
              (34%nat, mkAF 4096 (2 ^ 47 - 16) 0)] []
       [(SAlu ALU_ADD (SOff 21 0) (SOff 10 0), SOff 34 0)]).
Definition SH_P : list shent := [mkSHE 34 0 1].
Definition p_extra (u t c q : Z) : list word := [Z_to_bv 64 (u - 2); Z_to_bv 64 c; Z_to_bv 64 q].

(* ---- the ex_space decision on the byte alone (closed valuation with c at atom 33, after FMW_plain.v pl_D) ---- *)
Definition p_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition p_Ec (c : Z) : env := ewset p_E00 33 (Z_to_bv 64 c).
Definition p_D (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (p_Ec c) a) (sv_denot (p_Ec c) b).
Lemma p_D_of : forall E c cnd a b, ew E 33 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 33) a = true -> sv_atoms_in (Nat.eqb 33) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = p_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold p_D.
  assert (HA : env_agree_on (Nat.eqb 33) E (p_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold p_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
Lemma p_cls : forall g : Z -> bool, forallb g (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c < 256 -> g c = true.
Proof.
  intros g H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Definition p_a1 : sv := SOff 33 (-9).
Definition p_b1 : sv := SLit 5.
Definition p_a2 : sv := SOff 33 0.
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

Ltac p_dec HS E33 c Hc :=
  let H33 := fresh "H33" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H33 : ew Ex 33 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E33) end;
  erewrite (p_D_of _ _ _ _ _ H33) in Hc by reflexivity; clear H33.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD1 : dseg_D1 B.
Hypothesis SDN : dseg_N B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the entry: st_ok of ss_P and the shadow entry of text[p0] from ex_at_P ---- *)
Lemma P_entry : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3,
  ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) (MM.byte_at (cx_tb cx) (i + a1))
      (cx_t cx + Z.of_nat (i + a1)))) ss_P
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_P) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs P_Bx SH_P (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) (MM.byte_at (cx_tb cx) (i + a1))
      (cx_t cx + Z.of_nat (i + a1)))) (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HA.
  destruct HA as (HB & HC & HSL & HSR & HCR & HSC & Hi & Hh & Ha1 & R23 & R21 & R10).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _).
  destruct HSL as (_ & _ & _ & _ & _ & S60 & _).
  destruct HSR as (R19 & R27 & R8).
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
  assert (U21 : bv_unsigned (ew E 21) = cx_t cx + Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = Z.of_nat a1)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_u cx - 2)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = cx_u cx - 2) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx + Z.of_nat (i + a1))) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (U34 : bv_unsigned (ew E 34) = cx_t cx + Z.of_nat (i + a1)) by (rewrite E34; apply unsigned_lit_small; lia).
  split.
  - unfold ss_P. apply (entry_st_ok_full tfibsegs);
      change (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) c (cx_t cx + Z.of_nat (i + a1)))) with E.
    + unfold p_pins.
      repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
        cbn [sv_denot]; first [exact R19 | exact R27].
    + vm_compute. reflexivity.
    + unfold p_frame, p_byte. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x60 8 (SOff 32 0) (cx_u cx - 2));
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact S60].
      * rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (cx_t cx + Z.of_nat (i + a1)) 0 1 (SOff 33 0) c);
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        rewrite Z.add_0_r. exact Vc.
    + apply pairwise_disjoint_of_extents. unfold p_frame, p_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U34.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U2, U25, U33, U34. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold FW_SB, SHADOW_OFF. repeat split; first [exact HFm | lia].
      * cbn [f_alias alias_ok]. split; [|exact I]. cbn [sv_denot].
        rewrite U21, U10, U34, !Z.add_0_r. rewrite alu_add_small by (unfold M64; lia). f_equal. lia.
  - unfold sh_ok, SH_P. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E P_Bx 34 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
      (cx_t cx + Z.of_nat (i + a1)) 0 1).
    + exact HRA.
    + unfold P_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 34 _ E34). lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

(* ---- the exits ---- *)
(* not a space: EX_NEXT with s7 = i (the declaration at i is DNone) *)
Lemma p_exit_N : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  MM.is_space (MM.byte_at (cx_tb cx) (i + a1)) = false ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 23 = getr regs3 23 -> getr regs4 8 = getr regs3 8 ->
  getr regs4 16 = getr regs3 16 -> getr regs4 17 = getr regs3 17 -> getr regs4 5 = getr regs3 5 ->
  getr regs4 6 = getr regs3 6 ->
  getr regs4 19 = w64 5 -> getr regs4 27 = w64 32 ->
  dat_N B cx i d (pred f) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HA Hsp HJ4 AV
    Q2 Q3 Q4 Q25 Q23 Q8 Q16 Q17 Q5 Q6 R19' R27'.
  pose proof HA as (HB & HC & HSL & HSR & HCR & HSC & Hi & Hh & _ & R23 & _).
  pose proof HSR as (_ & _ & R8). pose proof HCR as (R16 & R17 & R5 & R6).
  apply (dd_N_none B cx i d f ly3 S3 W3 regs4 mem4 md4).
  - refine (dd_com_same B cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 _ HJ4 AV Q2 Q3 Q4 Q25 R19' R27' _);
      [|rewrite Q8; exact R8].
    split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HSC | exact Hi].
  - split; [rewrite Q16; exact R16|]. split; [rewrite Q17; exact R17|]. split; [rewrite Q5; exact R5 | rewrite Q6; exact R6].
  - rewrite Q23. exact R23.
  - exact (dm_decl_sp _ _ (i + a1) Hh Hsp).
Qed.

(* a space: D1 with k = 0 *)
Lemma p_exit_D1 : forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_at_P B cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  MM.is_space (MM.byte_at (cx_tb cx) (i + a1)) = true ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 23 = getr regs3 23 -> getr regs4 8 = getr regs3 8 ->
  getr regs4 16 = getr regs3 16 -> getr regs4 17 = getr regs3 17 -> getr regs4 5 = getr regs3 5 ->
  getr regs4 6 = getr regs3 6 ->
  getr regs4 19 = w64 5 -> getr regs4 27 = w64 32 ->
  getr regs4 10 = w64 (cx_t cx + Z.of_nat (i + a1)) -> getr regs4 20 = w64 (cx_t cx + Z.of_nat (i + a1)) ->
  getr regs4 12 = w64 (cx_t cx + 1 + Z.of_nat (i + a1)) -> getr regs4 24 = w64 (cx_t cx + 2 + Z.of_nat (i + a1)) ->
  getr regs4 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat (i + a1)) ->
  dat_D1 B cx i d f a1 0 ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HA Hsp HJ4 AV
    Q2 Q3 Q4 Q25 Q23 Q8 Q16 Q17 Q5 Q6 R19' R27' Q10 Q20 Q12 Q24 Q26.
  pose proof HA as (HB & HC & HSL & HSR & HCR & HSC & Hi & Hh & Ha1 & R23 & _).
  pose proof HSR as (_ & _ & R8). pose proof HCR as (R16 & R17 & R5 & R6).
  unfold dat_D1. rewrite !Nat.add_0_r.
  split.
  { refine (dd_com_same B cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 _ HJ4 AV Q2 Q3 Q4 Q25 R19' R27' _);
      [|rewrite Q8; exact R8].
    split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HSC | exact Hi]. }
  split; [split; [rewrite Q16; exact R16|]; split; [rewrite Q17; exact R17|];
          split; [rewrite Q5; exact R5 | rewrite Q6; exact R6]|].
  split; [split; [exact Hh|]; split; [exact Ha1 | exact Hsp]|].
  split; [lia|].
  split; [exact Q10|]. split; [exact Q20|]. split; [exact Q12|]. split; [exact Q24|]. split; [exact Q26|].
  rewrite Q23. exact R23.
Qed.

(* ---- the walk ---- *)
Theorem decl_P_holds : ex_seg_P B.
Proof.
  intros cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HLf HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HA as (HB & HC & HSL & HSR & HCR & HSC & Hi & Hh & Ha1 & R23 & R21 & R10).
  pose proof HC as (HJ & _ & _ & Rsp & Rgp & Rtp & R25 & _ & _ & HCt & _).
  pose proof HSR as (R19 & R27 & R8).
  pose proof HCR as (R16 & R17 & R5 & R6).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  pose proof (p_head_le _ _ _ Hh) as Hp0.
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i + a1) HCt Hp0) as (_ & Hcr).
  destruct (P_entry cx i d f a1 ly3 S3 W3 regs3 mem3 md3 HA) as [HS SHOK].
  set (c := MM.byte_at (cx_tb cx) (i + a1)) in *.
  remember (Ereg regs3 (p_extra (cx_u cx) (cx_t cx) c (cx_t cx + Z.of_nat (i + a1)))) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_u cx - 2)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx + Z.of_nat (i + a1))) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat a1)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (E21 : ew E 21 = Z_to_bv 64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
  clear HE.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_P) mem3 (seg_rom tfibsegs))) in HJ, SHOK.
  unfold cfg_at. change (w64 EX_P) with (Z_to_bv 64 EX_P).
  aj_run_tok EX_tbl_ok HS HJ SHOK P_Bspan.
  { awr_ok_tac. }
  dd_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK P_Bspan.
  - (* 0x814e8 bgeu taken: c is not in 9..13; 0x815c4 beq c ' ' next *)
    p_dec HS E33 c Hc. rename Hc into D1.
    aj_run_tok EX_tbl_ok HS HJ SHOK P_Bspan; [awr_ok_tac|]. dd_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK P_Bspan.
    + (* c = ' ': a space, 0x814ec .. D1 *)
      p_dec HS E33 c Hc.
      pose proof (p_cls_sp2 c Hcr D1 Hc) as Hsp. clear D1 Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_D1; [awr_ok_tac|]. dd_av W3 mem3.
      dd_mk HS.
      apply (SD1 cx i d f a1 0%nat ly3 S3 W3 _ _ _ HLf).
      eapply (p_exit_D1 cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HA Hsp HJ AV); dd_regs HS EE.
    + (* not a space: 0x815c8 j EX_NEXT (s7 = i) *)
      p_dec HS E33 c Hc.
      pose proof (p_cls_sp3 c Hcr D1 Hc) as Hsp. clear D1 Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_NEXT; [awr_ok_tac|]. dd_av W3 mem3.
      dd_mk HS.
      apply (SDN cx i i d (pred f) ly3 S3 W3 _ _ _ HLf (le_n i)).
      eapply (p_exit_N cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HA Hsp HJ AV); dd_regs HS EE.
  - (* 0x814e8 bgeu not taken: 9 <= c <= 13, a space, 0x814ec .. D1 *)
    p_dec HS E33 c Hc.
    pose proof (p_cls_sp1 c Hcr Hc) as Hsp. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK P_Bspan EX_D1; [awr_ok_tac|]. dd_av W3 mem3.
    dd_mk HS.
    apply (SD1 cx i d f a1 0%nat ly3 S3 W3 _ _ _ HLf).
    eapply (p_exit_D1 cx i d f a1 ly3 S3 W3 regs3 mem3 md3 _ _ _ HA Hsp HJ AV); dd_regs HS EE.
Qed.
End W.

Check decl_P_holds.
Print Assumptions decl_P_holds.
