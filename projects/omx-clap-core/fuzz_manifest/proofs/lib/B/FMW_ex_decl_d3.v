(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v, with its module paths and module names changed; 305 of its 367 lines of code are new or changed and 869 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_ex_tok_base.v; 567 of its 633 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_ex_decl_base.v; 247 of its 299 lines of code are new or changed and 581 lines of the source are left out. *)
(* G4.ExDecl, IMAGE B: expected's D3 loop (0x815d8..0x81630, fuzz_manifest.c:154-156) on fm.asan-ubsan, dseg_D3 of
   FMW_ex_decl_base.v. B twin of lib/A/FMW_ex_decl_d3.v (06d82004dc3); B's code (fm_b_expected_iface.out lines
   229-251): the spaces after the declaration's ':' at p2: the byte c = text[S p2 + m] is checked (a0 = s8 - 1, shadow
   check, error path 0x81614.. not reached) and loaded from 0(a2) (a2 = text + 1 + p2 + m, s8 = a2 + 1);
   0x815f4 `bgeu c - 9, s3 (= 5)` and 0x8160c `bne c, s11 (= ' ')` decide ex_space: a space goes 0x815f8..0x81600
   (a2, s8 += 1, s10 -= 1) and through the UBSan guard 0x81604 `bnez a2` back to D3 at m + 1; c = '<' (0x81624 not
   taken) passes the guard 0x81628 `beq a2, s0` and sets s7 = a2 + 1 = ns: D3c at 0x81630 with p3 = S p2 + m; any other
   byte: 0x81624 bne -> EX_NEXT with s7 = i (decl = DNone by dm_decl_lt). The loop closes by strong induction on
   |text| - (S p2 + m). Guards 0x81604 (B5 class K1n) and 0x81628 (K1): a2 is an atom in [4096, 2^47 - 16], so
   the executor decides `bnez a2 + 1` taken and `beq a2, -1` not taken. *)
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

(* ---- the symbolic state at D3 (0x815d8): s9 (register 25) holds the shadow base (the token base D3_Bx); s3 = 5,
   s11 = ' ', s0 = -1, t0 = ':', t1 = the mask pinned as literals; s8 (register 24) pinned to a2's atom 12 plus 1;
   extra atom 32 = c, the byte at a2 ---- *)
Definition D3_Bx : sv := SOff 25 0.
Definition D3_Bspan : Z * Z := EX_Bspan.
Definition d3_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 5%bv (SLit 58)) 6%bv (SLit EX_MASK1)) 19%bv (SLit 5))
    27%bv (SLit 32)) 8%bv (SLit 18446744073709551615)) 24%bv (SOff 12 1).
Definition d3_byte : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_D3 : sstate :=
  mkSS EX_D3 d3_regs [d3_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (12%nat, mkAF 4096 (2 ^ 47 - 16) 0);
              (25%nat, mkAF FW_SB FW_SB 0); (32%nat, mkAF 0 255 0)] [] []).
Definition SH_D3 : list shent := [mkSHE 12 0 1].

(* ---- pure facts ---- *)
(* ex_space as the code tests it: (c - 9) mod 2^64 <u 5, or c = ' ' (by enumeration of the 256 byte values) *)
Lemma d3_space : forall c, 0 <= c < 256 ->
  ManifestModel.is_space c = (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (ManifestModel.is_space c) (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

(* a space is inside the text (the NUL past its end is not a space) *)
Lemma d3_lt : forall tb q, ManifestModel.is_space (ManifestModel.byte_at tb q) = true -> (q < length tb)%nat.
Proof.
  intros tb q H. destruct (Nat.lt_ge_cases q (length tb)) as [Hq|Hq]; [exact Hq|].
  rewrite expected_m.byte_at_ge in H by exact Hq. discriminate.
Qed.

(* the byte the loop reads, S p2 + m, is at most |text| (the ':' at p2 is inside the text) *)
Lemma d3_le : forall cx i a1 p1 p2 m, dm_p2 cx i a1 p1 p2 ->
  (m <= ManifestModel.count_while ManifestModel.is_space (skipn (S p2) (cx_tb cx)))%nat ->
  (S p2 + m <= length (cx_tb cx))%nat.
Proof.
  intros cx i a1 p1 p2 m (_ & _ & H58) Hm. pose proof (dm_cw_le ManifestModel.is_space (cx_tb cx) (S p2)) as Hle.
  destruct (Nat.lt_ge_cases p2 (length (cx_tb cx))) as [Hp|Hp]; [lia|].
  rewrite expected_m.byte_at_ge in H58 by exact Hp. discriminate.
Qed.

(* the three branches of the loop body on c (atom 32): 0x815f4 bgeu (c - 9, s3 = 5), 0x8160c bne (c, s11 = ' '),
   0x81624 bne (c, '<') *)
Section b. Context {fx : YK11.FPState}.
Lemma d3_geu : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_GEU (sv_denot E (SOff 32 (-9))) (sv_denot E (SLit 5)) = negb ((c - 9) mod 2 ^ 64 <? 5).
Proof.
  intros E c H Hc. rewrite branch_geu_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
  unfold zcanon, M64. reflexivity.
Qed.
Lemma d3_ne32 : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SOff 32 0)) (sv_denot E (SLit 32)) = negb (c =? 32).
Proof. intros E c H Hc. rewrite branch_ne_U, (U_atom E 32 c H), U_SLit by lia. reflexivity. Qed.
Lemma d3_ne60 : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SOff 32 0)) (sv_denot E (SLit 60)) = negb (c =? 60).
Proof. intros E c H Hc. rewrite branch_ne_U, (U_atom E 32 c H), U_SLit by lia. reflexivity. Qed.
End b.

Ltac d3_dec HS Hc lem c E32 Rc :=
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    rewrite (lem Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.

(* the name's registers s4, s5, s2, s6, s1 on the paths that stay in the declaration *)
Definition d3_keepn (regs3 regs4 : bvmap 5 word) : Prop :=
  getr regs4 20 = getr regs3 20 /\ getr regs4 21 = getr regs3 21 /\ getr regs4 18 = getr regs3 18 /\
  getr regs4 22 = getr regs3 22 /\ getr regs4 9 = getr regs3 9.
Ltac d3_kp HS EE :=
  try unfold dd_keepc; try unfold d3_keepn;
  repeat match goal with |- _ /\ _ => split end; dd_regs HS EE.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD3c : dseg_D3c B.
Hypothesis SDN : dseg_N B.

(* ---- the entry: st_ok at D3 and the shadow entry of the checked byte, from dat_D3 ---- *)
Lemma d3_entry : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 (ManifestModel.byte_at (cx_tb cx) (S p2 + m))])
    ss_D3 (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs D3_Bx SH_D3 (Ereg regs3 [Z_to_bv 64 (ManifestModel.byte_at (cx_tb cx) (S p2 + m))])
    (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 HD.
  destruct HD as ((HB & HC & HSL & HSR & HSC & Hi) & HCR & HP2 & Hm & R20 & R21 & R18 & R22 & R9 & R12 & R24 & R26 & R23).
  pose proof (d3_le cx i a1 p1 p2 m HP2 Hm) as Hle.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _).
  destruct HSR as (R19 & R27 & R8). destruct HCR as (_ & _ & R5 & R6).
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (S p2 + m) HCt Hle) as (Vc & Rc).
  pose proof HCt as (_ & _ & _ & _ & Ham & HRA & _).
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *. set (c := ManifestModel.byte_at tb (S p2 + m)) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 c]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E12 : ew E 12 = Z_to_bv 64 (t + 1 + Z.of_nat p2 + Z.of_nat m))
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 12 12%bv eq_refl); exact R12).
  assert (U12 : bv_unsigned (ew E 12) = t + 1 + Z.of_nat p2 + Z.of_nat m)
    by (rewrite E12; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_D3. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 c]) with E.
    + unfold d3_regs.
      repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
        cbn [sv_denot];
        first [ exact R5 | exact R6 | exact R19 | exact R27 | exact R8
              | rewrite U12, R24; unfold w64; apply Z_to_bv64_eq_mod; f_equal; lia ].
    + vm_compute. reflexivity.
    + unfold d3_byte. apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (t + 1 + Z.of_nat p2 + Z.of_nat m) 0 1 (SOff 32 0) c);
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
        | cbn; lia |].
      replace (t + 1 + Z.of_nat p2 + Z.of_nat m + 0) with (t + Z.of_nat (S p2 + m)) by lia. exact Vc.
    + cbn. tauto.
    + split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U12, U25, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold FW_SB, SHADOW_OFF. repeat split; first [exact HFm | lia].
  - unfold sh_ok, SH_D3. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E D3_Bx 12 t (Z.of_nat (length tb) + 1)
      (t + 1 + Z.of_nat p2 + Z.of_nat m) 0 1).
    + exact HRA.
    + unfold D3_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 12 _ E12). lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

(* ---- the three exits ---- *)
(* the back edge: c is a space, D3 at m + 1 *)
Lemma d3_next : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = true ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  dd_keepc regs3 regs4 -> d3_keepn regs3 regs4 ->
  getr regs4 12 = w64 (cx_t cx + 1 + Z.of_nat p2 + Z.of_nat (S m)) ->
  getr regs4 24 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat (S m)) ->
  getr regs4 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat p2 - Z.of_nat (S m)) ->
  dat_D3 B cx i d f a1 p1 p2 (S m) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp HJ4 AV HK
    (N20 & N21 & N18 & N22 & N9) R12' R24' R26'.
  destruct HD as (HDC & HCR & HP2 & Hm & R20 & R21 & R18 & R22 & R9 & R12 & R24 & R26 & R23).
  destruct (dd_keepc_com B cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HCR HJ4 AV HK) as (HDC' & HCR' & Q23).
  split; [exact HDC'|]. split; [exact HCR'|]. split; [exact HP2|].
  split; [exact (dm_cw_next ManifestModel.is_space (cx_tb cx) (S p2) m dm_space0 Hm Hsp)|].
  split; [rewrite N20; exact R20|]. split; [rewrite N21; exact R21|]. split; [rewrite N18; exact R18|].
  split; [rewrite N22; exact R22|]. split; [rewrite N9; exact R9|].
  split; [exact R12'|]. split; [exact R24'|]. split; [exact R26'|]. rewrite Q23. exact R23.
Qed.

(* c = '<' (0x81624 not taken): D3c at 0x81630 with p3 = S p2 + m, s7 = s8 = text + S p3 *)
Lemma d3_exit_c : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = false ->
  ManifestModel.byte_at (cx_tb cx) (S p2 + m) = 60 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 19 = w64 5 -> getr regs4 27 = w64 32 -> getr regs4 8 = w64 (2 ^ 64 - 1) ->
  d3_keepn regs3 regs4 ->
  getr regs4 23 = w64 (cx_t cx + Z.of_nat (S (S p2 + m))) ->
  getr regs4 24 = w64 (cx_t cx + Z.of_nat (S (S p2 + m))) ->
  getr regs4 26 = w64 (cx_u cx - cx_t cx - Z.of_nat (S (S p2 + m))) ->
  dat_D3c B cx i d f a1 p1 p2 (S p2 + m) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp H60 HJ4 AV Q2 Q3 Q4 Q25 R19 R27 R8
    (N20 & N21 & N18 & N22 & N9) R23' R24' R26'.
  destruct HD as (HDC & HCR & HP2 & Hm & R20 & R21 & R18 & R22 & R9 & R12 & R24 & R26 & R23).
  split; [exact (dd_com_same B cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV Q2 Q3 Q4 Q25 R19 R27 R8)|].
  split.
  { split; [exact HP2|]. split; [|exact H60].
    rewrite (dm_cw_exact ManifestModel.is_space (cx_tb cx) (S p2) m Hm Hsp). reflexivity. }
  split; [rewrite N20; exact R20|]. split; [rewrite N21; exact R21|]. split; [rewrite N18; exact R18|].
  split; [rewrite N22; exact R22|]. split; [rewrite N9; exact R9|].
  split; [exact R23'|]. split; [exact R24' | exact R26'].
Qed.

(* c is neither a space nor '<' (0x81624 taken): EX_NEXT with s7 = i (decl = DNone) *)
Lemma d3_exit_N : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = false ->
  ManifestModel.byte_at (cx_tb cx) (S p2 + m) <> 60 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  dd_keepc regs3 regs4 ->
  dat_N B cx i d (pred f) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp H60 HJ4 AV HK.
  destruct HD as (HDC & HCR & HP2 & Hm & _ & _ & _ & _ & _ & _ & _ & _ & R23).
  destruct (dd_keepc_com B cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HCR HJ4 AV HK) as (HDC' & HCR' & Q23).
  pose proof HP2 as (((Hh & _ & Hs0) & E1) & E2 & H58).
  assert (Hdn : ManifestModel.decl (cx_tb cx) i = ManifestModel.DNone).
  { apply (dm_decl_lt (cx_tb cx) i (i + a1) p1 p2 (S p2 + m) Hh Hs0 E1 E2); [|exact H58|exact H60].
    rewrite (dm_cw_exact ManifestModel.is_space (cx_tb cx) (S p2) m Hm Hsp). reflexivity. }
  apply (dd_N_none B cx i d f ly3 S3 W3 regs4 mem4 md4 HDC' HCR'); [rewrite Q23; exact R23 | exact Hdn].
Qed.

(* ---- the loop: one iteration, its back edge by strong induction on |text| - (S p2 + m) ---- *)
Lemma d3_loop : forall n cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3,
  (length (cx_tb cx) - (S p2 + m) = n)%nat ->
  ex_seg_L_from B cx i -> dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D3 regs3 mem3 md3) (ex_post B cx).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 Hn HLF HD.
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (d3_entry cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 HD) as (HS & SHOK0).
  pose proof HD as (HDC & HCR & HP2 & Hm & R20 & R21 & R18 & R22 & R9 & R12 & R24 & R26 & R23).
  pose proof HDC as (HB & HC & HSL & HSR & HSC & Hi).
  pose proof HC as (HJ & _ & _ & _ & _ & _ & R25 & _ & _ & HCt & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  assert (FS : STK_expected = 8464) by reflexivity.
  pose proof (d3_le cx i a1 p1 p2 m HP2 Hm) as Hle.
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (S p2 + m) HCt Hle) as (_ & Rc).
  set (c := ManifestModel.byte_at (cx_tb cx) (S p2 + m)) in *.
  remember (Ereg regs3 [Z_to_bv 64 c]) as E eqn:HE.
  assert (EE : forall n0 (q : bv 5), Z.of_nat n0 = bv_unsigned q -> ew E n0 = getr regs3 q)
    by (intros n0 q Hn0; rewrite HE; apply ew_Ereg_nat; exact Hn0).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  clear HE.
  assert (E12 : ew E 12 = w64 (cx_t cx + 1 + Z.of_nat p2 + Z.of_nat m))
    by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E26 : ew E 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat p2 - Z.of_nat m))
    by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (SHOK : sh_ok tfibsegs D3_Bx SH_D3 E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))))) by exact SHOK0.
  clear SHOK0.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D3) with (Z_to_bv 64 EX_D3).
  (* 0x815d8 .. 0x815f4: the check of s8 - 1, the load of 0(a2), bgeu (c - 9, 5) *)
  aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan.
  { awr_ok_tac. }
  dd_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
  - (* (c - 9) mod 2^64 >=u 5: 0x8160c bne (c, ' ') *)
    d3_dec HS Hc d3_geu c E32 Rc. apply negb_true_iff in Hc. rename Hc into D1.
    aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan; [awr_ok_tac|]. dd_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
    + (* c <> ' ': not a space; 0x81620 a1 = '<', 0x81624 bne (c, '<') *)
      d3_dec HS Hc d3_ne32 c E32 Rc. apply negb_true_iff in Hc. rename Hc into D2.
      assert (SPF : ManifestModel.is_space c = false) by (rewrite (d3_space c Rc), D1, D2; reflexivity).
      aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan; [awr_ok_tac|]. dd_av W3 mem3.
      srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
      * (* c <> '<': EX_NEXT with s7 = i *)
        d3_dec HS Hc d3_ne60 c E32 Rc. apply negb_true_iff, Z.eqb_neq in Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_NEXT; [awr_ok_tac|]. dd_av W3 mem3. dd_mk HS.
        apply (SDN cx i i d (pred f) ly3 S3 W3 _ _ _ HLF (le_n i)).
        apply (d3_exit_N cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SPF Hc HJ AV).
        d3_kp HS EE.
      * (* c = '<': the guard 0x81628 (decided), s7 = a2 + 1, D3c (0x81630) with p3 = S p2 + m *)
        d3_dec HS Hc d3_ne60 c E32 Rc. apply negb_false_iff, Z.eqb_eq in Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3c; [awr_ok_tac|]. dd_av W3 mem3. dd_mk HS.
        eapply (SD3c cx i d f a1 p1 p2 (S p2 + m)%nat ly3 S3 W3 _ _ _ HLF).
        eapply (d3_exit_c cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SPF Hc HJ AV);
          d3_kp HS EE.
    + (* c = ' ': a space, 0x81610 j 0x815f8, the back edge through the guard 0x81604 (decided) *)
      d3_dec HS Hc d3_ne32 c E32 Rc. apply negb_false_iff in Hc.
      assert (SP : ManifestModel.is_space c = true) by (rewrite (d3_space c Rc), Hc; apply orb_true_r).
      clear Hc.
      pose proof (d3_lt (cx_tb cx) (S p2 + m) SP) as Hlt.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3; [awr_ok_tac|]. dd_av W3 mem3. dd_mk HS.
      eapply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d f a1 p1 p2 (S m) ly3 S3 W3);
        [lia | exact HLF |].
      eapply (d3_next cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SP HJ AV); d3_kp HS EE.
  - (* (c - 9) mod 2^64 <u 5: c is \t .. \r, a space, the back edge (0x815f8 .. 0x81604) *)
    d3_dec HS Hc d3_geu c E32 Rc. apply negb_false_iff in Hc.
    assert (SP : ManifestModel.is_space c = true) by (rewrite (d3_space c Rc), Hc; reflexivity).
    clear Hc.
    pose proof (d3_lt (cx_tb cx) (S p2 + m) SP) as Hlt.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3; [awr_ok_tac|]. dd_av W3 mem3. dd_mk HS.
    eapply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d f a1 p1 p2 (S m) ly3 S3 W3);
      [lia | exact HLF |].
    eapply (d3_next cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SP HJ AV); d3_kp HS EE.
Qed.

Theorem decl_D3_holds : dseg_D3 B.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 HLF HD.
  exact (d3_loop _ cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 eq_refl HLF HD).
Qed.
End W.

Check decl_D3_holds.
Print Assumptions decl_D3_holds.
