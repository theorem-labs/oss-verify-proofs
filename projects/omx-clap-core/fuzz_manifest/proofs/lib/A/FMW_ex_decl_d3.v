(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 332 of its 377 lines of code are new or changed and 222 lines of the source are left out. *)
(* G4.ExDecl.DeclD3B: expected's D3 loop (0x81454..0x8148c, fuzz_manifest.c:154-156) on fm.asan, dseg_D3 of
   FMW_ex_decl_base.v. The spaces after the declaration's ':' at p2: the byte c = text[S p2 + m] is checked
   (a0 = s11 - 1, shadow check, error path 0x81448..0x81450 not reached) and loaded from -1(s7) (s7 = s11 =
   text + 2 + p2 + m); ex_space c: s7, s11 += 1, s10 -= 1, back to D3 at m + 1 (0x81474..0x81480); c = '<': D3c at
   0x81490 with p3 = S p2 + m; else 0x814d0..0x814e0 (s7 = text, s1 = '@', s3 = a4 + 1 = i + 1) to EX_L at S i
   (decl = DNone by dm_decl_lt). The loop closes by strong induction on |text| - (S p2 + m). *)
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

(* ---- the symbolic state at D3 (0x81454): s9 (register 25) holds the shadow base (the token base D3_Bx); s0 = ' '
   and s2 = 5 pinned as literals; s11 (register 27) pinned to s7's atom 23 (both text + 2 + p2 + m); extra atom
   32 = text (the F + 0x58 slot, which the exit 0x814d0 reloads into s7), extra atom 33 = c, the byte at s7 - 1 ---- *)
Definition D3_Bx : sv := SOff 25 0.
Definition D3_Bspan : Z * Z := EX_Bspan.
Definition d3_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 8%bv (SLit 32)) 18%bv (SLit 5)) 27%bv (SOff 23 0).
Definition d3_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x58 0x60 0x58 0x58 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))].
Definition d3_byte : YP09.region :=
  YP09.mkRegion (Some 23%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 33 0))].
Definition ss_D3 : sstate :=
  mkSS EX_D3 d3_regs [d3_frame; d3_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF 4096 (2 ^ 47 - 16) 0);
              (25%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 0 255 0)] [] []).
Definition SH_D3 : list shent := [mkSHE 23 (-1) 0].

(* ---- pure facts ---- *)
(* ex_space as the code tests it: (c - 9) mod 2^64 <u 5, or c = ' ' (by enumeration of the 256 byte values, after
   G4.ExHead's FMW_ex_head_m.v hd_m_space) *)
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

Lemma d3_w64_add : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
  intros x k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l; [reflexivity|]. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

(* the three branches of the loop body on c (atom 33): 0x81470 bgeu (c - 9, s2 = 5), 0x81484 beq (c, s0 = ' '),
   0x8148c bne (c, '<') *)
Section b. Context {fx : YK11.FPState}.
Lemma d3_geu : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_GEU (sv_denot E (SOff 33 (-9))) (sv_denot E (SLit 5)) = negb ((c - 9) mod 2 ^ 64 <? 5).
Proof.
  intros E c H Hc. rewrite branch_geu_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
  unfold zcanon, M64. reflexivity.
Qed.
Lemma d3_eq32 : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_EQ (sv_denot E (SOff 33 0)) (sv_denot E (SLit 32)) = (c =? 32).
Proof. intros E c H Hc. rewrite branch_eq_U, (U_atom E 33 c H), U_SLit by lia. reflexivity. Qed.
Lemma d3_ne60 : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SOff 33 0)) (sv_denot E (SLit 60)) = negb (c =? 60).
Proof. intros E c H Hc. rewrite branch_ne_U, (U_atom E 33 c H), U_SLit by lia. reflexivity. Qed.
End b.

(* ---- the walk tactics of FMW_plain.v (fw_reg, pl_av, pl_mk, pl_g), as G4.ExHead's FMW_ex_head_t.v copies them ---- *)
Ltac d3_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac d3_av W mem1 :=
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
Ltac d3_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac d3_g HS :=
  lazymatch goal with |- getr _ ?r = _ => d3_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac d3_dec HS Hc lem c E33 Rc :=
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    rewrite (lem Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E33) Rc) in Hc end.

(* the registers every run of the loop keeps: atoms 2, 3, 4, 25, 22, 15, 16 and the pinned s0 = ' ', s2 = 5 *)
Definition d3_keep (regs3 regs4 : bvmap 5 word) : Prop :=
  getr regs4 2 = getr regs3 2 /\ getr regs4 3 = getr regs3 3 /\ getr regs4 4 = getr regs3 4 /\
  getr regs4 25 = getr regs3 25 /\ getr regs4 22 = getr regs3 22 /\ getr regs4 15 = getr regs3 15 /\
  getr regs4 16 = getr regs3 16 /\ getr regs4 8 = w64 32 /\ getr regs4 18 = w64 5.
(* and the name's registers s4, a4, s5, s8, s3, s1 on the paths that stay in the declaration *)
Definition d3_keepn (regs3 regs4 : bvmap 5 word) : Prop :=
  getr regs4 20 = getr regs3 20 /\ getr regs4 14 = getr regs3 14 /\ getr regs4 21 = getr regs3 21 /\
  getr regs4 24 = getr regs3 24 /\ getr regs4 19 = getr regs3 19 /\ getr regs4 9 = getr regs3 9.
Ltac d3_kp HS EE :=
  try unfold d3_keep; try unfold d3_keepn;
  repeat match goal with |- _ /\ _ => split end; d3_g HS; first [apply EE; reflexivity | reflexivity].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD3c : dseg_D3c B.

(* ---- the entry: st_ok at D3 and the shadow entry of the checked byte, from dat_D3 ---- *)
Lemma d3_entry : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 (cx_t cx); Z_to_bv 64 (ManifestModel.byte_at (cx_tb cx) (S p2 + m))])
    ss_D3 (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs D3_Bx SH_D3
    (Ereg regs3 [Z_to_bv 64 (cx_t cx); Z_to_bv 64 (ManifestModel.byte_at (cx_tb cx) (S p2 + m))])
    (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 HD.
  destruct HD as (HDC & HP2 & Hm & R20 & R14 & R21 & R24 & R19 & R9 & R23 & R27 & R26 & R15 & R16).
  pose proof (d3_le cx i a1 p1 p2 m HP2 Hm) as Hle.
  destruct HDC as (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _).
  destruct HSL as (_ & _ & _ & _ & _ & _ & _ & S58 & _).
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (S p2 + m) HCt Hle) as (Vc & Rc).
  pose proof HCt as (_ & _ & _ & _ & Ham & HRA & _).
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *. set (c := ManifestModel.byte_at tb (S p2 + m)) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 t; Z_to_bv 64 c]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E23 : ew E 23 = Z_to_bv 64 (t + 2 + Z.of_nat p2 + Z.of_nat m))
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl); exact R23).
  assert (U23 : bv_unsigned (ew E 23) = t + 2 + Z.of_nat p2 + Z.of_nat m)
    by (rewrite E23; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 t) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = t) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  - unfold ss_D3. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 t; Z_to_bv 64 c]) with E.
    + unfold d3_regs.
      repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
        cbn [sv_denot]; first [exact R8 | exact R18 | rewrite U23, Z.add_0_r; exact R27].
    + vm_compute. reflexivity.
    + unfold d3_frame, d3_byte. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x58 8 (SOff 32 0) t);
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact S58].
      * rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (t + 2 + Z.of_nat p2 + Z.of_nat m) (-1) 1 (SOff 33 0) c);
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        replace (t + 2 + Z.of_nat p2 + Z.of_nat m + -1) with (t + Z.of_nat (S p2 + m)) by lia. exact Vc.
    + apply pairwise_disjoint_of_extents. unfold d3_frame, d3_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U23, U25, U33. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold FW_SB, SHADOW_OFF. repeat split; first [exact HFm | lia].
  - unfold sh_ok, SH_D3. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E D3_Bx 23 t (Z.of_nat (length tb) + 1)
      (t + 2 + Z.of_nat p2 + Z.of_nat m) (-1) 0).
    + exact HRA.
    + unfold D3_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 23 _ E23). lia.
    + lia.
    + lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

(* ---- the cut's common facts after a run that writes nothing ---- *)
Lemma d3_dd : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dd_com B cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  d3_keep regs3 regs4 ->
  dd_com B cx i d f ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi) HJ4 AV
    (K2 & K3 & K4 & K25 & K22 & K15 & K16 & K8 & K18).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  split; [exact HB|]. split.
  { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4); [|exact K2|exact K3|exact K4|exact K25].
    intros a Ha _ _ _. exact (AV a Ha). }
  split; [apply (dd_slots_kept B cx W3 mem3 mem4 d HB HSL); intros a Ha; apply AV; lia|].
  split; [rewrite K22; exact R22|]. split; [exact K18|]. split; [exact K8|]. split; [exact HSC | exact Hi].
Qed.

(* ---- the three exits ---- *)
(* the back edge 0x81480: c is a space, D3 at m + 1 *)
Lemma d3_next : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = true ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  d3_keep regs3 regs4 -> d3_keepn regs3 regs4 ->
  getr regs4 23 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat (S m)) ->
  getr regs4 27 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat (S m)) ->
  getr regs4 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat p2 - Z.of_nat (S m)) ->
  dat_D3 B cx i d f a1 p1 p2 (S m) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp HJ4 AV HK
    (N20 & N14 & N21 & N24 & N19 & N9) R23' R27' R26'.
  destruct HD as (HDC & HP2 & Hm & R20 & R14 & R21 & R24 & R19 & R9 & R23 & R27 & R26 & R15 & R16).
  pose proof HK as (_ & _ & _ & _ & _ & K15 & K16 & _).
  split; [exact (d3_dd cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV HK)|].
  split; [exact HP2|].
  split; [exact (dm_cw_next ManifestModel.is_space (cx_tb cx) (S p2) m dm_space0 Hm Hsp)|].
  split; [rewrite N20; exact R20|]. split; [rewrite N14; exact R14|]. split; [rewrite N21; exact R21|].
  split; [rewrite N24; exact R24|]. split; [rewrite N19; exact R19|]. split; [rewrite N9; exact R9|].
  split; [exact R23'|]. split; [exact R27'|]. split; [exact R26'|].
  split; [rewrite K15; exact R15 | rewrite K16; exact R16].
Qed.

(* c = '<' (0x8148c not taken): D3c at 0x81490 with p3 = S p2 + m *)
Lemma d3_exit_c : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = false ->
  ManifestModel.byte_at (cx_tb cx) (S p2 + m) = 60 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  d3_keep regs3 regs4 -> d3_keepn regs3 regs4 ->
  getr regs4 23 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat m) ->
  getr regs4 27 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat m) ->
  getr regs4 26 = getr regs3 26 ->
  dat_D3c B cx i d f a1 p1 p2 (S p2 + m) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp H60 HJ4 AV HK
    (N20 & N14 & N21 & N24 & N19 & N9) R23' R27' N26.
  destruct HD as (HDC & HP2 & Hm & R20 & R14 & R21 & R24 & R19 & R9 & R23 & R27 & R26 & R15 & R16).
  split; [exact (d3_dd cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV HK)|].
  split.
  { split; [exact HP2|]. split; [|exact H60].
    rewrite (dm_cw_exact ManifestModel.is_space (cx_tb cx) (S p2) m Hm Hsp). reflexivity. }
  split; [rewrite N20; exact R20|]. split; [rewrite N21; exact R21|]. split; [rewrite N24; exact R24|].
  split; [rewrite N19; exact R19|]. split; [rewrite N9; exact R9|].
  split; [rewrite R23'; unfold w64; f_equal; lia|]. split; [rewrite R27'; unfold w64; f_equal; lia|].
  rewrite N26, R26. unfold w64; f_equal; lia.
Qed.

(* c is neither a space nor '<' (0x8148c taken): 0x814d0 s7 = text, s1 = '@', s3 = a4 + 1; EX_L at S i *)
Lemma d3_exit_L : forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D3 B cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (S p2 + m)) = false ->
  ManifestModel.byte_at (cx_tb cx) (S p2 + m) <> 60 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  d3_keep regs3 regs4 ->
  getr regs4 23 = w64 (cx_t cx) -> getr regs4 19 = w64 (Z.of_nat (S i)) -> getr regs4 9 = w64 64 ->
  ex_at_L B cx (S i) d (pred f) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HD Hsp H60 HJ4 AV HK R23' R19' R9'.
  pose proof HD as (HDC & HP2 & Hm & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15 & R16).
  pose proof (d3_dd cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV HK)
    as (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi).
  pose proof HK as (_ & _ & _ & _ & _ & K15 & K16 & _).
  pose proof HP2 as (((Hh & _ & Hs0) & E1) & E2 & H58).
  assert (Hdn : ManifestModel.decl (cx_tb cx) i = ManifestModel.DNone).
  { apply (dm_decl_lt (cx_tb cx) i (i + a1) p1 p2 (S p2 + m) Hh Hs0 E1 E2); [|exact H58|exact H60].
    rewrite (dm_cw_exact ManifestModel.is_space (cx_tb cx) (S p2) m Hm Hsp). reflexivity. }
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|].
  split; [split; [exact R23'|]; split; [exact R22|]; split; [exact R18 | exact R8]|].
  split; [eapply dd_scan_none; eassumption|].
  split; [exact R19'|]. split; [exact R9'|]. split; [rewrite K15; exact R15 | rewrite K16; exact R16].
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
  pose proof HD as (HDC & HP2 & Hm & R20 & R14 & R21 & R24 & R19 & R9 & R23 & R27 & R26 & R15 & R16).
  pose proof HDC as (HB & HC & HSL & R22 & R18 & R8 & HSC & Hi).
  pose proof HC as (HJ & _ & _ & _ & _ & _ & R25 & _ & _ & HCt & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  assert (FS : STK_expected = 8432) by reflexivity.
  pose proof (d3_le cx i a1 p1 p2 m HP2 Hm) as Hle.
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (S p2 + m) HCt Hle) as (_ & Rc).
  set (c := ManifestModel.byte_at (cx_tb cx) (S p2 + m)) in *.
  remember (Ereg regs3 [Z_to_bv 64 (cx_t cx); Z_to_bv 64 c]) as E eqn:HE.
  assert (EE : forall n0 (q : bv 5), Z.of_nat n0 = bv_unsigned q -> ew E n0 = getr regs3 q)
    by (intros n0 q Hn0; rewrite HE; apply ew_Ereg_nat; exact Hn0).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  clear HE.
  assert (SHOK : sh_ok tfibsegs D3_Bx SH_D3 E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))))) by exact SHOK0.
  clear SHOK0.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D3) with (Z_to_bv 64 EX_D3).
  (* 0x81454 .. 0x81470: the check of s11 - 1, the load of -1(s7), bgeu (c - 9, 5) *)
  aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan.
  { awr_ok_tac. }
  d3_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
  - (* (c - 9) mod 2^64 >=u 5: 0x81484 beq (c, ' ') *)
    d3_dec HS Hc d3_geu c E33 Rc. apply negb_true_iff in Hc. rename Hc into D1.
    aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan; [awr_ok_tac|]. d3_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
    + (* c = ' ': a space, the back edge *)
      d3_dec HS Hc d3_eq32 c E33 Rc.
      assert (SP : ManifestModel.is_space c = true) by (rewrite (d3_space c Rc), Hc; apply orb_true_r).
      clear Hc.
      pose proof (d3_lt (cx_tb cx) (S p2 + m) SP) as Hlt.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3; [awr_ok_tac|]. d3_av W3 mem3. d3_mk HS.
      eapply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d f a1 p1 p2 (S m) ly3 S3 W3);
        [lia | exact HLF |].
      eapply (d3_next cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3);
        [exact HD | exact SP | exact HJ | exact AV | d3_kp HS EE | d3_kp HS EE | | | ].
      * d3_g HS. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal; lia.
      * d3_g HS. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal; lia.
      * d3_g HS. rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite d3_w64_add. f_equal; lia.
    + d3_dec HS Hc d3_eq32 c E33 Rc. rename Hc into D2.
      assert (SPF : ManifestModel.is_space c = false) by (rewrite (d3_space c Rc), D1, D2; reflexivity).
      (* 0x81488 a1 = '<', 0x8148c bne (c, '<') *)
      aj_run_tok EX_tbl_ok HS HJ SHOK D3_Bspan; [awr_ok_tac|]. d3_av W3 mem3.
      srr_branch_tok EX_tbl_ok HS SHOK D3_Bspan.
      * (* c <> '<': 0x814d0 .. 0x814e0, EX_L at S i *)
        d3_dec HS Hc d3_ne60 c E33 Rc. apply negb_true_iff, Z.eqb_neq in Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_L; [awr_ok_tac|]. d3_av W3 mem3. d3_mk HS.
        eapply (HLF (S i) d (pred f)); [lia|].
        eapply (d3_exit_L cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3);
          [exact HD | exact SPF | exact Hc | exact HJ | exact AV | d3_kp HS EE | | | ].
        -- d3_g HS. exact E32.
        -- d3_g HS. rewrite (EE 14%nat 14%bv eq_refl), R14. unfold w64.
           rewrite unsigned_lit_small by lia. f_equal; lia.
        -- d3_g HS. reflexivity.
      * (* c = '<': D3c (0x81490) with p3 = S p2 + m *)
        d3_dec HS Hc d3_ne60 c E33 Rc. apply negb_false_iff, Z.eqb_eq in Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3c; [awr_ok_tac|]. d3_av W3 mem3. d3_mk HS.
        eapply (SD3c cx i d f a1 p1 p2 (S p2 + m)%nat ly3 S3 W3 _ _ _ HLF).
        eapply (d3_exit_c cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3);
          [exact HD | exact SPF | exact Hc | exact HJ | exact AV | d3_kp HS EE | d3_kp HS EE | | | ].
        -- d3_g HS. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
        -- d3_g HS. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
        -- d3_g HS. apply EE. reflexivity.
  - (* (c - 9) mod 2^64 <u 5: c is \t .. \r, a space, the back edge (0x81474 .. 0x81480) *)
    d3_dec HS Hc d3_geu c E33 Rc. apply negb_false_iff in Hc.
    assert (SP : ManifestModel.is_space c = true) by (rewrite (d3_space c Rc), Hc; reflexivity).
    clear Hc.
    pose proof (d3_lt (cx_tb cx) (S p2 + m) SP) as Hlt.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK D3_Bspan EX_D3; [awr_ok_tac|]. d3_av W3 mem3. d3_mk HS.
    eapply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d f a1 p1 p2 (S m) ly3 S3 W3);
      [lia | exact HLF |].
    eapply (d3_next cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3);
      [exact HD | exact SP | exact HJ | exact AV | d3_kp HS EE | d3_kp HS EE | | | ].
    + d3_g HS. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
    + d3_g HS. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
    + d3_g HS. rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite d3_w64_add. f_equal; lia.
Qed.

Theorem decl_D3_holds : dseg_D3 B.
Proof.
  intros cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 HLF HD.
  exact (d3_loop _ cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 eq_refl HLF HD).
Qed.
End W.

Print Assumptions decl_D3_holds.
