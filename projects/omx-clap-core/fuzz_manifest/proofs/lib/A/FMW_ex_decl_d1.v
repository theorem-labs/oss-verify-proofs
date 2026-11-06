(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 309 of its 356 lines of code are new or changed and 220 lines of the source are left out. *)
(* G4.ExDecl.DeclD1B: the space loop at D1 (0x81380..0x813d8, fuzz_manifest.c:147-148) on fm.asan: dseg_D1.
   One iteration: the shadow check of a0 = text + q (q = i + a1 + k), lbu a1 = text[q] (via s4 = a0),
   `addi a2, a1, -9; bgeu a2, s2 (= 5)` and `bne a1, s0 (= ' ')` decide ManifestModel.is_space; a space goes back to
   D1 at k + 1 (a0, s4, s7, s11 += 1, s10 -= 1), else 0x813c8..0x813d8 (a4 = s3 = i, s5 = 0, s8 = 1,
   s3 = s1 = ld F+0x40 = text + 1) reach D2 with p1 = q, j = 0. The loop by strong induction on |text| - q.
   Patterns after FMW_plain.v (L_entry, pl_loop, pl_av/pl_mk/pl_g, fw_reg) and G4.ExHead's FMW_ex_head_e.v (hd_L_entry:
   registers as atoms, s9 as the shadow base) / FMW_ex_head_t.v (ht_ltu, ht_eq32) / FMW_ex_head_m.v (hd_m_space). *)
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

(* ---- the symbolic state at D1: registers are their own atoms (sr_atoms), a0 = s4 (atom 20) = text + q,
   s0 = ' ', s2 = 5; atom 32 = text[q], atom 33 = text + 1 (the slot F+0x40, read on the exit path) ---- *)
Definition D1_Bx : sv := SOff 25 0.
Definition d1_pins (sr : list sv) : list sv :=
  sr_set (sr_set (sr_set sr 8%bv (SLit 32)) 18%bv (SLit 5)) 10%bv (SOff 20 0).
Definition d1_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x40 0x48 0x40 0x40 [YP09.mkChunk 0x40 (CVal 8 (SOff 33 0))].
Definition d1_byte : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_D1 : sstate :=
  mkSS EX_D1 (d1_pins sr_atoms) [d1_frame; d1_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF FW_SB FW_SB 0); (20%nat, mkAF 4096 (2 ^ 47 - 16) 0);
              (32%nat, mkAF 0 255 0)] [] []).
Definition SH_D1 : list shent := [mkSHE 20 0 1].
Definition d1_extra (t c : Z) : list word := [Z_to_bv 64 c; Z_to_bv 64 (t + 1)].

(* ---- pure facts ---- *)
(* ManifestModel.is_space as the two branches decide it (after G4.ExHead's FMW_ex_head_m.v hd_m_space) *)
Lemma d1_space : forall c, 0 <= c < 256 ->
  ManifestModel.is_space c = (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (ManifestModel.is_space c) (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

(* the head word ends on a space inside the text, so q = p0 + k <= |text| *)
Lemma d1_q : forall cx i a1 k, dm_p0 cx i a1 ->
  (k <= ManifestModel.count_while ManifestModel.is_space (skipn (i + a1) (cx_tb cx)))%nat ->
  (i + a1 + k <= length (cx_tb cx))%nat.
Proof.
  intros cx i a1 k (_ & _ & Hs) Hk.
  pose proof (dm_cw_le ManifestModel.is_space (cx_tb cx) (i + a1)) as Hle.
  destruct (Nat.lt_ge_cases (i + a1) (length (cx_tb cx))) as [H|H]; [lia|].
  rewrite (expected_m.byte_at_ge _ _ H) in Hs. vm_compute in Hs. discriminate Hs.
Qed.

Lemma d1_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l; [reflexivity|]. unfold bv_modulus. lia.
Qed.

(* the two branches of the loop body on c = text[q] (atom 32), after FMW_ex_head_t.v ht_ltu / ht_eq32 *)
Section b. Context {fx : YK11.FPState}.
Lemma d1_geu : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_GEU (sv_denot E (SOff 32 (-9))) (sv_denot E (SLit 5)) = negb ((c - 9) mod 2 ^ 64 <? 5).
Proof.
  intros E c H Hc. rewrite branch_geu_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
  unfold zcanon, M64. reflexivity.
Qed.
Lemma d1_ne32 : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SOff 32 0)) (sv_denot E (SLit 32)) = negb (c =? 32).
Proof. intros E c H Hc. rewrite branch_ne_U, (U_atom E 32 c H), U_SLit by lia. reflexivity. Qed.
End b.

(* ---- walk tactics (copied from FMW_plain.v fw_reg / pl_av / pl_mk / pl_g) ---- *)
Ltac d1_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac d1_av W mem1 :=
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
Ltac d1_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac d1_g HS :=
  lazymatch goal with |- getr _ ?r = _ => d1_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* a register of the run's end state: its atom's value at the entry (the E<n> equations), then arithmetic *)
Ltac d1_rg HS :=
  d1_g HS;
  repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end;
  first [ reflexivity | unfold w64; rewrite ?d1_off; first [reflexivity | f_equal; lia] ].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD2 : dseg_D2 B.

Lemma d1_cfg : forall W pc regs mem md (Q : world tfibsegs -> config -> Prop),
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

(* ---- the entry state at D1 from dat_D1 ---- *)
Lemma d1_entry : forall cx i d f a1 k ly3 S3 W3 regs3 mem3 md3,
  dat_D1 B cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (d1_extra (cx_t cx) (ManifestModel.byte_at (cx_tb cx) (i + a1 + k)))) ss_D1
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D1) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs D1_Bx SH_D1 (Ereg regs3 (d1_extra (cx_t cx) (ManifestModel.byte_at (cx_tb cx) (i + a1 + k))))
    (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 HD.
  destruct HD as ((HB & HC & HSL & R22 & R18 & R8 & HSC & Hi) & Hp0 & Hk & R10 & R20 & R23 & R27 & R26 & R19 & R9
    & R15 & R16).
  pose proof (d1_q cx i a1 k Hp0 Hk) as Hq.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _).
  destruct HSL as (_ & _ & _ & _ & S40 & _).
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i + a1 + k) HCt Hq) as (Vc & Rc).
  pose proof HCt as (_ & _ & _ & _ & Ham & HRA & _).
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *. set (q := (i + a1 + k)%nat) in *.
  set (c := ManifestModel.byte_at tb q) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (d1_extra t c)).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E20 : ew E 20 = Z_to_bv 64 (t + Z.of_nat q))
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl); exact R20).
  assert (U20 : bv_unsigned (ew E 20) = t + Z.of_nat q) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 (t + 1)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (U33 : bv_unsigned (ew E 33) = t + 1) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  - unfold ss_D1. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d1_extra t c)) with E.
    + unfold d1_pins.
      repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
        cbn [sv_denot];
        first [ exact R8 | exact R18
              | rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E20; exact R10 ].
    + vm_compute. reflexivity.
    + unfold d1_frame, d1_byte. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x40 8 (SOff 33 0) (t + 1));
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact S40].
      * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (t + Z.of_nat q) 0 1 (SOff 32 0) c);
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        rewrite Z.add_0_r. exact Vc.
    + apply pairwise_disjoint_of_extents. unfold d1_frame, d1_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U20.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U25, U20, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold FW_SB, SHADOW_OFF. repeat split; first [exact HFm | lia].
  - unfold sh_ok, SH_D1. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E D1_Bx 20 t (Z.of_nat (length tb) + 1) (t + Z.of_nat q) 0 1).
    + exact HRA.
    + unfold D1_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 20 _ E20). lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

(* ---- the cut facts at the run's end: memory unchanged, the kept registers ---- *)
Lemma d1_dd : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dd_com B cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 22 = w64 6 -> getr regs4 18 = w64 5 -> getr regs4 8 = w64 32 ->
  dd_com B cx i d f ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HB & HC & HSL & _ & _ & _ & HSC & Hi) HJ4 AV
    Q2 Q3 Q4 Q25 R22 R18 R8.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _). assert (FS : STK_expected = 8432) by reflexivity.
  split; [exact HB|].
  split; [exact (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4
                  (fun a Ha _ _ _ => AV a Ha) Q2 Q3 Q4 Q25)|].
  split; [apply (dd_slots_kept B cx W3 mem3 mem4 d HB HSL); intros a Ha; apply AV; lia|].
  split; [exact R22|]. split; [exact R18|]. split; [exact R8|]. split; [exact HSC | exact Hi].
Qed.

(* the back edge: a space at q, D1 at k + 1 *)
Lemma d1_back : forall cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D1 B cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (i + a1 + k)) = true ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 22 = w64 6 -> getr regs4 18 = w64 5 -> getr regs4 8 = w64 32 ->
  getr regs4 10 = w64 (cx_t cx + Z.of_nat (i + a1 + S k)) ->
  getr regs4 20 = w64 (cx_t cx + Z.of_nat (i + a1 + S k)) ->
  getr regs4 23 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + S k)) ->
  getr regs4 27 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + S k)) ->
  getr regs4 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat (i + a1 + S k)) ->
  getr regs4 19 = w64 (Z.of_nat i) -> getr regs4 9 = w64 64 -> getr regs4 15 = w64 58 ->
  getr regs4 16 = w64 EX_MASK1 ->
  dat_D1 B cx i d f a1 (S k) ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HDC & Hp0 & Hk & _) Hsp HJ4 AV Q2 Q3 Q4 Q25
    R22 R18 R8 R10 R20 R23 R27 R26 R19 R9 R15 R16.
  split; [exact (d1_dd cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV Q2 Q3 Q4 Q25 R22 R18 R8)|].
  split; [exact Hp0|].
  split; [apply dm_cw_next; [reflexivity | exact Hk | exact Hsp]|].
  repeat (split; [assumption|]). assumption.
Qed.

(* the exit: not a space at q, D2 with p1 = q (the count is k), j = 0 *)
Lemma d1_exit : forall cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dat_D1 B cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 ->
  ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (i + a1 + k)) = false ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 22 = w64 6 -> getr regs4 18 = w64 5 -> getr regs4 8 = w64 32 ->
  getr regs4 11 = w64 (ManifestModel.byte_at (cx_tb cx) (i + a1 + k)) ->
  getr regs4 10 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) -> getr regs4 20 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) ->
  getr regs4 14 = w64 (Z.of_nat i) -> getr regs4 21 = w64 (Z.of_nat 0) -> getr regs4 24 = w64 (1 + Z.of_nat 0) ->
  getr regs4 19 = w64 (cx_t cx + 1 + Z.of_nat 0) -> getr regs4 9 = w64 (cx_t cx + 1 + Z.of_nat 0) ->
  getr regs4 23 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k) + Z.of_nat 0) ->
  getr regs4 27 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k) + Z.of_nat 0) ->
  getr regs4 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat (i + a1 + k) - Z.of_nat 0) ->
  getr regs4 15 = w64 58 -> getr regs4 16 = w64 EX_MASK1 ->
  dat_D2 B cx i d f a1 (i + a1 + k) 0 ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HDC & Hp0 & Hk & _) Hsp HJ4 AV Q2 Q3 Q4 Q25
    R22 R18 R8 R11 R10 R20 R14 R21 R24 R19 R9 R23 R27 R26 R15 R16.
  split; [exact (d1_dd cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV Q2 Q3 Q4 Q25 R22 R18 R8)|].
  split; [split; [exact Hp0 | rewrite (dm_cw_exact _ _ _ _ Hk Hsp); reflexivity]|].
  split; [lia|].
  split; [rewrite Nat.add_0_r; exact R11|].
  repeat (split; [assumption|]). assumption.
Qed.

(* ---- the loop: one iteration from dat_D1, re-entry by strong induction on |text| - q ---- *)
Lemma d1_loop : forall r cx i d f a1 k ly3 S3 W3 regs3 mem3 md3,
  r = (length (cx_tb cx) - (i + a1 + k))%nat ->
  ex_seg_L_from B cx i -> dat_D1 B cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D1 regs3 mem3 md3) (ex_post B cx).
Proof.
  induction r as [r IH] using lt_wf_ind.
  intros cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 Hr HLF HD.
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HD as ((HB & HC & HSL & R22 & R18 & R8 & HSC & Hi) & Hp0 & Hk & R10 & R20 & R23 & R27 & R26 & R19 & R9
    & R15 & R16).
  pose proof (d1_q cx i a1 k Hp0 Hk) as Hq.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof (dd_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i + a1 + k) HCt Hq) as (_ & Rc).
  pose proof (d1_entry cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 HD) as [HS SHOK].
  set (c := ManifestModel.byte_at (cx_tb cx) (i + a1 + k)) in *.
  remember (Ereg regs3 (d1_extra (cx_t cx) c)) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = w64 (cx_t cx + 1)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  clear HE.
  assert (E2 : ew E 2 = getr regs3 2) by (apply EE; reflexivity).
  assert (E3 : ew E 3 = getr regs3 3) by (apply EE; reflexivity).
  assert (E4 : ew E 4 = getr regs3 4) by (apply EE; reflexivity).
  assert (E25 : ew E 25 = getr regs3 25) by (apply EE; reflexivity).
  assert (E22 : ew E 22 = w64 6) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (E19 : ew E 19 = w64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E9 : ew E 9 = w64 64) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E15 : ew E 15 = w64 58) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 EX_MASK1) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
  assert (E20 : ew E 20 = w64 (cx_t cx + Z.of_nat (i + a1 + k))) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 23 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k)))
    by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (E27 : ew E 27 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k)))
    by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (E26 : ew E 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat (i + a1 + k)))
    by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  clear EE.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change (mrestrict (w_H W3) mem3)
    with (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D1) mem3 (seg_rom tfibsegs)))) in SHOK.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D1) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D1) with (Z_to_bv 64 EX_D1).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  d1_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  - (* (c - 9) >=u 5: not \t..\r; the ' ' test *)
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      rewrite (d1_geu Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.
    apply Bool.negb_true_iff in Hc. rename Hc into G1.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
    { awr_ok_tac. }
    d1_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    + (* c <> ' ': not a space, D2 *)
      lazymatch type of HS with st_ok _ ?Ex _ _ =>
        rewrite (d1_ne32 Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.
      apply Bool.negb_true_iff in Hc.
      assert (SP : ManifestModel.is_space c = false) by (rewrite (d1_space c Rc), G1, Hc; reflexivity).
      clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_D2; [awr_ok_tac|]. d1_av W3 mem3.
      d1_mk HS.
      apply (d1_cfg W3 EX_D2).
      refine (SD2 cx i d f a1 (i + a1 + k)%nat 0%nat ly3 S3 W3 _ _ _ HLF _).
      refine (d1_exit cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SP HJ AV
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      all: d1_rg HS.
    + (* c = ' ': a space, back to D1 *)
      lazymatch type of HS with st_ok _ ?Ex _ _ =>
        rewrite (d1_ne32 Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.
      apply Bool.negb_false_iff in Hc.
      assert (SP : ManifestModel.is_space c = true) by (rewrite (d1_space c Rc), G1, Hc; reflexivity).
      clear Hc.
      assert (Hn : (S k <= ManifestModel.count_while ManifestModel.is_space (skipn (i + a1) (cx_tb cx)))%nat)
        by (apply dm_cw_next; [reflexivity | exact Hk | exact SP]).
      pose proof (dm_cw_in ManifestModel.is_space (cx_tb cx) (i + a1) k ltac:(lia)) as Hlt.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_D1; [awr_ok_tac|]. d1_av W3 mem3.
      d1_mk HS.
      apply (d1_cfg W3 EX_D1).
      refine (IH (length (cx_tb cx) - (i + a1 + S k))%nat ltac:(lia) cx i d f a1 (S k) ly3 S3 W3 _ _ _
        eq_refl HLF _).
      refine (d1_back cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SP HJ AV
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      all: d1_rg HS.
  - (* (c - 9) <u 5: \t..\r, a space, back to D1 *)
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      rewrite (d1_geu Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.
    apply Bool.negb_false_iff in Hc.
    assert (SP : ManifestModel.is_space c = true) by (rewrite (d1_space c Rc), Hc; reflexivity).
    clear Hc.
    assert (Hn : (S k <= ManifestModel.count_while ManifestModel.is_space (skipn (i + a1) (cx_tb cx)))%nat)
      by (apply dm_cw_next; [reflexivity | exact Hk | exact SP]).
    pose proof (dm_cw_in ManifestModel.is_space (cx_tb cx) (i + a1) k ltac:(lia)) as Hlt.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_D1; [awr_ok_tac|]. d1_av W3 mem3.
    d1_mk HS.
    apply (d1_cfg W3 EX_D1).
    refine (IH (length (cx_tb cx) - (i + a1 + S k))%nat ltac:(lia) cx i d f a1 (S k) ly3 S3 W3 _ _ _
      eq_refl HLF _).
    refine (d1_back cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 _ _ _ HD SP HJ AV
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: d1_rg HS.
Qed.

Theorem decl_D1_holds : dseg_D1 B.
Proof.
  intros cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 HLF HD.
  exact (d1_loop _ cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 eq_refl HLF HD).
Qed.
End W.

Print Assumptions decl_D1_holds.
