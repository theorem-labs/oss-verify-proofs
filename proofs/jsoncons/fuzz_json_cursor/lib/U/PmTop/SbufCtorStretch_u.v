(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_sbufctor_csrc_u Cut_sbufctor_b_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SBT.
Definition R_LOC : Z := 0x40c5c.       Definition R_ASSIGN : Z := 0x40ca0.     Definition RET : Z := 0x40cc8.
Definition EXT : Z := 0x64744.         Definition EXT_R_MOVE : Z := 0x6478c.   Definition EXT_R_NEW : Z := 0x647bc.    Definition EXT_R_CPY : Z := 0x647cc.    Definition EXT_RET : Z := 0x64804.
Definition MEMMOVE : Z := 0xb7c98.     Definition MEMCPY : Z := 0xb7894.
Definition FRAME : Z := 64.            Definition EFRAME : Z := 48.
End SBT.

Module SBS.
Module G := Cut_sbufctor_csrc_u.
Module GB := Cut_sbufctor_b_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_sb : CL.is_ret_at RSEGS SBT.RET. Proof. CL.solve_is_ret. Qed.
Lemma ret_ext : CL.is_ret_at RSEGS SBT.EXT_RET. Proof. CL.solve_is_ret. Qed.

Definition KO6 : list nat := [3; 4; 22; 23; 24; 25; 26; 27]%nat.
Definition KO5 : list nat := [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition sb_live (R : bvmap 5 word) (SB so : Z) : Prop := getr R 8%bv = Z_to_bv 64 SB /\ getr R 19%bv = Z_to_bv 64 8 /\ getr R 20%bv = Z_to_bv 64 so.
Definition same_s05 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\ getr R' 21%bv = getr R0 21%bv.
Definition same_s04 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv.
Definition sb_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)).
Definition ext_frame (M : mem) (spe rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (spe - 8) rav /\ L5.u64_at RSEGS M (spe - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (spe - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (spe - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (spe - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (spe - 48) (bv_unsigned (getr R0 20%bv)).
Lemma sb_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 64 <= i < sp1 -> K i) -> sb_frame M sp1 rav R0 -> sb_frame M' sp1 rav R0.
Proof. intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7). repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.
Lemma ext_frame_x : forall (K : Z -> Prop) (M M' : mem) spe rav R0, TK.samem K M M' -> 2 ^ 40 <= spe <= 2 ^ 47 -> (forall i, spe - 48 <= i < spe -> K i) -> ext_frame M spe rav R0 -> ext_frame M' spe rav R0.
Proof. intros K M M' spe rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6). repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.

Definition sb_ptrs (M : mem) (SB d e : Z) : Prop :=
  L5.u64_at RSEGS M (SB + 16) d /\ L5.u64_at RSEGS M (SB + 24) d /\ L5.u64_at RSEGS M (SB + 32) e /\ L5.u64_at RSEGS M (SB + 88) e.
Definition sb_zero3 (M : mem) (SB : Z) : Prop := L5.u64_at RSEGS M (SB + 40) 0 /\ L5.u64_at RSEGS M (SB + 48) 0 /\ L5.u64_at RSEGS M (SB + 56) 0.

Lemma u64_zero : forall (M : mem) A, (forall i, 0 <= i < 8 -> M (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0)) -> L5.u64_at RSEGS M A 0.
Proof.
  intros M A H. unfold L5.u64_at. cbn [rdn]. rewrite !L5C.add1_lit.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  replace (A + 1 + 1) with (A + 2) by lia. replace (A + 2 + 1) with (A + 3) by lia. replace (A + 3 + 1) with (A + 4) by lia. replace (A + 4 + 1) with (A + 5) by lia.
  replace (A + 5 + 1) with (A + 6) by lia. replace (A + 6 + 1) with (A + 7) by lia.
  rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.

Definition bit0 (w0 : Z) : Z := Z.land (w0 mod 256) 1.

Lemma copy_cap_big : forall n, 44 < n -> PML.copy_cap n = 8 * (n / 8) + 8.
Proof. intros n Hn. unfold PML.copy_cap. rewrite Z.max_l by lia. rewrite CL5.lor7 by lia. lia. Qed.
Lemma copy_cap_small : forall n, n <= 44 -> PML.copy_cap n = 48.
Proof. intros n Hn. unfold PML.copy_cap. rewrite Z.max_r by lia. reflexivity. Qed.

Ltac tk_linx HLF r tac :=
  lazymatch type of HLF with
  | CC.leaf_facts _ _ ?ps _ _ _ _ =>
      let o := eval vm_compute in (TK.ps_reg ps (ridx r)) in
      lazymatch o with Some ?e => apply (TK.leaf_lin _ _ _ _ _ _ r e _ HLF ltac:(vm_compute; reflexivity)); [lin_form; tac | lia] end
  end.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition KE1 (sp1 SB : Z) (a : Z) : Prop := ~ (sp1 - 64 <= a < sp1) /\ ~ (SB <= a < SB + 8).
Definition KE2 (sp1 SB : Z) (a : Z) : Prop := ~ (sp1 - 112 <= a < sp1 - 64) /\ ~ (SB <= a < SB + 8) /\ ~ (SB + 16 <= a < SB + 104).

Lemma s_sb_entry : forall (fx : FPState) R M model K sp1 SB so rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 SB -> getr R 11%bv = Z_to_bv 64 so -> getr R 12%bv = Z_to_bv 64 8 ->
  2 ^ 40 <= SB <= 2 ^ 47 - 104 -> 0 <= so < 2 ^ 64 -> PML.img_ro M -> L5.defined M (sp1 - 64) 64 -> L5.defined M SB 104 -> sp1 <= SB ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 SBT.R_LOC -> getr R' 10%bv = Z_to_bv 64 (SB + 8) ->
      sb_live R' SB so -> sb_frame M' sp1 rav R -> TK.keepsR KO6 R R' -> TK.samem (KE1 sp1 SB) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_SBUF_CTOR M model) K.
Proof.
  intros fx R M model K sp1 SB so rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 HSB Hso RO DF DS J1 Kloc.
  change PML.PC_SBUF_CTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) [(12%nat, 8)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (10%bv : reg) H10.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE1 sp1 SB) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kloc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.R_LOC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | | ck_keeps HLF Hag64 KO6 | exact FRM | exact MG].
    + unfold sb_live. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg)].
    + unfold sb_frame. repeat split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg) | ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg)
        | ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg) | ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg) | ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg)].
Qed.

Lemma u_half_byte : forall E v w0, bv_unsigned (ev E v) = w0 -> 0 <= w0 < 2 ^ 64 -> bv_unsigned (edenot E (EAlu ALU_SRL (EExt false 0 1 (EVar v)) (ELit 1))) = (w0 mod 256) / 2.
Proof.
  intros E v w0 U Hw. rewrite u_srl_lit. cbn [edenot]. rewrite (RK.w_of_u _ _ U), RK.ext_u8_mod by lia. pose proof (Z.mod_pos_bound w0 256 ltac:(lia)). rewrite u64_of_Z by lia. reflexivity.
Qed.
Lemma w_bit0 : forall E v w0, bv_unsigned (ev E v) = w0 -> 0 <= w0 < 2 ^ 64 -> alu64 ALU_AND (ext_val false 0 1 (ev E v)) (Z_to_bv 64 1) = Z_to_bv 64 (bit0 w0).
Proof. intros E v w0 U Hw. rewrite (RK.w_of_u _ _ U), RK.ext_u8_mod by lia. pose proof (Z.mod_pos_bound w0 256 ltac:(lia)). rewrite RK.and_lit by lia. reflexivity. Qed.
Lemma sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. change (alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b)) with (if bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) then Z_to_bv 64 1 else Z_to_bv 64 0 : word).
  unfold bv_ltu. rewrite !u64_of_Z by lia. destruct (Z.ltb_spec a b); reflexivity.
Qed.
Lemma sltu_lit0 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b Ha Hb Hab. rewrite sltu_lit by lia. destruct (Z.ltb_spec a b); [exfalso; lia | reflexivity]. Qed.
Lemma sltu_lit1 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a < b -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof. intros a b Ha Hb Hab. rewrite sltu_lit by lia. destruct (Z.ltb_spec a b); [reflexivity | exfalso; lia]. Qed.

Lemma s_sb_r_loc : forall (fx : FPState) R M model K sp1 SB so rav R0 w0 w1 w2,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> CK.spok sp1 -> sb_live R SB so ->
  2 ^ 40 <= SB <= 2 ^ 47 - 104 -> 2 ^ 40 <= so <= 2 ^ 47 - 24 -> sp1 <= SB -> sp1 <= so -> (SB + 104 <= so \/ so + 24 <= SB) ->
  sb_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 112) 48 -> PML.img_ro M -> L5.defined M SB 104 ->
  0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 -> L5.u64_at RSEGS M so w0 -> L5.u64_at RSEGS M (so + 8) w1 -> L5.u64_at RSEGS M (so + 16) w2 ->
  (bit0 w0 = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> TK.keepsR KO6 R R' ->
      L5.u64_at RSEGS M' SB PML.VT_STRINGBUF -> sb_ptrs M' SB (SB + 65) (SB + 65 + (w0 mod 256) / 2) -> sb_zero3 M' SB ->
      L5.u64_at RSEGS M' (SB + 64) w0 -> L5.u64_at RSEGS M' (SB + 72) w1 -> L5.u64_at RSEGS M' (SB + 80) w2 -> L5.u32_at RSEGS M' (SB + 96) 8 ->
      TK.samem (KE2 sp1 SB) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (bit0 w0 <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 SBT.R_ASSIGN -> getr R' 10%bv = Z_to_bv 64 (SB + 64) ->
      getr R' 11%bv = Z_to_bv 64 w2 -> getr R' 12%bv = Z_to_bv 64 w1 -> getr R' 8%bv = Z_to_bv 64 SB -> TK.keepsR KO6 R R' ->
      L5.u64_at RSEGS M' SB PML.VT_STRINGBUF -> (forall j, 0 <= j < 10 -> L5.u64_at RSEGS M' (SB + 16 + 8 * j) 0) -> L5.u32_at RSEGS M' (SB + 96) 8 ->
      TK.samem (KE2 sp1 SB) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' SBT.EXT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.R_LOC M model) K.
Proof.
  intros fx R M model K sp1 SB so rav R0 w0 w1 w2 Hh Hl Hfp H2 [Hsp Hal] (H8 & H19 & H20) HSB Hso J1 J2 APT (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hra DF RO DS Hw0 Hw1 Hw2 C0 C1 C2 Ksso Klong.
  change SBT.R_LOC with (CC.cp_pc G.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv); w0; w1; w2]).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-64) gl (fun _ : nat => @nil byte) [(19%nat, 8)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (20%bv : reg) H20.
    ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 7%nat w0. ck_gh E 8%nat w1. ck_gh E 9%nat w2.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4. + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + e_unk. + e_wr. + e_range. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr.
    + ck_kw64 so w0 C0. + ck_kw64 (so + 8) w1 C1. + ck_kw64 (so + 16) w2 C2.
    + e_disj. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (20%bv : reg) H20. ck_gh E 7%nat w0. ck_gh E 8%nat w1. ck_gh E 9%nat w2.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp1) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE2 sp1 SB) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    pose proof (u_half_byte E' 71%nat w0 ltac:(assumption) Hw0) as UH.
    pose proof (Z.mod_pos_bound w0 256 ltac:(lia)) as Hb0.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]); ck_probes HLF PF.
    +
      exfalso. destruct PF as (PF & _). ck_w2z PF. rewrite TK.add_lit in PF by lia. apply RK.w_inj in PF; lia.
    +
      destruct PF as (PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF. apply RK.w_inj in PF; [|unfold bit0; apply RK.land_range; lia | lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sb Hh Hl R1 Hra).
      apply (Ksso PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO6 | | | | | | | | exact FRM | exact MG].
      * unfold same_s05. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * unfold PML.VT_STRINGBUF. ck_cell64 HLF (EVar 40) 0 (ELit 791824). reflexivity.
      * unfold sb_ptrs. repeat split.
        -- ck_cell64 HLF (EVar 40) 16 (EAlu ALU_ADD (EVar 40) (ELit 65)). ck_vlin.
        -- ck_cell64 HLF (EVar 40) 24 (EAlu ALU_ADD (EVar 40) (ELit 65)). ck_vlin.
        -- ck_cell64 HLF (EVar 40) 32 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 40) (EAlu ALU_SRL (EExt false 0 1 (EVar 71)) (ELit 1))) (ELit 65)).
           apply CL5.u_lin; [lin_form; rewrite UH; cbn [edenot]; rw_atoms; lia | pose proof (Z.div_pos (w0 mod 256) 2 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (w0 mod 256) 2 256 ltac:(lia) ltac:(lia)); lia].
        -- ck_cell64 HLF (EVar 40) 88 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 40) (EAlu ALU_SRL (EExt false 0 1 (EVar 71)) (ELit 1))) (ELit 65)).
           apply CL5.u_lin; [lin_form; rewrite UH; cbn [edenot]; rw_atoms; lia | pose proof (Z.div_pos (w0 mod 256) 2 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (w0 mod 256) 2 256 ltac:(lia) ltac:(lia)); lia].
      * pose proof (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 40) 40) (ELit 24)) HLF ltac:(vm_compute; reflexivity)) as KZ. cbn [kentry_ok] in KZ. destruct KZ as (_ & KZ).
        assert (ES : estart E' (SA (EVar 40) 40) = SB + 40) by ev_start. rewrite ES in KZ. change (elenZ E' (ELit 24)) with 24 in KZ.
        unfold sb_zero3. repeat split; apply u64_zero; intros i Hi.
        -- apply KZ. lia.
        -- replace (SB + 48 + i) with (SB + 40 + (8 + i)) by lia. apply KZ. lia.
        -- replace (SB + 56 + i) with (SB + 40 + (16 + i)) by lia. apply KZ. lia.
      * ck_cell64 HLF (EVar 40) 64 (EVar 71). ck_atom.
      * ck_cell64 HLF (EVar 40) 72 (EVar 72). ck_atom.
      * ck_cell64 HLF (EVar 40) 80 (EVar 73). ck_atom.
      * ck_cell32 HLF (EVar 40) 96 (ELit 8). reflexivity.
    +
      destruct PF as (PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF. apply RK.w_neq in PF.
      apply (Klong PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.R_ASSIGN; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | tk_lin HLF (8%bv : reg)
        | ck_keeps HLF Hag64 KO6 | | | | exact FRM | exact MG].
      * unfold PML.VT_STRINGBUF. ck_cell64 HLF (EVar 40) 0 (ELit 791824). reflexivity.
      * pose proof (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 40) 16) (ELit 48)) HLF ltac:(vm_compute; reflexivity)) as KZ. cbn [kentry_ok] in KZ. destruct KZ as (_ & KZ).
        assert (ES : estart E' (SA (EVar 40) 16) = SB + 16) by ev_start. rewrite ES in KZ. change (elenZ E' (ELit 48)) with 48 in KZ.
        intros j Hj. destruct (Z_lt_le_dec j 6) as [J6|J6].
        -- apply u64_zero. intros i Hi. replace (SB + 16 + 8 * j + i) with (SB + 16 + (8 * j + i)) by lia. apply KZ. lia.
        -- assert (JJ : j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia. destruct JJ as [-> | [-> | [-> | ->]]].
           ++ replace (SB + 16 + 8 * 6) with (SB + 64) by lia. ck_cell64 HLF (EVar 40) 64 (ELit 0). reflexivity.
           ++ replace (SB + 16 + 8 * 7) with (SB + 72) by lia. ck_cell64 HLF (EVar 40) 72 (ELit 0). reflexivity.
           ++ replace (SB + 16 + 8 * 8) with (SB + 80) by lia. ck_cell64 HLF (EVar 40) 80 (ELit 0). reflexivity.
           ++ replace (SB + 16 + 8 * 9) with (SB + 88) by lia. ck_cell64 HLF (EVar 40) 88 (ELit 0). reflexivity.
      * ck_cell32 HLF (EVar 40) 96 (ELit 8). reflexivity.
Qed.

Definition KE3 (spe this : Z) (a : Z) : Prop := ~ (spe - 48 <= a < spe) /\ ~ (this <= a < this + 2).

Lemma s_ext_entry : forall (fx : FPState) R M model K spe this data n rae,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 spe -> CK.spok spe -> getr R 1%bv = Z_to_bv 64 rae -> L5.ra_ok rae -> getr R 10%bv = Z_to_bv 64 this -> getr R 11%bv = Z_to_bv 64 data -> getr R 12%bv = Z_to_bv 64 n ->
  2 ^ 40 <= this <= 2 ^ 47 - 24 -> 0 <= data < 2 ^ 64 -> 0 <= n <= 2 ^ 26 -> L5.defined M (spe - 48) 48 -> L5.defined M this 2 -> spe <= this ->
  (23 <= n -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (spe - 48) -> getr R' 1%bv = Z_to_bv 64 SBT.EXT_R_NEW -> getr R' 10%bv = Z_to_bv 64 (PML.copy_cap n) ->
      getr R' 8%bv = Z_to_bv 64 n -> getr R' 9%bv = Z_to_bv 64 this -> getr R' 19%bv = Z_to_bv 64 data -> getr R' 20%bv = Z_to_bv 64 (PML.copy_cap n - 1) ->
      ext_frame M' spe rae R -> TK.keepsR KO5 R R' -> TK.samem (KE3 spe this) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPNEW M' model) K) ->
  (n = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 spe -> getr R' 10%bv = Z_to_bv 64 this -> TK.keepsR CK.CSR R R' ->
      L5.u8_at RSEGS M' this 0 -> L5.u8_at RSEGS M' (this + 1) 0 -> TK.samem (KE3 spe this) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rae M' model) K) ->
  (1 <= n <= 22 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (spe - 48) -> getr R' 1%bv = Z_to_bv 64 SBT.EXT_R_MOVE -> getr R' 10%bv = Z_to_bv 64 (this + 1) ->
      getr R' 11%bv = Z_to_bv 64 data -> getr R' 12%bv = Z_to_bv 64 n -> getr R' 8%bv = Z_to_bv 64 n -> getr R' 9%bv = Z_to_bv 64 this -> getr R' 18%bv = Z_to_bv 64 (this + 1) ->
      ext_frame M' spe rae R -> TK.keepsR KO5 R R' -> L5.u8_at RSEGS M' this (2 * n) -> TK.samem (KE3 spe this) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' SBT.MEMMOVE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.EXT M model) K.
Proof.
  intros fx R M model K spe this data n rae Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 Hthis Hdata Hn DF DT J1 Knew Kzero Kmove.
  change SBT.EXT with (CC.cp_pc G.cp2).
  assert (Hrae : 0 <= rae < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) spe R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (12%bv : reg) H12.
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (12%bv : reg) H12. ck_reg E (1%bv : reg) H1.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE3 spe this) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (EFR : forall ps0, CC.leaf_facts RSEGS G.cp2 ps0 E' R' M M' ->
              existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-8)) 8 (EVar 33))) (SR.ps_cells ps0) = true -> existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-16)) 8 (EVar 40))) (SR.ps_cells ps0) = true ->
              existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-24)) 8 (EVar 41))) (SR.ps_cells ps0) = true -> existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-32)) 8 (EVar 50))) (SR.ps_cells ps0) = true ->
              existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-40)) 8 (EVar 51))) (SR.ps_cells ps0) = true -> existsb (APC.kentry_eqb (KWord (SA (EVar 2) (-48)) 8 (EVar 52))) (SR.ps_cells ps0) = true ->
              ext_frame M' spe rae R).
    { intros ps0 HLF0 B1 B2 B3 B4 B5 B6. unfold ext_frame. repeat split.
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B1) | ev_start | ck_atom].
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B2) | ev_start | ck_vgh Hag64 40%nat; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ (8%bv : reg))]].
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B3) | ev_start | ck_vgh Hag64 41%nat; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ (9%bv : reg))]].
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B4) | ev_start | ck_vgh Hag64 50%nat; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ (18%bv : reg))]].
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B5) | ev_start | ck_vgh Hag64 51%nat; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ (19%bv : reg))]].
      - eapply (CL5.kword64_elim CK.RSEGS); [exact (CK.lf_cell _ _ _ _ _ _ _ HLF0 B6) | ev_start | ck_vgh Hag64 52%nat; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ (20%bv : reg))]]. }
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]]); ck_paths HLF PF; destruct PF as (P1 & _); ck_rlin P1.
    +
      assert (N44 : 44 < n) by lia. pose proof (copy_cap_big n N44) as CC. pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound n 8 (2 ^ 26) ltac:(lia) ltac:(lia)) as D1.
      apply (Knew ltac:(lia) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.EXT_R_NEW; tk_lin HLF (1%bv : reg) | | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (19%bv : reg) |
        | apply (EFR _ HLF); vm_compute; reflexivity | ck_keeps HLF Hag64 KO5 | exact FRM | exact MG].
      * rewrite CC. tk_linx HLF (10%bv : reg) ltac:(rewrite u_srl_lit; cbn [edenot]; rw_atoms; change (2 ^ ((3 mod two64) mod 64)) with 8; lia).
      * rewrite CC. tk_linx HLF (20%bv : reg) ltac:(rewrite u_srl_lit; cbn [edenot]; rw_atoms; change (2 ^ ((3 mod two64) mod 64)) with 8; lia).
    +
      assert (N44 : n <= 44) by lia. pose proof (copy_cap_small n N44) as CC.
      apply (Knew ltac:(lia) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.EXT_R_NEW; tk_lin HLF (1%bv : reg) | rewrite CC; tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg)
        | tk_lin HLF (19%bv : reg) | rewrite CC; tk_lin HLF (20%bv : reg) | apply (EFR _ HLF); vm_compute; reflexivity | ck_keeps HLF Hag64 KO5 | exact FRM | exact MG].
    +
      assert (N0 : n = 0) by lia.
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rae) by (tk_lin HLF (1%bv : reg)).
      apply (CK.ret_leaf fx' R' _ M' model K rae ret_ext Hh Hl R1 Hra).
      apply (Kzero N0 fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | | exact FRM | exact MG].
      * ck_cell8 HLF (EVar 42) 0 (EMd M_MUL (ELit 2) (EVar 44)). ck_vlin.
      * eapply RK.kword8_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EAlu ALU_ADD (EVar 42) (EVar 44)) 1) 1 (ELit 0)) HLF); vm_compute; reflexivity | | reflexivity].
        apply CL5.estart_lin with (v := this); [lin_eval; rw_atoms; lia | lia].
    +
      apply (Kmove ltac:(lia) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.EXT_R_MOVE; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg)
        | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | apply (EFR _ HLF); vm_compute; reflexivity | ck_keeps HLF Hag64 KO5 | | exact FRM | exact MG].
      ck_cell8 HLF (EVar 42) 0 (EMd M_MUL (ELit 2) (EVar 44)). ck_vlin.
Qed.

Ltac nul_start v0 := apply CL5.estart_lin with (v := v0); [lin_eval; rw_atoms; lia | lia].
Ltac e_unk_nul v0 := eapply CL5.kunk_intro; [nul_start v0 | ev_len | lia | lia | lia | rewrite Z.add_0_r; assumption].
Ltac e_wr_nul v0 := eapply CL5.kwr_intro; [nul_start v0 | ev_len | lia | lia | lia | rewrite Z.add_0_r; assumption].

Lemma s_ext_r_move : forall (fx : FPState) R M model K spe this dst n rae R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (spe - 48) -> CK.spok spe ->
  getr R 8%bv = Z_to_bv 64 n -> getr R 9%bv = Z_to_bv 64 this -> getr R 18%bv = Z_to_bv 64 dst -> 0 <= this < 2 ^ 64 -> 2 ^ 40 <= dst <= 2 ^ 47 -> 1 <= n <= 22 ->
  ext_frame M spe rae R0 -> L5.ra_ok rae -> L5.defined M (n + dst) 1 -> spe <= dst ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 spe -> getr R' 10%bv = Z_to_bv 64 this -> same_s04 R0 R' -> TK.keepsR KO5 R R' ->
      L5.u8_at RSEGS M' (dst + n) 0 -> TK.samem (fun a => ~ (dst + n <= a < dst + n + 1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rae M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.EXT_R_MOVE M model) K.
Proof.
  intros fx R M model K spe this dst n rae R0 Hh Hl Hfp H2 [Hsp Hal] H8 H9 H18 Hthis Hdst Hn (F1 & F2 & F3 & F4 & F5 & F6) Hra DN J1 Kret.
  change SBT.EXT_R_MOVE with (CC.cp_pc G.cp3).
  assert (Hrae : 0 <= rae < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20.
  set (gl := [rae; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv)]).
  ck_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) spe R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (18%bv : reg) H18.
    ck_gh E 0%nat rae. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)).
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (spe - 8) rae F1. + ck_kw64 (spe - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (spe - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (spe - 32) (bv_unsigned (getr R0 18%bv)) F4. + ck_kw64 (spe - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (spe - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + e_range. + e_range. + e_unk_nul (n + dst). + e_wr_nul (n + dst).
    + eapply CL5.kdisj_intro; [ev_start | ev_len | nul_start (n + dst) | ev_len | lia].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 6)%nat) by (change 6%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp3) with 70%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (dst + n <= a < dst + n + 1)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1.
      assert (ES : estart E' (SA (EAlu ALU_ADD (EVar 40) (EVar 50)) 0) = n + dst + 0) by (nul_start (n + dst)).
      set (F := CC.cp_F G.cp3); vm_compute in F; subst F. apply Forall_cons; [|apply Forall_nil]. cbv beta iota zeta. rewrite ES. change (elenZ E' (ELit 1)) with 1. rewrite ?u64_of_Z by lia. lia. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rae) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rae ret_ext Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO5 | | exact FRM | exact MG].
    + unfold same_s04. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + eapply RK.kword8_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EAlu ALU_ADD (EVar 40) (EVar 50)) 0) 1 (ELit 0)) HLF); vm_compute; reflexivity | | reflexivity].
      replace (dst + n) with (n + dst + 0) by lia. nul_start (n + dst).
Qed.

Definition KN : list nat := [3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma s_ext_r_new : forall (fx : FPState) R M model K spe p data n,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (spe - 48) -> CK.spok spe ->
  getr R 8%bv = Z_to_bv 64 n -> getr R 10%bv = Z_to_bv 64 p -> getr R 19%bv = Z_to_bv 64 data -> 0 <= p < 2 ^ 64 -> 0 <= data < 2 ^ 64 -> 23 <= n <= 2 ^ 26 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (spe - 48) -> getr R' 1%bv = Z_to_bv 64 SBT.EXT_R_CPY -> getr R' 10%bv = Z_to_bv 64 p -> getr R' 11%bv = Z_to_bv 64 data ->
      getr R' 12%bv = Z_to_bv 64 n -> getr R' 18%bv = Z_to_bv 64 p -> TK.keepsR KN R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' SBT.MEMCPY M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.EXT_R_NEW M model) K.
Proof.
  intros fx R M model K spe p data n Hh Hl Hfp H2 [Hsp Hal] H8 H10 H19 Hp Hdata Hn Kcpy.
  change SBT.EXT_R_NEW with (CC.cp_pc G.cp4).
  ck_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (-48) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) spe R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8.
    unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (10%bv : reg) H10. ck_reg E (19%bv : reg) H19.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kcpy fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SBT.EXT_R_CPY; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | tk_lin HLF (18%bv : reg)
      | ck_keeps HLF Hag64 KN].
Qed.

Lemma s_ext_r_cpy : forall (fx : FPState) R M model K spe this p n c7 rae R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (spe - 48) -> CK.spok spe ->
  getr R 8%bv = Z_to_bv 64 n -> getr R 9%bv = Z_to_bv 64 this -> getr R 18%bv = Z_to_bv 64 p -> getr R 20%bv = Z_to_bv 64 c7 ->
  2 ^ 40 <= this <= 2 ^ 47 - 24 -> 4096 <= p <= 2 ^ 47 -> 23 <= n <= 2 ^ 26 -> 0 <= c7 < 2 ^ 63 ->
  ext_frame M spe rae R0 -> L5.ra_ok rae -> L5.defined M this 24 -> L5.defined M (n + p) 1 -> spe <= this -> n + p + 1 <= spe - 48 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 spe -> getr R' 10%bv = Z_to_bv 64 this -> same_s04 R0 R' -> TK.keepsR KO5 R R' ->
      L5.u64_at RSEGS M' this (c7 + 2) -> L5.u64_at RSEGS M' (this + 8) n -> L5.u64_at RSEGS M' (this + 16) p -> L5.u8_at RSEGS M' (p + n) 0 ->
      TK.samem (fun a => ~ (this <= a < this + 24) /\ ~ (p + n <= a < p + n + 1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rae M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.EXT_R_CPY M model) K.
Proof.
  intros fx R M model K spe this p n c7 rae R0 Hh Hl Hfp H2 [Hsp Hal] H8 H9 H18 H20 Hthis Hp Hn Hc7 (F1 & F2 & F3 & F4 & F5 & F6) Hra DT DN J1 J2 Kret.
  change SBT.EXT_R_CPY with (CC.cp_pc G.cp5).
  assert (Hrae : 0 <= rae < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20.
  set (gl := [rae; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv)]).
  ck_open FPM G.cp5 (G.plans 5%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) spe R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18.
    ck_gh E 0%nat rae. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)).
    unfold know_ok, G.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (spe - 8) rae F1. + ck_kw64 (spe - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (spe - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (spe - 32) (bv_unsigned (getr R0 18%bv)) F4. + ck_kw64 (spe - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (spe - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + e_range. + e_range. + e_range. + e_unk. + e_wr. + e_unk_nul (n + p). + e_wr_nul (n + p).
    + e_disj.
    + eapply CL5.kdisj_intro; [ev_start | ev_len | nul_start (n + p) | ev_len | lia].
    + eapply CL5.kdisj_intro; [ev_start | ev_len | nul_start (n + p) | ev_len | lia].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18. ck_reg E (20%bv : reg) H20.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 6)%nat) by (change 6%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp5) with 70%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (this <= a < this + 24) /\ ~ (p + n <= a < p + n + 1)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2).
      assert (ES : estart E' (SA (EAlu ALU_ADD (EVar 40) (EVar 50)) 0) = n + p + 0) by (nul_start (n + p)).
      set (F := CC.cp_F G.cp5); vm_compute in F; subst F. apply Forall_cons; [unfold estart, elenZ; cbn [a_base a_off edenot]; rw_atoms; rewrite ?u64_of_Z by lia; lia|].
      apply Forall_cons; [|apply Forall_nil]. cbv beta iota zeta. rewrite ES. change (elenZ E' (ELit 1)) with 1. rewrite ?u64_of_Z by lia. lia. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rae) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rae ret_ext Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO5 | | | | | exact FRM | exact MG].
    + unfold same_s04. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + ck_cell64 HLF (EVar 41) 0 (EAlu ALU_ADD (EVar 52) (ELit 2)). ck_vlin.
    + ck_cell64 HLF (EVar 41) 8 (EVar 40). ck_atom.
    + ck_cell64 HLF (EVar 41) 16 (EVar 50). ck_atom.
    + eapply RK.kword8_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EAlu ALU_ADD (EVar 40) (EVar 50)) 0) 1 (ELit 0)) HLF); vm_compute; reflexivity | | reflexivity].
      replace (p + n) with (n + p + 0) by lia. nul_start (n + p).
Qed.

Definition KE4 (sp1 SB : Z) (a : Z) : Prop := ~ (sp1 - 112 <= a < sp1 - 64) /\ ~ (SB + 16 <= a < SB + 40) /\ ~ (SB + 88 <= a < SB + 96).

Lemma s_sb_r_assign : forall (fx : FPState) R M model K sp1 SB rav R0 w0 w1 w2,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 SB ->
  2 ^ 40 <= SB <= 2 ^ 47 - 104 -> sp1 <= SB -> sb_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 112) 48 -> L5.defined M SB 104 ->
  0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 -> L5.u64_at RSEGS M (SB + 64) w0 -> L5.u64_at RSEGS M (SB + 72) w1 -> L5.u64_at RSEGS M (SB + 80) w2 -> L5.u32_at RSEGS M (SB + 96) 8 ->
  (bit0 w0 <> 0 -> w1 <= 2 ^ 26 /\ 0 < w2 <= 2 ^ 47) ->
  (forall (fx' : FPState) R' M' d e, PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> TK.keepsR KO6 R R' ->
      ((bit0 w0 = 0 /\ d = SB + 65 /\ e = SB + 65 + (w0 mod 256) / 2) \/ (bit0 w0 <> 0 /\ d = w2 /\ e = w2 + w1)) -> sb_ptrs M' SB d e ->
      TK.samem (KE4 sp1 SB) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SBT.R_ASSIGN M model) K.
Proof.
  intros fx R M model K sp1 SB rav R0 w0 w1 w2 Hh Hl Hfp H2 [Hsp Hal] H8 HSB J1 (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hra DF DS Hw0 Hw1 Hw2 C0 C1 C2 C96 LONG Kret.
  change SBT.R_ASSIGN with (CC.cp_pc GB.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv); w0; w1; w2]).
  ck_open FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-64) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8.
    ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 7%nat w0. ck_gh E 8%nat w1. ck_gh E 9%nat w2.
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4. + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + e_unk. + e_wr. + e_range.
    + ck_kw64 (SB + 64) w0 C0. + ck_kw64 (SB + 72) w1 C1. + ck_kw64 (SB + 80) w2 C2. + ck_kw32 (SB + 96) 8 C96.
    + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_gh E 7%nat w0. ck_gh E 8%nat w1. ck_gh E 9%nat w2.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GB.cp0) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE4 sp1 SB) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    pose proof (u_half_byte E' 71%nat w0 ltac:(assumption) Hw0) as UH.
    pose proof (Z.mod_pos_bound w0 256 ltac:(lia)) as Hb0.
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav -> forall d e, ((bit0 w0 = 0 /\ d = SB + 65 /\ e = SB + 65 + (w0 mod 256) / 2) \/ (bit0 w0 <> 0 /\ d = w2 /\ e = w2 + w1)) -> sb_ptrs M' SB d e ->
                 getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> TK.keepsR KO6 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' (CC.cp_pc (CC.CP SBT.RET [] [] 0 [] [] (ELit 0))) M' model) K).
    { intros R1 d e CASE PTR H2' SS KO. apply (CK.ret_leaf fx' R' _ M' model K rav ret_sb Hh Hl R1 Hra). exact (Kret fx' R' M' d e Hfp' H2' SS KO CASE PTR FRM MG). }
    cbn [CC.cp_pc] in R1.
    assert (SS : forall ps0, CC.leaf_facts RSEGS GB.cp0 ps0 E' R' M M' -> TK.ps_reg ps0 8 = Some (EVar 65) -> TK.ps_reg ps0 9 = Some (EVar 66) -> TK.ps_reg ps0 18 = Some (EVar 67) ->
                TK.ps_reg ps0 19 = Some (EVar 68) -> TK.ps_reg ps0 20 = Some (EVar 69) -> TK.ps_reg ps0 21 = Some (EVar 70) -> same_s05 R0 R').
    { intros ps0 HLF0 Q8 Q9 Q18 Q19 Q20 Q21. unfold same_s05. repeat split.
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (8%bv : reg) _ HLF0 Q8). cbn [edenot]. etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (9%bv : reg) _ HLF0 Q9). cbn [edenot]. etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (18%bv : reg) _ HLF0 Q18). cbn [edenot]. etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (19%bv : reg) _ HLF0 Q19). cbn [edenot]. etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (20%bv : reg) _ HLF0 Q20). cbn [edenot]. etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      - rewrite (TK.ps_reg_r _ _ _ _ _ _ (21%bv : reg) _ HLF0 Q21). cbn [edenot]. etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]. }
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]]); ck_probes HLF PF.
    +
      destruct PF as (PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF.
      apply RK.w_inj in PF; [|unfold bit0; apply RK.land_range; lia | lia].
      apply (R1 ltac:(tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)) (SB + 65) (SB + 65 + (w0 mod 256) / 2) ltac:(left; split; [exact PF | split; reflexivity]));
        [ | tk_lin HLF (2%bv : reg) | apply (SS _ HLF); vm_compute; reflexivity | ck_keeps HLF Hag64 KO6].
      unfold sb_ptrs. repeat split.
      * ck_cell64 HLF (EVar 40) 16 (EAlu ALU_ADD (EVar 40) (ELit 65)). ck_vlin.
      * ck_cell64 HLF (EVar 40) 24 (EAlu ALU_ADD (EVar 40) (ELit 65)). ck_vlin.
      * ck_cell64 HLF (EVar 40) 32 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 40) (EAlu ALU_SRL (EExt false 0 1 (EVar 71)) (ELit 1))) (ELit 65)).
        apply CL5.u_lin; [lin_form; rewrite UH; cbn [edenot]; rw_atoms; lia | pose proof (Z.div_pos (w0 mod 256) 2 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (w0 mod 256) 2 256 ltac:(lia) ltac:(lia)); lia].
      * ck_cell64 HLF (EVar 40) 88 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 40) (EAlu ALU_SRL (EExt false 0 1 (EVar 71)) (ELit 1))) (ELit 65)).
        apply CL5.u_lin; [lin_form; rewrite UH; cbn [edenot]; rw_atoms; lia | pose proof (Z.div_pos (w0 mod 256) 2 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (w0 mod 256) 2 256 ltac:(lia) ltac:(lia)); lia].
    +
      destruct PF as (PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF.
      apply RK.w_neq in PF. destruct (LONG PF) as [B1 [B2 B3]]. exfalso.
      pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EAlu ALU_SLTU (EAlu ALU_ADD (EVar 72) (EVar 73)) (EVar 73)) 1 1) HLF ltac:(vm_compute; reflexivity)) as KW.
      cbn [kentry_ok edenot] in KW. ck_w2z KW. rewrite TK.add_lit in KW by lia. rewrite (sltu_lit0 (w1 + w2) w2) in KW by lia.
      rewrite u64_of_Z in KW by lia. lia.
    +
      destruct PF as (PX & PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF.
      apply RK.w_neq in PF. destruct (LONG PF) as [B1 [B2 B3]]. exfalso.
      ck_w2z PX. rewrite TK.add_lit in PX by lia. rewrite (sltu_lit1 0 w2) in PX by lia. rewrite (sltu_lit0 (w1 + w2) 1) in PX by lia.
      apply (f_equal bv_unsigned) in PX. vm_compute in PX. discriminate PX.
    +
      destruct PF as (_ & PF & _). rewrite (w_bit0 E' 71%nat w0 ltac:(assumption) Hw0) in PF.
      apply RK.w_neq in PF. destruct (LONG PF) as [L1 [_ L2]].
      apply (R1 ltac:(tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)) w2 (w2 + w1) ltac:(right; split; [exact PF | split; reflexivity]));
        [ | tk_lin HLF (2%bv : reg) | apply (SS _ HLF); vm_compute; reflexivity | ck_keeps HLF Hag64 KO6].
      unfold sb_ptrs. repeat split.
      * ck_cell64 HLF (EVar 40) 16 (EVar 73). ck_atom.
      * ck_cell64 HLF (EVar 40) 24 (EVar 73). ck_atom.
      * ck_cell64 HLF (EVar 40) 32 (EAlu ALU_ADD (EVar 72) (EVar 73)). ck_vlin.
      * ck_cell64 HLF (EVar 40) 88 (EAlu ALU_ADD (EVar 72) (EVar 73)). ck_vlin.
Qed.
End S.
End SBS.
