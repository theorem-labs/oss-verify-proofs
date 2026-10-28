(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs I_ikit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition g_tls_index : Z := 0x16b030.
Definition g_dtv_ptr : Z := 0x6a7e60.
Definition g_dtv : Z := 0x6a7e88.
Definition g_dtv1 : Z := 0x6a7e90.
Definition dtv1_val : Z := 0x6a8668.
Definition g_real_tls_get_addr : Z := 0x16c140.
Definition tls_get_addr_entry : Z := 0x6c498.
Definition musl_tls_get_addr_entry : Z := 0x15d5cc.
Definition dtls_entry : Z := 0x9a678.

Definition tga_musl_cells (m : mem) : Prop :=
  rw_cells asegs m g_tls_index [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0xfffffffffffff800)]
  /\ rw_cells asegs m g_dtv_ptr [C8 (Z_to_bv 64 g_dtv)]
  /\ rw_cells asegs m g_dtv1 [C8 (Z_to_bv 64 dtv1_val)].

Lemma musl_tls_get_addr_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  tga_musl_cells m -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc tpA m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 g_tls_index) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 musl_tls_get_addr_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros (TI & DP & D1) MI. unfold g_tls_index, g_dtv_ptr, g_dtv, g_dtv1, dtv1_val, musl_tls_get_addr_entry, tpA in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 9 zstep.
  finish.
Qed.

Definition g_got_common_flags : Z := 0x16a220.
Definition g_common_flags : Z := 0x205768.
Definition g_intercept_tls_get_addr : Z := 0x2057f1.
Definition g_got_verbosity : Z := 0x16a280.
Definition g_current_verbosity : Z := 0x2036d8.
Definition g_got_dtls_off : Z := 0x16b040.
Definition g_tls_dtls : Z := 0x6a7e70.

Definition dtls_cells (DTV dtvbeg : Z) (m : mem) : Prop :=
  rw_cells asegs m g_got_common_flags [C8 (Z_to_bv 64 g_common_flags)]
  /\ rw_cells asegs m g_intercept_tls_get_addr [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_got_verbosity [C8 (Z_to_bv 64 g_current_verbosity)]
  /\ rw_cells asegs m g_current_verbosity [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m g_tls_index [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0xfffffffffffff800)]
  /\ rw_cells asegs m g_got_dtls_off [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m g_tls_dtls [C8 (Z_to_bv 64 DTV)]
  /\ rw_cells asegs m (DTV + 24) [C8 (Z_to_bv 64 dtvbeg)].

Lemma dtls_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (DTV dtvbeg lo : Z),
  dtls_cells DTV dtvbeg m -> 0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> 0x6ca000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 144, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 g_tls_index) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 dtls_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) HD HDL HB ST LO ILO MI.
  unfold g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index,
    g_got_dtls_off, g_tls_dtls, dtls_entry, tpA in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 144%nat ST.
  zidle_begin sp 144%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 10 zstep. ifF.
  do 10 zstep. ifF.
  do 4 zstep. ifF.
  zstep. ifT.
  zstep. ifF.
  do 4 zstep. ifT.
  do 5 zstep. ifF.
  do 15 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

Ltac sp_facts :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_unsigned ?sp + ?k)] =>
      lazymatch goal with
      | _ : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + k)) = _ |- _ => fail
      | _ => let E := fresh "Esp" in
             assert (E : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + k)) = bv_unsigned sp + k)
               by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp) as Hr; unfold bv_modulus in Hr; cbn [Z.of_N] in Hr; lia)
      end
  end.

Definition ttls_cells (T : Z) (m : mem) (tb te : word) : Prop := rw_cells asegs m (T + 48) [C8 tb; C8 te].

Definition tga_cells (DTV dtvbeg : Z) (m : mem) : Prop :=
  rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_real_tls_get_addr [C8 (Z_to_bv 64 musl_tls_get_addr_entry)]
  /\ rw_cells asegs m g_dtv_ptr [C8 (Z_to_bv 64 g_dtv)]
  /\ rw_cells asegs m g_dtv1 [C8 (Z_to_bv 64 dtv1_val)]
  /\ dtls_cells DTV dtvbeg m.

Lemma tls_get_addr_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (DTV dtvbeg TCX T lo : Z) (tb te : word),
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 ->
  0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x6ca000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc tpA [(bv_unsigned sp - 176, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 g_tls_index) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 tls_get_addr_entry) fc None m (seg_rom asegs)).
Proof.
  intros until te. intros (AI & RL & DP & D1 & DC) TC TT HD HDL HB HX HXL HT HTL ST LO ILO MI.
  destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
  unfold ttls_cells, g_real_tls_get_addr, musl_tls_get_addr_entry, tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  carve_frame 32%nat ST.
  zidle_begin_rw sp 32%Z MUz WMz.
  do 7 zstep.
  zidle_end MUz WMz.
  sp_facts.
  call try_init_spec; [exact AI| rewrite Esp; exact ST| rewrite Esp; lia| lia| assumption|].
  do 5 zstep.
  call musl_tls_get_addr_spec; [split; [exact G5| split; assumption]| assumption|].
  do 2 zstep. ifF.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TX]. }
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
  do 6 zstep.
  call (dtls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg lo).
  1:{ split; [exact G1|split; [exact G2|split; [exact G3|split; [exact G4|split; [exact G5|split; [exact G6|split; [exact G7|exact G8]]]]]]]. }
  all: rewrite ?Esp in *; try lia; try eassumption.
  do 6 zstep.
  release_frame FR POST (bv_unsigned sp).
  zstep.
  finish.
Qed.
