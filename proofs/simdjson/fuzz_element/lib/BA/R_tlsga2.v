(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs I_ikit R_tlsgetaddr.
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

Lemma musl_tls_get_addr_p_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p : Z),
  rw_cells asegs m p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> 0 < p -> p + 16 <= 2 ^ 47 ->
  rw_cells asegs m g_dtv_ptr [C8 (Z_to_bv 64 g_dtv)] -> rw_cells asegs m g_dtv1 [C8 (Z_to_bv 64 dtv1_val)] -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dtv1_val m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 musl_tls_get_addr_entry) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros TI HP HPH DP D1 MI. unfold g_dtv_ptr, g_dtv, g_dtv1, dtv1_val, musl_tls_get_addr_entry, tpA in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 9 zstep.
  finish.
Qed.

Lemma dtls_p_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p DTV dtvbeg lo : Z),
  rw_cells asegs m p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> 0 < p -> bv_unsigned sp <= p -> p + 16 <= 2 ^ 47 ->
  dtls_cells DTV dtvbeg m -> 0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> 0x6ca000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 144, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 dtls_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros TI HP HSP HPH (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) HD HDL HB ST LO ILO MI.
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

Lemma tls_get_addr_p_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p DTV dtvbeg TCX T lo : Z) (tb te : word),
  rw_cells asegs m p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> 0 < p -> bv_unsigned sp <= p -> p + 16 <= 2 ^ 47 ->
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 ->
  0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x6ca000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dtv1_val [(bv_unsigned sp - 176, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 tls_get_addr_entry) fc None m (seg_rom asegs)).
Proof.
  intros until te. intros TI HP HSP HPH (AI & RL & DP & D1 & DC) TC TT HD HDL HB HX HXL HT HTL ST LO ILO MI.
  pose proof DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
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
  call (musl_tls_get_addr_p_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ p TI HP HPH DP D1); [assumption|].
  do 2 zstep. ifF.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TX]. }
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
  do 6 zstep.
  assert (HSP' : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) <= p) by (rewrite Esp; lia).
  call (dtls_p_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ p DTV dtvbeg lo TI HP HSP' HPH
          (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))) HD HDL HB).
  all: rewrite ?Esp in *; try lia; try eassumption.
  do 6 zstep.
  release_frame FR POST (bv_unsigned sp).
  zstep.
  finish.
Qed.
