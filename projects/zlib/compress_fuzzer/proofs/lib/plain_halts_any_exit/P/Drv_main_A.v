(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Str_tac Startup_glue InitMem Layout Exit Startup Printf_lib Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_main_defs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_compress_fuzzer_repro.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Src_zlib_compress_fuzzer_repro.M.phdrs.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
(* the auxv as P/Startup_B states it (pauxv), named qualified; the image's entry word *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Startup_B.
Notation pentry := (Z_to_bv 64 (Z.of_N Src_zlib_compress_fuzzer_repro.M.init_pc)).
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.

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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call psegs m mm MU WM end end.

Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : ro_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8ro segs m ?A _ |- _ => zidle_nspZ H A q
    end
  end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma Z_to_bv8_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH, Z_to_bv8_unsigned. reflexivity. Qed.
Lemma zb_map_unsigned : forall bs : list byte, zb (map bv_unsigned bs) = bs.
Proof. intros bs. unfold zb. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH, Z_to_bv8_unsigned. reflexivity. Qed.
Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
  intros bs NI. apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia].
  exfalso. apply NI. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.
Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Section Pieces.
  (* port727: the block is the family's img_at ('s build_stack_bytes) and the launch's
     geometry comes as GEOM; the pieces are read off by P/InitMem's img_pieces (the donor's Plain/RDriver_kit form). *)
  Variables (sp : word) (argv envp : list (list byte)) (uid : word) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at psegs m usp (img_at sp argv envp uid).
  Hypothesis GEOM : launch_ok run_la sp (ed_top run_draw) argv envp run_execfn.

  (* the old seven conjuncts in the old order, over P/InitMem's forms (the envp pointers and the two string
     blocks are read by no caller of the walk; they still hold, so they are kept) *)
  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs (ed_top run_draw) argv envp run_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (envp_addr sp argv) (u64s (envp_ptrs (ed_top run_draw) argv envp run_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (auxv_addr sp argv envp)
      (u64s (Startup_B.pauxv run_la run_hw pentry uid run_gid (Z_to_bv 64 (rnd_addr (la_rseq run_la) sp argv envp))
                             (Z_to_bv 64 (xfn_base (ed_top run_draw) argv envp run_execfn)))) /\
    bytes_at psegs m (str_base (ed_top run_draw) argv envp run_execfn) (flatten_strings argv) /\
    bytes_at psegs m (env_base (ed_top run_draw) argv envp run_execfn) (flatten_strings envp) /\
    bytes_at psegs m (rnd_addr (la_rseq run_la) sp argv envp) (rnd_bytes run_draw).
  Proof.
    destruct GEOM as (G & _).
    destruct (img_pieces psegs run_la pph pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw run_draw m IMG G)
      as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & _).
    rewrite (Startup_B.pauxv_auxv_words run_la pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw) in B3.
    rewrite app_assoc in B2. apply bytes_at_app in B2. destruct B2 as [B2 _].
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - exact B1.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. exact B2.
    - exact B3.
    - exact B5.
    - exact B6.
    - exact B4.
  Qed.

  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) i = Some (Z_to_bv 64 p) /\
      str_base (ed_top run_draw) argv envp run_execfn <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (img_at sp argv envp uid)) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn _. destruct GEOM as (G & _).
    exact (img_argv_cstring psegs run_la pph pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw run_draw m IMG G i s Hn).
  Qed.
End Pieces.

(* where the strings and the block's end sit relative to [sp] (the donor's Section Geom). *)
Section Geom.
  Variables (sp : word) (argv envp : list (list byte)) (uid : word).
  Notation usp := (bv_unsigned sp).
  Hypothesis GEOM : launch_ok run_la sp (ed_top run_draw) argv envp run_execfn.

  Lemma str_base_lo : usp + 8 * (argc argv + envc envp) + 184 <= str_base (ed_top run_draw) argv envp run_execfn.
  Proof.
    destruct GEOM as (G & _). pose proof (str_base_ge _ _ _ _ _ _ G) as SB.
    pose proof (head_len_ge (la_rseq run_la) argv envp) as HL.
    assert (ASZ : (160 <= auxv_size (la_rseq run_la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq run_la); lia).
    lia.
  Qed.

  Lemma img_at_end : usp + Z.of_nat (length (img_at sp argv envp uid)) = bv_unsigned (ed_top run_draw)
                     /\ bv_unsigned (ed_top run_draw) <= 0x800000000000.
  Proof.
    destruct GEOM as (G & TW). unfold sp_window_hi in TW.
    pose proof (img_length run_la pph pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw run_draw G) as L.
    unfold img_at. split; lia.
  Qed.
End Geom.

End WithCeiling0.
Ltac img_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside crt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

From Stdlib Require PrimString PrimInt63 Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PERF_HEX__.
Import PrimInt63 Uint63.
Definition is_hexc__ (c : PrimInt63.int) : bool :=
  ((Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63) || (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63))%bool.
Fixpoint hex_all_z__ (s : PrimString.string) (z : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => is_hexc__ (PrimString.get s (Uint63.of_Z z)) && hex_all_z__ s (z + 1) n'
  end.
Lemma hex_all_z_spec__ : forall s n z, hex_all_z__ s z n = true ->
  forall k, (z <= k < z + Z.of_nat n)%Z -> is_hexc__ (PrimString.get s (Uint63.of_Z k)) = true.
Proof.
  intros s n. induction n as [|n IH]; intros z H k Hk; [lia|].
  cbn [hex_all_z__] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec k z) as [->|NE]; [exact H1|]. apply (IH (z + 1)%Z H2). lia.
Qed.
Lemma is_hexc_nybble__ : forall c, is_hexc__ c = true -> (hex_nybble c <? 16)%N = true.
Proof.
  intros c H. unfold is_hexc__ in H. unfold hex_nybble.
  pose proof (Uint63.to_Z_bounded c) as B.
  destruct (Uint63.leb 48%uint63 c) eqn:E1; destruct (Uint63.leb c 57%uint63) eqn:E2; cbn [andb orb] in H |- *.
  - apply Uint63.leb_spec in E1, E2. change (Uint63.to_Z 48%uint63) with 48%Z in E1. change (Uint63.to_Z 57%uint63) with 57%Z in E2.
    apply N.ltb_lt. lia.
  - apply andb_prop in H. destruct H as [H3 H4]. rewrite H3, H4. cbn [andb].
    apply Uint63.leb_spec in H3, H4. change (Uint63.to_Z 97%uint63) with 97%Z in H3. change (Uint63.to_Z 102%uint63) with 102%Z in H4.
    apply N.ltb_lt. lia.
  - apply andb_prop in H. destruct H as [H3 H4]. rewrite H3, H4. cbn [andb].
    apply Uint63.leb_spec in H3, H4. change (Uint63.to_Z 97%uint63) with 97%Z in H3. change (Uint63.to_Z 102%uint63) with 102%Z in H4.
    apply N.ltb_lt. lia.
  - apply andb_prop in H. destruct H as [H3 H4]. rewrite H3, H4. cbn [andb].
    apply Uint63.leb_spec in H3, H4. change (Uint63.to_Z 97%uint63) with 97%Z in H3. change (Uint63.to_Z 102%uint63) with 102%Z in H4.
    apply N.ltb_lt. lia.
Qed.
Lemma hex_byte_at_some__ : forall s (i : N),
  (2 * Z.of_N i + 1 < Uint63.to_Z (PrimString.length s))%Z ->
  is_hexc__ (PrimString.get s (Uint63.of_Z (2 * Z.of_N i))) = true ->
  is_hexc__ (PrimString.get s (Uint63.of_Z (2 * Z.of_N i + 1))) = true ->
  exists b, hex_byte_at s i = Some b.
Proof.
  intros s i HL H0 H1. unfold hex_byte_at.
  pose proof (Uint63.to_Z_bounded (PrimString.length s)) as B.
  rewrite N2Z.inj_add, N2Z.inj_mul. change (Z.of_N 2) with 2%Z. change (Z.of_N 1) with 1%Z.
  assert (LT : Uint63.ltb (Uint63.of_Z (2 * Z.of_N i + 1)) (PrimString.length s) = true).
  { apply Uint63.ltb_spec. rewrite Uint63.of_Z_spec. rewrite Z.mod_small; [lia|]. unfold Uint63.wB in *. lia. }
  rewrite LT. cbn [orb].
  rewrite (is_hexc_nybble__ _ H0), (is_hexc_nybble__ _ H1). cbn [andb]. eexists. reflexivity.
Qed.
Lemma stk_of_seg__ : forall segs (m : word -> option byte) (seg : Segment) (c : PrimString.string) (lo hi : Z),
  (0 <= lo)%Z -> (hi <= 2^64)%Z ->
  (forall a : Z, (lo <= a < hi)%Z -> find_segment segs a 1 = Some seg) ->
  seg_readable seg = true -> seg_writable seg = true -> seg_bytes seg = [c] ->
  (Z.of_N (seg_base seg) <= lo)%Z ->
  (2 * (hi - Z.of_N (seg_base seg)) <= Uint63.to_Z (PrimString.length c))%Z ->
  hex_all_z__ c (2 * (lo - Z.of_N (seg_base seg))) (Z.to_nat (2 * (hi - lo))) = true ->
  (forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None) ->
  stk segs m lo hi.
Proof.
  intros segs m seg c lo hi L0 H64 FS RD WR SB BL LEN HX NONE'.
  split; [exact L0|]. split; [exact H64|]. intros a Ha.
  assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (Hm : m (wa a) = None) by (apply NONE'; rewrite Ua; exact Ha).
  remember (Z.to_N (a - Z.of_N (seg_base seg))) as off eqn:Hoff.
  assert (Eoff : Z.of_N off = (a - Z.of_N (seg_base seg))%Z) by (rewrite Hoff; rewrite Z2N.id by lia; reflexivity).
  assert (KEY : exists b, segment_byte_at [c] off = Some b).
  { cbn [segment_byte_at].
    assert (LT : (off <? Z.to_N (Uint63.to_Z (PrimString.length c) / 2))%N = true).
    { apply N.ltb_lt. apply N2Z.inj_lt. rewrite Eoff, Z2N.id by (apply Z.div_pos; [apply Uint63.to_Z_bounded| lia]).
      cut (a - Z.of_N (seg_base seg) + 1 <= Uint63.to_Z (PrimString.length c) / 2)%Z; [lia|].
      apply Z.div_le_lower_bound; lia. }
    rewrite LT. apply hex_byte_at_some__.
    - rewrite Eoff. lia.
    - apply (hex_all_z_spec__ c _ _ HX). rewrite Eoff, Z2Nat.id by lia. lia.
    - apply (hex_all_z_spec__ c _ _ HX). rewrite Eoff, Z2Nat.id by lia. lia. }
  destruct KEY as [b KEY].
  split.
  - unfold wview. rewrite Hm, Ua, (FS a Ha), WR, SB. rewrite <- Hoff, KEY. discriminate.
  - exists b. unfold mrd. rewrite Hm. unfold seg_rom, memory_read. rewrite Ua, (FS a Ha), RD, SB. rewrite <- Hoff.
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite KEY. reflexivity.
Qed.
End PERF_HEX__.
Lemma find_seg3__ : forall a, (0x2a000 <= a < 0x5c000)%Z -> find_segment psegs a 1 = Some Src_zlib_compress_fuzzer_repro_segment_003.
Proof.
  intros a Ha. unfold Image.psegs, Src_zlib_compress_fuzzer_repro.M.loaded_segments, Src_zlib_compress_fuzzer_repro_loaded_segments.
  cbn [find_segment seg_base seg_size Src_zlib_compress_fuzzer_repro_segment_000 Src_zlib_compress_fuzzer_repro_segment_001 Src_zlib_compress_fuzzer_repro_segment_002 Src_zlib_compress_fuzzer_repro_segment_003 Z.of_N].
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  try reflexivity;
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H : (_ && _)%bool = false |- _ => apply andb_false_iff in H; destruct H
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
  end; lia.
Qed.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section InitFacts.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (m : mem).
  Hypothesis NONE : forall a : word, (0x29000 <= bv_unsigned a < 0x5c000)%Z -> outside (crt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0x5ab90 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0x5ab98 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0x29570 [C8 (Z_to_bv 64 0x5ab70)].
  Hypothesis GUARD : rw_cells psegs m 0x5ab70 [C8 rr_guard].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMG : bytes_at psegs m (bv_unsigned sp0) (img_at sp0 argv envp uid).
  Hypothesis GEOM : launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn.
  Hypothesis CEIL : ceil_ok sp0.

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs)) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    intros a Ha. apply NONE; [lia|]. unfold crt_written. cbn. lia.
  Qed.

  Lemma rauxv_ok_init : rauxv_ok m (bv_unsigned sp0).
  Proof.
    (* the donor's proof (Plain/RDriver_kit) over the new rauxv_ok; ours keep CEIL and rr_secret *)
    destruct (stack_pieces sp0 argv envp uid m IMG GEOM) as (_ & _ & _ & AUXW & _ & _ & RND).
    destruct (img_at_end sp0 argv envp uid GEOM) as [PE TW].
    pose proof (str_base_lo sp0 argv envp GEOM) as SBL.
    destruct GEOM as (G & _). pose proof (str_base_ge _ _ _ _ _ _ G) as SB.
    pose proof (head_len_eq (la_rseq run_la) argv envp) as HL. pose proof (lsb_eq argv envp run_execfn) as LE.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (bv_unsigned_in_range 64 sp0) as RS0. unfold bv_modulus in RS0. cbn in RS0.
    unfold ceil_ok in CEIL.
    set (VS := map bv_unsigned
                 [la_sysinfo_ehdr run_la; cw_l1i_size (la_cache run_la); cw_l1i_geom (la_cache run_la);
                  cw_l1d_size (la_cache run_la); cw_l1d_geom (la_cache run_la); cw_l2_size (la_cache run_la);
                  cw_l2_geom (la_cache run_la); cw_l3_size (la_cache run_la); cw_l3_geom (la_cache run_la);
                  la_minsigstksz run_la; run_hw; Z_to_bv 64 4096; Z_to_bv 64 100; Z_to_bv 64 0x10040;
                  Z_to_bv 64 56; Z_to_bv 64 10; Z_to_bv 64 0; Z_to_bv 64 0; pentry; uid; uid; run_gid; run_gid;
                  Z_to_bv 64 0; Z_to_bv 64 (xfn_base (ed_top run_draw) argv envp run_execfn)]).
    assert (LR : Z.of_nat (length (rauxv_list VS (la_rseq run_la) (rnd_addr (la_rseq run_la) sp0 argv envp)))
                 = 2 * Z.of_nat (auxv_count (la_rseq run_la))).
    { unfold rauxv_list, auxv_count. rewrite length_map. destruct (la_rseq run_la); reflexivity. }
    exists (auxv_addr sp0 argv envp), VS, (la_rseq run_la), (rnd_addr (la_rseq run_la) sp0 argv envp).
    split; [apply (proj2 heap_init)|].
    split.
    { replace (rauxv_list VS (la_rseq run_la) (rnd_addr (la_rseq run_la) sp0 argv envp))
        with (Startup_B.pauxv run_la run_hw pentry uid run_gid (Z_to_bv 64 (rnd_addr (la_rseq run_la) sp0 argv envp))
                              (Z_to_bv 64 (xfn_base (ed_top run_draw) argv envp run_execfn))); [exact AUXW|].
      subst VS. unfold rauxv_list, Startup_B.pauxv, MallocRep.wz.
      destruct (la_rseq run_la); cbn [map nth app]; rewrite !Z_to_bv_bv_unsigned; reflexivity. }
    split.
    { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
      unfold draw_secret in R. rewrite Z_to_bv_bv_unsigned in R. exact R. }
    rewrite LR. unfold auxv_addr, rnd_addr, str_base, argc, envc in *.
    repeat split; lia.
  Qed.

  Lemma stderr_init : rw_cells psegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5afd0 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)).
  Proof.
    unfold file_cells.
    img_chunk0 NONE m 0x2a5b0 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5afd0 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)) H.
    unfold file_cells in H. exact H.
  Qed.
  Lemma stderr_wfile0_init : stderr_wfile0 m.
  Proof.
    exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (zeros 80). split; [apply stderr_init|].
    split; [vm_compute; reflexivity|]. split; [left; reflexivity| lia].
  Qed.
  Lemma stderr_wfile_init : stderr_wfile m.
  Proof. apply stderr_wfile0_wfile, stderr_wfile0_init. Qed.

  Lemma zl_statics_init : zl_statics m.
  Proof.
    unfold zl_statics, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI.
    split; [intros a Ha; apply NONE; [lia| cbn [outside crt_written]; lia]|].
    split; [intros a Ha; apply NONE; [lia| cbn [outside crt_written]; lia]|].
    split; [exists (wz 0), (wz 0); let A := eval cbv delta [ZH_STATICS] in ZH_STATICS in (img_chunk0 NONE m A [C8 (wz 0); C8 (wz 0)] H; exact H)|].
    let A := eval cbv delta [ZL_MREPL] in ZL_MREPL in (img_chunk0 NONE m A [C4 (wz 0)] H; exact H).
  Qed.

  Lemma adp_init : adp_cells ATX0 m.
  Proof.
    unfold adp_cells, RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0. cbn [atx_n atx_head atx_f0 atx_a0].
    split; [img_chunk0 NONE m 0x3a7f0 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x3a7f4 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5a948 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5a94c [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5a958 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H; exact H|].
    img_chunk0 NONE m 0x5aa68 [C8 (Z_to_bv 64 0)] H; exact H.
  Qed.
  Lemma initflag_init : rdrv_statics m.
  Proof. exists ATX0. apply adp_init. Qed.
  Lemma dso_init : rw_cells psegs m 0x2a588 [C8 (wz 0x2a588)].
  Proof. img_chunk0 NONE m 0x2a588 [C8 (wz 0x2a588)] H. exact H. Qed.

  Lemma stage_init : stk psegs m RSTAGE (RSTAGE + 65536).
  Proof.
    apply (PERF_HEX__.stk_of_seg__ psegs m Src_zlib_compress_fuzzer_repro_segment_003 Src_zlib_compress_fuzzer_repro_seg_bytes_003).
    - lia.
    - lia.
    - intros a Ha. apply find_seg3__. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. lia.
    - apply Z.leb_le. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - intros a Ha. apply NONE; [lia| cbn [outside crt_written]; lia].
  Qed.
End InitFacts.

End WithCeiling1.
Ltac open_at_main AM :=
  destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & EMS
                 & MI & ST & TDa & ERR & TDb & LCa & LCb & MT & SI & G2 & HW & ENVC & DS & GU & GD & GOT0 & GCX & GSE & GFZ & GOT3 & GIN & GG & GFI
                 & INA & FIA & SEP & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & WR & HP0 & NONE & Ht).

Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem main_to_P1_proof : main_to_P1_stmt.
Proof.
  unfold main_to_P1_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS GEOM ARGC2 AM.
  open_at_main AM. subst ms.
  exists t. split; [exact Ht|].
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
  assert (HC2 : argc argv = 2) by (unfold argc; lia).
  clear SEF WR INA INI GOT0 GOT3 GIN GD DS ENVC HW G2 SI MT TDb.
  destruct SOF as (sflags & smode & stail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
  unfold file_cells in SOF1. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add] in SOF1.
  pose proof (munch_refl [(bv_unsigned sp0 - 6144513, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  rewrite HC2.
  carve_frame 80%nat ST.
  zidle_beginZ (bv_unsigned sp0) 128%Z MUz WMz.
  do 12 lstep.
  zidle_end MUz WMz.
  if_false.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (NONE' : forall a : word, (0x29000 <= bv_unsigned a < 0x5c000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
      by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
    destruct (heap_init sp0 argv envp mf NONE' LCa LCb GG GU MI) as [HEAP AUXC];
    pose proof (rauxv_ok_init sp0 argv envp uid mf NONE' LCa LCb GG GU MI IMG GEOM CEIL) as RAUX;
    pose proof (stderr_wfile0_init mf NONE') as SWF;
    pose proof (zl_statics_init mf NONE') as FLG;
    pose proof (initflag_init mf NONE') as IFL;
    pose proof (dso_init mf NONE') as DSOI;
    pose proof (stage_init mf NONE') as STG0
  end.
  apply evt_done. unfold P1.
  exists t0, t1, t2, a3, a4, a5, a6, a7, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6. eexists. eexists.
  split. { unfold Drv_main_defs.RMAIN_RET, RP1, RATP, RMAIN. cbv delta [mkR]. reflexivity. }
  split. { unfold MFRAME, RMAIN, Drv_main_defs.RMAIN_RET. rewrite HC2. exact FR. }
  split.
  { unfold BASE, LO, ESTAT, RGOT_LLVMINIT. split; [exact ST|]. split; [exact MI|].
    split. { split_spine; hyp_by_addr. }
    split; [exact RAUX|]. split; [split; [exact GG| exact GU]|]. split; [| exact IMG].
    unfold lx_statics. split; [exact GSE | exact SEP]. }
  split; [exact HEAP|].
  split. { unfold RATP. replace (bv_unsigned (wz 0x3a900) + -164)%Z with 0x3a85c%Z by (unfold wz; rewrite unsigned_lit by lia; reflexivity). exact ERR. }
  split. { exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
           exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6))))). }
  split; [exact SWF|]. split; [exact FLG|]. split; [exact IFL| exact STG0].
Qed.

Section Usage.

  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Theorem main_usage_proof : main_usage_stmt.
  Proof.
    unfold main_usage_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS GEOM ARGCN AM.
    open_at_main AM. subst ms.
    pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (HCR : 0 <= argc argv <= 1024 /\ argc argv <> 2) by (unfold argc; lia).

    assert (Harg0 : exists arg0 rest, argv = arg0 :: rest).
    { destruct argv as [|a r]; [cbn in VA1; lia | exists a, r; reflexivity]. }
    destruct Harg0 as (arg0 & rest & EARGV).
    assert (Hnth : nth_error argv 0 = Some arg0) by (rewrite EARGV; reflexivity).
    destruct (argv_cstring sp0 argv envp uid m IMG GEOM 0 arg0 Hnth ltac:(clear - SP16; Z.div_mod_to_equations; lia))
      as (p & slack & HP & PLO & PHI & STR0 & SLK).
    rewrite HP0 in HP. assert (EW : Z_to_bv 64 P0 = Z_to_bv 64 p) by congruence. clear HP.
    pose proof (str_base_lo sp0 argv envp GEOM) as SBL. unfold argc, envc in SBL. destruct (img_at_end sp0 argv envp uid GEOM) as [IME TW].
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMB.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Hnth)) as NONUL0. cbn beta in NONUL0.
    pose proof (proj1 (Forall_forall _ _) VA3 arg0 (nth_error_In _ _ Hnth)) as LEN0. cbn beta in LEN0.

    destruct (stack_pieces sp0 argv envp uid m IMG GEOM) as (_ & ARGV & _).
    destruct SOF as (sflags & smode & stail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    unfold file_cells in SOF1. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add] in SOF1.
    clear SEF WR INA INI GOT0 GOT3 GIN GD DS ENVC HW G2 SI MT TDb.
    pose proof (munch_refl [(bv_unsigned sp0 - 6144513, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM at 1.
    eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 80%nat ST.
    zidle_beginZ (bv_unsigned sp0) 128%Z MUz WMz.
    do 12 lstep.
    zidle_end MUz WMz.
    if_cases Hc; zify_cond Hc; [| exfalso; rewrite ?unsigned_lit in Hc by lia; lia].

    lstep. lstep. lstep.
    pose proof (rd_u64s_g psegs _ (bv_unsigned sp0 + 8) _ 0 _ (Z_to_bv 64 (bv_unsigned sp0 + 8)) ARGV
                  ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite EW. lstep. lstep. lstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (0x29000 <= bv_unsigned a < 0x5c000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
      pose proof (stderr_wfile_init mf NONE') as SWF;
      pose proof (adp_init mf NONE') as (AX1 & AX2 & AX3 & AX4 & AX5 & AX6);
      unfold RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0 in AX1, AX2, AX3, AX4, AX5, AX6; cbn [atx_n atx_head atx_f0 atx_a0] in AX1, AX4, AX5, AX6;
      pose proof (dso_init mf NONE') as DSOI; clear NONE NONE'
    end.
    apply evt_done.

    change (io_diag io (DUsage (nth 0 (argv_Z argv) []))) with (s_diag (St:=PState) (DUsage (nth 0 (argv_Z argv) []))).
    replace (nth 0 (argv_Z argv) []) with (map bv_unsigned arg0) by (rewrite EARGV; reflexivity).
    assert (ESP112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -128)) = bv_unsigned sp0 + -128) by (apply unsigned_lit; lia).
    eapply implM_bind.
    { eapply (FPR (DUsage (map bv_unsigned arg0))) with (lo := bv_unsigned sp0 - 6144513) (canary := rr_guard);
        [ exact FWE | exact FLS | exact SWF | reflexivity |
        | rewrite ESP112; exact ST | rewrite ESP112; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite ESP112; lia
        | split; [exact GG | exact GU] | exact MI | vm_compute; reflexivity ].
      rewrite ?ESP112. cbn [diag_args]. split; [reflexivity|]. exists slack.
      rewrite unsigned_lit by lia. rewrite zb_map_unsigned. unfold zlength. rewrite length_map.
      split; [exact STR0|]. split; [apply map_unsigned_pos; exact NONUL0|]. split; [exact SLK|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 & -> & MU1 & WM1 & MI1 & FRM1 & FREGS & ST1 & SWF1 & SSP1 & ->).
    rewrite (ret_pc_even _) by (cbn; lia). rewrite ESP112 in MU1, ST1.
    clear MU WM. lazymatch type of MU1 with munch _ ?mprev m2 => transport_after_call psegs mprev m2 MU1 WM1 end.
    apply implM_ret.

    step. step. do 9 step. step. step.
    try rewrite (ret_pc_even _) by (cbn; lia).
    step.
    release_frame FR ST1 (bv_unsigned sp0 + -48).
    apply evt_done.
    destruct SWF1 as (eflags & emode & ee & ewend & etail & SEF1 & _).
    destruct SSP1 as [GG1 GU1]. unfold got_ssp, ssp_guard in GG1, GU1.
    unfold at_exit.
    do 31 eexists. exists Ft, fc', m2, (bv_unsigned sp0 - 6144513), t. do 4 eexists. exists rr_guard. do 4 eexists.
    split. { cbv delta [mkR]. reflexivity. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -48)) = bv_unsigned sp0 + -48) by (apply unsigned_lit; lia).
    rewrite !ESP.
    split; [exact ST1|].
    split; [exact TDa|]. split; [exact EXL|]. split; [exact GFI|]. split; [exact FIA|]. split; [exact FIN|]. split; [exact GCX|].
    split; [exact DSOI|]. split; [exists ATX0; exact (conj AX1 (conj AX2 (conj AX3 (conj AX4 (conj AX5 AX6)))))|].
    split; [exact LCa|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split. { cbn [ps_so ps_init]. exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
             split; [exact SOF1|]. split; [exact SOF2|]. split; [exact SOF3|]. split; [exact SOF4|]. split; [exact SOF5| exact SOF6]. }
    split. { exists eflags, emode, ee, ewend, etail. exact SEF1. }
    split; [exact GG1|]. split; [exact GU1|]. split; [exact MI1|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|]. split; lia.
  Qed.
End Usage.
End WithCeiling2.
