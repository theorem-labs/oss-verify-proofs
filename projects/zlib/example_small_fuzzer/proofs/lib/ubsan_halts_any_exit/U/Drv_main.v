(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.

Module Drv_main_A.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
(* the auxv as P/Startup_B states it (pauxv), named qualified; the image's entry word *)
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Startup.
Notation pentry := (Z_to_bv 64 (Z.of_N Tgt_example_small_fuzzer_ubsan.M.init_pc)).
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
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
      unfold zidle in *; transport_after_call usegs m mm MU WM end end.
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
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
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
  (* the block is the family's img_at (727298f3's build_stack_bytes) and the launch's
     geometry comes as GEOM; the pieces are read off by P/InitMem's img_pieces (the donor's Plain/RDriver_kit form). *)
  Variables (sp : word) (argv envp : list (list byte)) (uid : word) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at usegs m usp (img_at sp argv envp uid).
  Hypothesis GEOM : launch_ok run_la sp (ed_top run_draw) argv envp run_execfn.

  (* the old seven conjuncts in the old order, over P/InitMem's 727298f3 forms (the envp pointers and the two string
     blocks are read by no caller of the walk; they still hold, so they are kept) *)
  Lemma stack_pieces :
    bytes_at usegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at usegs m (usp + 8) (u64s (argv_ptrs (ed_top run_draw) argv envp run_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (envp_addr sp argv) (u64s (envp_ptrs (ed_top run_draw) argv envp run_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (auxv_addr sp argv envp)
      (u64s (Startup_B.pauxv run_la run_hw pentry uid run_gid (Z_to_bv 64 (rnd_addr (la_rseq run_la) sp argv envp))
                             (Z_to_bv 64 (xfn_base (ed_top run_draw) argv envp run_execfn)))) /\
    bytes_at usegs m (str_base (ed_top run_draw) argv envp run_execfn) (flatten_strings argv) /\
    bytes_at usegs m (env_base (ed_top run_draw) argv envp run_execfn) (flatten_strings envp) /\
    bytes_at usegs m (rnd_addr (la_rseq run_la) sp argv envp) (rnd_bytes run_draw).
  Proof.
    destruct GEOM as (G & _).
    destruct (img_pieces usegs run_la pph pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw run_draw m IMG G)
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
      bytes_at usegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn _. destruct GEOM as (G & _).
    exact (img_argv_cstring usegs run_la pph pentry sp (ed_top run_draw) argv envp run_execfn uid run_gid run_hw run_draw m IMG G i s Hn).
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
  assert (H : rw_cells usegs m A cs);
  [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 usegs m A bs);
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
Lemma find_seg3__ : forall a, (0x2d000 <= a < 0x5e000)%Z -> find_segment usegs a 1 = Some Tgt_example_small_fuzzer_ubsan_segment_003.
Proof.
  intros a Ha. unfold Image.usegs, Tgt_example_small_fuzzer_ubsan.M.loaded_segments, Tgt_example_small_fuzzer_ubsan_loaded_segments.
  cbn [find_segment seg_base seg_size Tgt_example_small_fuzzer_ubsan_segment_000 Tgt_example_small_fuzzer_ubsan_segment_001 Tgt_example_small_fuzzer_ubsan_segment_002 Tgt_example_small_fuzzer_ubsan_segment_003 Z.of_N].
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
  Hypothesis NONE : forall a : word, (0x2b000 <= bv_unsigned a < 0x5e000)%Z -> outside (crt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells usegs m 0x5d688 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells usegs m 0x5d690 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells usegs m 0x2c078 [C8 (Z_to_bv 64 0x5d668)].
  Hypothesis GUARD : rw_cells usegs m 0x5d668 [C8 rr_guard].
  Hypothesis MI : mem_inv usegs m.
  Hypothesis IMG : bytes_at usegs m (bv_unsigned sp0) (img_at sp0 argv envp uid).
  Hypothesis GEOM : launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn.
  Hypothesis CEIL : ceil_ok sp0.

  Lemma heap_init : RHEAP (ps_init (reservedZ usegs)) [] m /\ rw_cells usegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
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
    {
             rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
      unfold draw_secret in R. rewrite Z_to_bv_bv_unsigned in R. exact R. }
    rewrite LR. unfold auxv_addr, rnd_addr, str_base, argc, envc in *.
    repeat split; lia.
  Qed.

  Lemma stderr_init : rw_cells usegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5dac8 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)).
  Proof.
    unfold file_cells.
    img_chunk0 NONE m 0x2d0b8 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5dac8 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)) H.
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
    split; [img_chunk0 NONE m 0x3d2f0 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x3d2f4 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5d440 [C1 (Z_to_bv 8 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5d444 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] H; exact H|].
    split; [img_chunk0 NONE m 0x5d450 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H; exact H|].
    img_chunk0 NONE m 0x5d560 [C8 (Z_to_bv 64 0)] H; exact H.
  Qed.
  Lemma initflag_init : rdrv_statics m.
  Proof. exists ATX0. apply adp_init. Qed.
  Lemma dso_init : rw_cells usegs m 0x2d090 [C8 (wz 0x2d090)].
  Proof. img_chunk0 NONE m 0x2d090 [C8 (wz 0x2d090)] H. exact H. Qed.

  Lemma stage_init : stk usegs m RSTAGE (RSTAGE + 65536).
  Proof.
    apply (PERF_HEX__.stk_of_seg__ usegs m Tgt_example_small_fuzzer_ubsan_segment_003 Tgt_example_small_fuzzer_ubsan_seg_bytes_003).
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
                 & MI & ST & TDa & ERR & TDb & LCa & LCb & MT & SI & G2 & HW & ENVC & DS & GU & GD & GOT0 & GCX & GSE & GFZ & GDF & GOT3 & GIN & GG & GFI
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
  pose proof (munch_refl [(bv_unsigned sp0 - 6144513, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  rewrite HC2.
  carve_frame 80%nat ST.
  zidle_beginZ (bv_unsigned sp0) 128%Z MUz WMz.
  do 12 lstep.
  zidle_end MUz WMz.
  if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (NONE' : forall a : word, (0x2b000 <= bv_unsigned a < 0x5e000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
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
  split. { unfold RATP. replace (bv_unsigned (wz 0x3d400) + -164)%Z with 0x3d35c%Z by (unfold wz; rewrite unsigned_lit by lia; reflexivity). exact ERR. }
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
    pose proof (munch_refl [(bv_unsigned sp0 - 6144513, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM at 1.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 80%nat ST.
    zidle_beginZ (bv_unsigned sp0) 128%Z MUz WMz.
    do 12 lstep.
    zidle_end MUz WMz.
    if_cases Hc; zify_cond Hc; [| exfalso; rewrite ?unsigned_lit in Hc by lia; lia].
    lstep. lstep. lstep.
    pose proof (rd_u64s_g usegs _ (bv_unsigned sp0 + 8) _ 0 _ (Z_to_bv 64 (bv_unsigned sp0 + 8)) ARGV
                  ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite EW. lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (0x2b000 <= bv_unsigned a < 0x5e000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
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
    clear MU WM. lazymatch type of MU1 with munch _ ?mprev m2 => transport_after_call usegs mprev m2 MU1 WM1 end.
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
End Drv_main_A.


Module Drv_main_B.
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Lemma implM_unfold__ : forall {St A : Type} (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment)
  (c : @OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M St A) (s : St)
  (Q : A -> St -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state -> Prop) ms,
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.implM segs c s Q ms ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree.impl segs (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes.at_node segs) (c s)
    (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree.epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros St A segs c s Q ms H. exact H. Qed.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition S_OOM : Z := 0x10374.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x105cc.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x103bc.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b usegs S_OOM (to_bytes s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b usegs S_SHORT (to_bytes s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b usegs S_OVER (to_bytes s_over) = true. Proof. vm_compute. reflexivity. Qed.

Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv usegs m -> ro_bytes_b usegs A (to_bytes s) = true -> 0x10000 <= A -> A + zlength s <= 0x5e000 ->
  bytes_at usegs m A (to_bytes s).
Proof.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| rewrite to_bytes_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound usegs); exact RO].
Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.
Lemma lit_range : forall s, Forall (fun c => 0 <= c < 256) (str s ++ [10]).
Proof. intros s. apply Forall_app. split; [apply str_range| constructor; [lia| constructor]]. Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl usegs (at_node usegs) (enode n pl) (epost P) ms ->
  implM usegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells usegs m A [CB 0%nat []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma shiftr26_zero_iff : forall a, 0 <= a -> Z.shiftr a 26 = 0 <-> a < 67108864.
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Lemma lb_remove_second : forall p b1 b2, blk_id b2 = p -> List.NoDup (map blk_id [b1; b2]) -> lb_remove p [b1; b2] = [b1].
Proof.
  intros p [[p1 A1] n1] [[p2 A2] n2] E ND. cbn [blk_id fst] in E. subst p2. cbn [map blk_id fst] in ND.
  inversion ND as [|x l NI _]; subst.
  unfold lb_remove. cbn.
  destruct (bptr_eqb p1 p) eqn:E1; cbn.
  - exfalso. apply bptr_eqb_eq in E1. subst p1. apply NI. left. reflexivity.
  - replace (bptr_eqb p p) with true by (symmetry; apply bptr_eqb_eq; reflexivity). cbn. reflexivity.
Qed.

Section CTXB.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling <= LO' /\ LO' + 6144513 = usp0 /\ 0x5e000 <= LO'.
  Proof. destruct VSP as (A & B & C). unfold ceil_ok in CEIL. unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  Definition EXTRA (mm : mem) (s : PState) : Prop :=
    stdout_file mm (ps_so s) /\ stderr_wfile0 mm /\ zl_statics mm /\ rdrv_statics mm.

  Definition extra_addr (a : Z) : Prop := stdout_addr a \/ stderr_addr a \/ zls_addr a \/ drv_addr a.

  Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
    agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
  Proof.
    intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
    exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
    eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. unfold file_cells in Ha. cbn in Ha. lia.
  Qed.

  Lemma EXTRA_agree : forall (P : Z -> Prop) m m' s s',
    agree_on P m m' -> (forall a, extra_addr a -> P a) -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros P m m' s s' AG HP ESO (X1 & X2 & X3 & X4). unfold EXTRA. rewrite ESO.
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact X1]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; right; left; exact Ha| exact X2]|].
    split; [eapply zl_statics_agree; [exact AG| intros a Ha; apply HP; right; right; left; exact Ha| exact X3]|].
    eapply rdrv_statics_agree; [exact AG| | exact X4]. intros a Ha. apply HP. right; right; right. exact Ha.
  Qed.

  Lemma ESTAT_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, estat_addr a -> P a) -> ESTAT TID m -> ESTAT TID m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). unfold ESTAT, RGOT_LLVMINIT in *.
    Ltac tre AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold estat_addr; cbn in Ha; lia].
    split; [tre AG HP A1|]. split; [tre AG HP A2|]. split; [tre AG HP A3|]. split; [tre AG HP A4|].
    split; [tre AG HP A5|]. split; [tre AG HP A6|]. split; [tre AG HP A7|]. split; [tre AG HP A8|].
    split; [tre AG HP A9|]. split; [tre AG HP A10|]. split; [tre AG HP A11| tre AG HP A12].
  Qed.

  Definition base_addr (a : Z) : Prop := estat_addr a \/ lxs_addr a \/ usp0 <= a.

  Lemma BASE_heap : forall LB m m' s' LB', BASE' m -> rheap_pres LB (usp0 + -128) m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> RHEAP s' LB' m' -> BASE' m'.
  Proof.
    intros LB m m' s' LB' (ST & MI & ES & AUX & SSP & LXS & IMG) HP MI' ST' AUX' HP'.
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ESTAT_agree; [exact AG| | exact ES]. intros a Ha. right; left.
             unfold estat_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    split; [exact AUX'|]. split; [exact (RHEAP_ssp _ _ _ HP')|].
    split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. right; left.
             unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    eapply bytes_at_agree; [exact AG| exact IMG| intros a Ha; left; lia].
  Qed.

  Lemma EXTRA_heap : forall LB m m' s s', rheap_pres LB (usp0 + -128) m m' -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros LB m m' s s' HP ESO. apply (EXTRA_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [| exact ESO].
    intros a Ha. right; left.
    unfold extra_addr, stdout_addr, stderr_addr, zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL, drv_addr, RINIT_FLAG, RATX_FIN, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
  Qed.

  Definition WOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RMallocRep.RERRNO /\ snd iv = RMallocRep.RERRNO + 4)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x5e000 <= fst iv))
    \/ (fst iv = RSTAGE /\ RSTAGE <= snd iv <= RSTAGE + 65536).
  Definition WOKE (iv : Z * Z) : Prop := WOK iv \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232).

  Lemma WOK_WOKE : forall W, Forall WOK W -> Forall WOKE W.
  Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv Hiv. left. exact Hiv. Qed.

  Lemma WOKE_outside : forall W a, Forall WOKE W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x5e000 /\ ~ (RMallocRep.RERRNO <= a < RMallocRep.RERRNO + 4) /\ ~ (RSTDERR <= a < RSTDERR + 232)
                          /\ ~ (RSTAGE <= a < RSTAGE + 65536))) -> outside W a.
  Proof.
    pose proof sp_facts as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKE, WOK, LO, RMallocRep.RERRNO in H1. cbn [fst snd] in H1. unfold RMallocRep.RERRNO in Ha. lia.
  Qed.

  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x5e000 /\ ~ (RMallocRep.RERRNO <= a < RMallocRep.RERRNO + 4) /\ ~ (RSTAGE <= a < RSTAGE + 65536))) -> outside W a.
  Proof.
    pose proof sp_facts as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOK, LO, RMallocRep.RERRNO in H1. cbn [fst snd] in H1. unfold RMallocRep.RERRNO in Ha. lia.
  Qed.

  Lemma BASE_munch : forall W m m', BASE' m -> Forall WOKE W -> munch W m m' -> wmono usegs m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> BASE' m'.
  Proof.
    intros W m m' (ST & MI & ES & AUX & SSP & LXS & IMG) HW MU WM MI' ST'. pose proof sp_facts as SF. unfold LO in *.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply ESTAT_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold estat_addr, RMallocRep.RERRNO in *; lia]| exact ES]|].
    split.
    { eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; apply WOKE_outside; [exact HW| left; lia| exact HW|].
      unfold RAUXV_CELL, RMallocRep.RERRNO in *. lia. }
    split; [eapply ssp_cells_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold ssp_addr, got_ssp, ssp_guard, RMallocRep.RERRNO in *; lia]| exact SSP]|].
    split; [eapply lx_statics_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, RMallocRep.RERRNO in *; lia]| exact LXS]|].
    eapply bytes_at_agree; [exact AG| exact IMG|]. intros a Ha. apply WOKE_outside; [exact HW| left; lia].
  Qed.

  Lemma EXTRA_munch : forall W m m' s s', Forall WOK W -> munch W m m' -> wmono usegs m m' -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros W m m' s s' HW MU WM ESO. apply (EXTRA_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)); [| exact ESO].
    intros a Ha. apply WOK_outside; [exact HW|].
    unfold extra_addr, stdout_addr, stderr_addr, zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL, drv_addr, RINIT_FLAG, RATX_FIN, RMallocRep.RERRNO in *. lia.
  Qed.

  Lemma EXTRA_stdio : forall W m m' s s', Forall WOKE W -> munch W m m' -> wmono usegs m m' -> ps_so s' = ps_so s ->
    stderr_wfile0 m' -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros W m m' s s' HW MU WM ESO SE' (X1 & X2 & X3 & X4). pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    unfold EXTRA. rewrite ESO.
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold stdout_addr, RMallocRep.RERRNO in *; lia]| exact X1]|].
    split; [exact SE'|].
    split; [eapply zl_statics_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL, RMallocRep.RERRNO in *; lia]| exact X3]|].
    eapply rdrv_statics_agree; [exact AG| | exact X4]. intros a Ha. apply WOKE_outside; [exact HW|]. unfold drv_addr, RINIT_FLAG, RATX_FIN, RMallocRep.RERRNO in *. lia.
  Qed.

  Lemma RHEAP_munchW : forall s LB W m m', Forall WOKE W -> munch W m m' -> wmono usegs m m' ->
    (forall iv, In iv W -> snd iv <= alloc_ceiling -> (snd iv <= 0x10000 \/ 0x5e000 <= fst iv) ->
                exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
    RHEAP s LB m -> RHEAP s LB m'.
  Proof.
    intros s LB W m m' HW MU WM HB HP. pose proof sp_facts as SF. unfold LO in *.
    eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    apply Forall_forall. intros [lo1 hi1] Hin. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as H.
    unfold WOKE, WOK, rclient_write_ok, RMallocRep.RERRNO, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LO in *. cbn [fst snd] in *.
    destruct H as [[H|[H|[H|H]]]|H]; [left; lia| right; left; lia| right; right| right; left; lia| right; left; lia]. apply (HB (lo1, hi1)); [exact Hin| cbn; lia| cbn; lia].
  Qed.

  Lemma MFRAME_heap : forall LB m m' pd a b c d, rheap_pres LB (usp0 + -128) m m' -> MFRAME sp0 argv m pd a b c d -> MFRAME sp0 argv m' pd a b c d.
  Proof. intros LB m m' pd a b c d HP FR. unfold MFRAME in *. eapply rheap_pres_rw_cells; [exact HP| exact FR| left; cbn; lia]. Qed.
  Lemma MFRAME_munch : forall W m m' pd a b c d, Forall WOKE W -> munch W m m' -> wmono usegs m m' -> MFRAME sp0 argv m pd a b c d -> MFRAME sp0 argv m' pd a b c d.
  Proof.
    intros W m m' pd a b c d HW MU WM FR. unfold MFRAME in *. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact FR|].
    intros x Hx. cbn in Hx. apply WOKE_outside; [exact HW| left; lia].
  Qed.


  Lemma at_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo SP -> lo <= SP - 176 -> 0x5e000 <= lo -> 0 <= SP < 2^64 ->
    ESTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m -> rdrv_statics m ->
    at_exit ps_so code s (MS (mkR ra (wz SP) (wz 0x10800) (wz RATP) t0 t1 t2 s0 s1 (wz code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz 0x23270) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (E1 & E2 & E3 & E4 & E5 & E6 & E6b & E7 & E8 & E9 & E10 & E11) HP SOF SEF MI ATX.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
    unfold at_exit. cbv delta [MallocRep.wz] in *.
    do 31 eexists. exists F, fc, m, lo, TID, (Z_to_bv 64 0x3d338), (Z_to_bv 64 0x3d338), (Z_to_bv 64 0x3d338), (Z_to_bv 64 0), rr_guard.
    exists cdt, thr, sec, tm1.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    split; [exact E5|]. split; [exact E6|]. split; [exact E6b|]. split; [exact ATX|]. split; [exact LC|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. lia.
  Qed.
End CTXB.

Section B.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis GEOM : launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation EXTRA' := EXTRA.
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (img_at sp0 argv envp uid).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma IMGB_bound : usp0 + Z.of_nat (length IMGB) <= 2^64.
  (* by img_at_end; the hypothesis list is the old one plus GEOM, so the lemmas over it
     keep their argument lists *)
  Proof using VSP VARGV VENVP GEOM.
    destruct (img_at_end sp0 argv envp uid GEOM) as [IME TW]. lia.
  Qed.

  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    stk usegs mm LO' (usp0 + -128) ->
    ESTAT TID mm -> RHEAP s LB mm -> stdout_file mm (ps_so s) -> stderr_file mm -> mem_inv usegs mm -> rdrv_statics mm ->
    evt usegs (at_exit ps_so 2 s) (GST 0x15d60 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros ST ES HP SOF SEF MI ATX. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x15d68)) with (Z_to_bv 64 0x15d68) by (symmetry; rpc).
    apply evt_done. eapply (at_exit_intro TID HT 2 s LB); [exact ST| lia| lia| lia| exact ES| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.

  Lemma fprintf_exit : forall (d : diag_msg) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v LO' (usp0 + -128) ->
    BASE' mm -> RHEAP s LB mm -> EXTRA' mm s -> frm0 fc ->
    (forall ms', at_exit ps_so 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag d ;;; K) s Q
      (GST 0x15d38 x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA HP EX FRM HK.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    pose proof EX as (SOF & SE & FL & IB).
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s Q msx) end.
    eapply implM_bind.
    { eapply (FPR d) with (lo := usp0 - 6144513) (canary := rr_guard);
        [exact FWX| exact SWF| apply stderr_wfile0_wfile; exact SE| reflexivity
        | rewrite unsigned_lit by lia; unfold LO in DA; exact DA
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | exact SSP| exact MI| exact FRM]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x15d3c)) with (Z_to_bv 64 0x15d3c) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 6144513, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (HP2 : RHEAP s LB m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact HP].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (SOF2 : stdout_file m2 (ps_so s)).
    { eapply stdout_file_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact SOF]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold stdout_addr, RMallocRep.RERRNO in *. lia. }
    assert (IB2 : rdrv_statics m2).
    { eapply rdrv_statics_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact IB]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold drv_addr, RINIT_FLAG, RATX_FIN, RMallocRep.RERRNO in *. lia. }
    pose proof BA2 as (ST3 & MI3 & ES3 & _).
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    eapply (exit2_tail s LB); [exact ST3| exact ES3| exact HP2| exact SOF2| apply stderr_wfile_file; exact SEW| exact MI3| exact IB2].
  Qed.

  Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    BASE' mm -> RHEAP s LB mm -> EXTRA' mm s ->
    (forall ms', at_exit ps_so 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag DOom ;;; K) s Q
      (GST 0x15d5c x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA HP EX HK.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    pose proof EX as (SOF & SE & FL & IB).
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s Q msx) end.
    cbn [s_diag]. change (concat pieces_oom) with s_oom.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 6144513) (canary := rr_guard) (s := s_oom);
        [exact SE
        | rewrite unsigned_lit by (unfold S_OOM; lia); change (map _ s_oom) with (to_bytes s_oom); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
        | apply lit_range
        | unfold s_oom, zlength; cbn; lia| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | exact SSP| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x15d60)) with (Z_to_bv 64 0x15d60) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 6144513, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (HP2 : RHEAP s LB m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact HP].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (SOF2 : stdout_file m2 (ps_so s)).
    { eapply stdout_file_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact SOF]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold stdout_addr, RMallocRep.RERRNO in *. lia. }
    assert (IB2 : rdrv_statics m2).
    { eapply rdrv_statics_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact IB]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold drv_addr, RINIT_FLAG, RATX_FIN, RMallocRep.RERRNO in *. lia. }
    pose proof BA2 as (ST3 & MI3 & ES3 & _).
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    eapply (exit2_tail s LB); [exact ST3| exact ES3| exact HP2| exact SOF2| apply stderr_wfile0_file; exact SEW| exact MI3| exact IB2].
  Qed.


  Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    RHEAP s [(bufp, A, cap)] mm /\ A = ptr_addr s bufp
    /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  Definition STG (mm : mem) : Prop := stk usegs mm RSTAGE (RSTAGE + 65536).

  Lemma STG_heap : forall LB mm mm', rheap_pres LB (usp0 + -128) mm mm' -> STG mm -> STG mm'.
  Proof.
    intros LB mm mm' HP SG. unfold STG in *. eapply stk_agree; [eapply agree_of_heap_pres; exact HP| exact SG|].
    intros a Ha. right; left.
    unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
  Qed.

  Lemma STG_munch : forall W mm mm', munch W mm mm' -> wmono usegs mm mm' ->
    (forall a, RSTAGE <= a < RSTAGE + 65536 -> outside W a) -> STG mm -> STG mm'.
  Proof.
    intros W mm mm' MU WM HO SG. unfold STG in *. eapply stk_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact SG| exact HO].
  Qed.

  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Definition RDHEAD (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x15b60 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk /\ STG mm
      /\ FRAME' mm /\ BASE' mm /\ EXTRA' mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x15bcc x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk /\ STG mm
      /\ FRAME' mm /\ BASE' mm /\ EXTRA' mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDHEAD fd P1v st' s ms
    | inr RdExit => at_exit ps_so 2 s ms
    | inr (RdDone b c) => RDBRK fd P1v b c s ms
    end.

  Definition rd_read_part (fd : Z) (path : list Z) (len : Z) (st1 : rd_st (ptr:=bptr)) : M PState (rd_st + rd_result) :=
    s <- mget ;;
    let buf := ustage in
    let cnt := Z.min (rd_cap st1 - len) 65536 in
    a <- msys (NRead fd buf cnt) (dec_read buf cnt) ;;
    match a with
    | RdErr _ => io_diag io (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : M PState (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag io DTooBig ;;; mret None
      else
        nb <- raw_malloc (rd_cap st * 2) ;;
        match nb with
        | None => io_diag io DOom ;;; mret None
        | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  Lemma read_loop_body_eq : forall fd path st,
    read_loop_body io raw_malloc raw_free ustage fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 => rd_read_part fd path (zlength (rd_content st)) st1 end).
  Proof. intros. reflexivity. Qed.

  Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> Z.of_nat (length DATA) < rd_cap st1 ->
    STG mm ->
    FRAME' mm -> BASE' mm -> EXTRA' mm s -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (rd_read_part fd (map bv_unsigned arg1) (zlength (rd_content st1)) st1) s (POSTBODY fd P1v)
      (GST 0x15ba4 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU LT SG FR BA EX ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    destruct BU as (P0 & HA & BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). 
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ. unfold MAX_INPUT in CAPR.
    unfold rd_read_part. apply implM_get_bind. cbv beta zeta.
    unfold MFRAME in FR. unfold RMallocRep.RERRNO in ERR. unfold STG in SG.
    set (LEN := Z.of_nat (length DATA)) in *. set (CNT := Z.min (rd_cap st1 - LEN) 65536).
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. assert (ECNT : CNT = Z.min (rd_cap st1 - LEN) 65536) by reflexivity. clearbody LEN CNT.
    assert (LEN0 : 0 <= LEN) by lia. assert (CNT1 : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - LEN) by lia.
    eapply (implM_evt usegs) with (P := fun ms1 => ms1 = GST 0x15bb4 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).
    { zstep. zstep. zstep. if_cases K; zify_cond K.
      - apply evt_done. replace CNT with (rd_cap st1 - LEN) by lia. replace (rd_cap st1 + - LEN) with (rd_cap st1 - LEN) by lia. reflexivity.
      - zstep. apply evt_done. replace CNT with 65536 by lia. reflexivity. }
    cbv beta. intros ms1 ->.
    unfold implM. iprefix. zstep. zstep. zstep.
    destruct (stk_split usegs mm RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SG ltac:(lia)) as [SGlo REST].
    destruct (stk_carve usegs mm RSTAGE (RSTAGE + CNT) (Z.to_nat CNT) SGlo ltac:(lia)) as [_ [sjk DST]].
    replace (RSTAGE + CNT - Z.of_nat (Z.to_nat CNT)) with RSTAGE in DST by lia. clear SGlo.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
    eapply implM_bind.
    { set (w1 := Z_to_bv 64 RSTAGE). unfold ustage. replace RSTAGE with (bv_unsigned w1) by (subst w1; rewrite unsigned_lit; lia).
      eapply implM_of_enode.
      eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.read_spec with (lo := usp0 - 6144513) (junk := sjk) (errv := errv); subst w1; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit RSTAGE) by lia; try reflexivity;
        unfold RMallocRep.RATP; cbn [Z.add];
        first [exact ST | exact DST | exact ERR | exact MI | lia]. }
    cbv beta. intros a s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    unfold RATP in MUc, RES. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc, RES by (unfold RMallocRep.RATP; lia).
    rewrite !(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite !(unsigned_lit RSTAGE) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit RSTAGE) in RES by lia.
    unfold RMallocRep.RATP in MUc, RES. cbn [Z.add] in MUc, RES.
    replace (ret_pc (Z_to_bv 64 0x15bc0)) with (Z_to_bv 64 0x15bc0) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (RSTAGE, RSTAGE + Z.of_nat (Z.to_nat CNT)); (250716, 250716 + 4)]).
    { unfold WOK, LO, RMallocRep.RERRNO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; intros Hiv Hiv2; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (EX2 : EXTRA' m2 s) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX]).
    assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact FR]).
    assert (REST2 : stk usegs m2 (RSTAGE + CNT) (RSTAGE + 65536)).
    { eapply stk_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact REST|]. intros x Hx. cbn. lia. }
    assert (BLK2 : rw_cells usegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA))) junk]).
    { rewrite <- ELEN. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact BLK|]. intros x Hx. cbn in Hx |- *. lia. }
    clear MUc WMc BA WOKW REST DST BLK SG. 
    destruct a as [e|bs]; cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.read_ret] in *.
    -
      destruct RES as (DST2 & ERR2 & He).
      pose proof BA2 as (ST3 & MI3 & ES3 & AUX3 & SSP3 & LXS3 & IMG3). unfold LO in ST3.
      pose proof LXS3 as (G1 & G2).
      pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
      destruct (argv_cstring sp0 argv envp uid m2 IMG3 GEOM 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
        as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). pose proof (str_base_lo sp0 argv envp GEOM) as SBL1. unfold argc, envc in SBL1.
      pose proof IMGB_bound as IL.
      rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
      assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
      assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
      unfold implM. iprefix.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
      cbn [io_diag io io_S].
      eapply (fprintf_exit (DReadError (map bv_unsigned arg1)));
        [| exact BA2| exact P2| exact EX2| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    - destruct RES as (DST2 & ERR2 & Hbs).
      unfold implM. iprefix.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNT1 LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
        assert (LBS : (1 <= length bs)%nat) by (destruct bs; [exfalso; apply K1; reflexivity| cbn; lia]).
        pose proof DST2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SRC. destruct SRC as [SRC STG2b].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
        pose proof BLK2 as BLKx. rewrite <- ELEN in BLKx. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKx. destruct BLKx as [BLK1 BLKj].
        cbn [cells_size csize Nat.add] in BLKj. replace (length DATA + 0)%nat with (length DATA) in BLKj by lia.
        destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.Str_cpy.rw_cells_CB_split_at usegs m2 (A + Z.of_nat (length DATA)) (Z.to_nat (rd_cap st1 - LEN)) junk (length bs) ltac:(lia) BLKj) as [DSTB RESTB].
        replace (A + Z.of_nat (length DATA)) with (A + LEN) in DSTB, RESTB by lia.
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 bs (firstn (length bs) junk));
            rewrite ?unsigned_lit by lia;
            [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; exact DSTB| lia| exact MI2]. }
        cbv beta. intros ms' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI3 & DSTB' & _).
        rewrite !unsigned_lit in MUd by lia. rewrite !unsigned_lit in DSTB' by lia.
        replace (ret_pc (Z_to_bv 64 0x15b58)) with (Z_to_bv 64 0x15b58) by (symmetry; rpc).
        assert (WOKV : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
        { unfold WOK. constructor; [cbn [fst snd]; lia| constructor]. }
        assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
        { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| | exact P2].
          intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
        assert (ST3 : stk usegs m3 (usp0 - 6144513) (usp0 + -128)).
        { eapply stk_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| pose proof BA2 as (ST2' & _); unfold LO in ST2'; exact ST2'| intros y Hy; cbn; lia]. }
        assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA2| apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| exact MI3| unfold LO; exact ST3]).
        assert (EX3 : EXTRA' m3 s) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKV| exact MUd| exact WMd| reflexivity| exact EX2]).
        assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| exact FR2]).
        assert (ERR3 : rw_cells usegs m3 250716 [C4 errv]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact ERR2|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (BLK1' : rw_cells usegs m3 A [CB (length DATA) DATA]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact BLK1|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (RESTB' : rw_cells usegs m3 (A + LEN + Z.of_nat (length bs)) [CB (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat (skipn (length bs) junk)]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact RESTB|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (SGab : rw_cells usegs m3 RSTAGE [CB (length bs) bs; CB (Z.to_nat CNT - length bs) (skipn (length bs) sjk)]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact DST2|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (SGc : stk usegs m3 (RSTAGE + CNT) (RSTAGE + 65536)).
        { eapply stk_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact REST2|]. intros y Hy. cbn. lia. }
        pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.Str_cpy.rw_cells_CB_join _ _ _ _ _ _ _ BLK1' ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact DSTB')) as BLKab.
        assert (BLK3 : rw_cells usegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs);
                                           CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (skipn (length bs) junk)]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split.
          - replace (length DATA + length bs)%nat with (length DATA + Z.to_nat (Z.of_nat (length bs)))%nat by lia. exact BLKab.
          - cbn [cells_size csize Nat.add]. replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + LEN + Z.of_nat (length bs)) by lia.
            replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact RESTB'. }
        pose proof (stk_release usegs m3 RSTAGE RSTAGE _ (stk_empty usegs m3 RSTAGE ltac:(lia)) SGab ltac:(lia)) as SGlo3.
        cbn [cells_size csize Nat.add] in SGlo3.
        replace (RSTAGE + Z.of_nat (length bs + (Z.to_nat CNT - length bs + 0)))%Z with (RSTAGE + CNT)%Z in SGlo3 by lia.
        pose proof (stk_merge usegs m3 RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SGlo3 SGc ltac:(lia)) as SG3.
        clear MUd WMd WOKV SRC STG2b DSTB RESTB REST2 BLK1 BLK1' RESTB' SGc SGab SGlo3 BLKab DSTB' BLK2 DST2.
        zstep. zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
        apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDHEAD. cbn [rd_content rd_cap rd_buf].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        rewrite LEN'.
        do 16 eexists. exists F, fc, m3, A, (DATA ++ bs), (skipn (length bs) junk), errv.
        split; [rewrite ?(Z.add_comm (Z.of_nat (length bs)) LEN); reflexivity|].
        split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
        split; [| split; [exact SG3| split; [exact FR3| split; [exact BA3| split; [exact EX3| split; [exact ERR3| exact FRM]]]]]].
        split; [exact P3|]. split; [exact HA|]. split; [exact BLK3|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR].
      +
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb]. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
        apply implM_ret. apply evt_done.
        cbn [POSTBODY]. unfold RDBRK.
        pose proof (stk_release usegs m2 RSTAGE RSTAGE _ (stk_empty usegs m2 RSTAGE ltac:(lia)) DST2 ltac:(lia)) as SGlo2.
        cbn [cells_size csize Nat.add length] in SGlo2.
        replace (RSTAGE + Z.of_nat (0 + (Z.to_nat CNT - 0 + 0)))%Z with (RSTAGE + CNT)%Z in SGlo2 by lia.
        pose proof (stk_merge usegs m2 RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SGlo2 REST2 ltac:(lia)) as SG3.
        do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, errv.
        split; [rewrite LENZ; reflexivity|].
        split; [exact HC|]. split; [| split; [exact SG3| split; [exact FR2| split; [exact BA2| split; [exact EX2| split; [exact ERR2| exact FRM]]]]]].
        split; [exact P2|]. split; [exact HA|]. split; [exact BLK2|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
  Qed.
End B.
End WithCeiling0.
End Drv_main_B.


Module Drv_main_B2.
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section B2.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis GEOM : launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation RDHEAD' := (RDHEAD sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact CEIL | exact VARGV | exact VENVP | exact GEOM | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) 1 = Some (Z_to_bv 64 P1v) ->
    RDHEAD' fd P1v st s ms ->
    implM usegs (read_loop_body io raw_malloc raw_free ustage fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v) ms.
  Proof.
    intros fd P1v st s ms FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv
                    & -> & HC & BU & SG & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & HA & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    rewrite read_loop_body_eq. unfold rd_grow_part. rewrite LENZ.
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. unfold MFRAME in FR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    unfold implM. iprefix.
    zstep. if_cases K00; zify_cond K00.
    2:{
      replace (Z.of_nat (length DATA) =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
      zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_retb. cbv iota beta.
      rewrite <- LENZ. eapply (rd_read sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11);
        first [hyps | exact FD | exact HP1 | exact HC | exact BU | exact SG | exact BA | exact EX | unfold MFRAME; exact FR | unfold RMallocRep.RERRNO; exact ERR | exact FRM | lia]. }
    replace (Z.of_nat (length DATA) =? rd_cap st) with true by (symmetry; apply Z.eqb_eq; lia).
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_bind_assoc. cbn [io_diag io io_S].
      eapply (fprintf_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FPR FWX SWF DTooBig);
        [| exact BA| exact P0| exact EX| exact FRM| intros ms'' AE; apply implM_retb; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
    apply implM_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := usp0 - 6144513) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P0 | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR1. cbn [Z.add] in ERR1.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
    replace (ret_pc (Z_to_bv 64 0x15b80)) with (Z_to_bv 64 0x15b80) by (symmetry; rpc).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]). unfold MFRAME in FR1.
    assert (SG1 : STG m1) by (eapply (STG_heap sp0); [exact HPR| exact SG]).
    assert (BLK1 : rw_cells usegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (rd_buf st, A, rd_cap st). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    destruct r as [nb|].
    2:{
        destruct RR as [-> HEAP1].
        assert (BA1 : BASE' m1) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA| exact HPR| exact MI1| unfold LO; exact ST1| exact AUX1| exact HEAP1]).
        assert (EX1 : EXTRA m1 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX]).
        clear FR BLK ST MI AUX IMG ES SSP ERR.
        pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS' & IMG). unfold LO in ST.
        pose proof LXS' as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
        unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
        apply implM_bind_assoc. cbn [io_diag io io_S].
        eapply (fwrite_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FWR);
          [exact BA1| exact HEAP1| exact EX1| intros ms'' AE; apply implM_retb; cbv beta iota; apply implM_ret; apply evt_done; exact AE]. }
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & HEXP).
    specialize (HEXP ltac:(apply raddr_exposed_big; unfold MMAP_THRESHOLD; lia)).
    assert (BA1 : BASE' m1) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA| exact HPR| exact MI1| unfold LO; exact ST1| exact AUX1| exact HEAP1]).
    assert (EX1 : EXTRA m1 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX]).
    clear FR BLK ST MI AUX IMG ES SSP ERR SG LXS.
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
    apply implM_bind_assoc.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|]. clear K2.
    zstep. zstep. zstep. zstep.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    eapply evt_cut.
    { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 DATA (firstn (length DATA) junk'));
        rewrite ?unsigned_lit by lia;
        [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1| lia| exact MI]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB1' & _).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in NB1' by lia.
    replace (ret_pc (Z_to_bv 64 0x15b9c)) with (Z_to_bv 64 0x15b9c) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(A', A' + Z.of_nat (length DATA))]).
    { unfold WOK. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P2 : RHEAP s1 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact HEAP1].
      intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA1| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; eapply stk_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ST| intros a Ha; cbn; lia]]).
    assert (EX2 : EXTRA m2 s1) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX1]).
    assert (FR2 : rw_cells usegs m2 (usp0 + -128) [CB 8 PAD; C8 S7; C8 S6; C8 S5; C8 S4; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN); C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact FR1|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (SG2 : STG m2) by (eapply STG_munch; [exact MUc| exact WMc| intros a Ha; cbn; lia| exact SG1]).
    assert (NB2' : rw_cells usegs m2 (A' + Z.of_nat (length DATA + 0)) [CB (Z.to_nat (rd_cap st * 2) - length DATA) (take (Z.to_nat (rd_cap st * 2) - length DATA) (drop (length DATA) junk'))]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact NB2|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (ERR2 : rw_cells usegs m2 250716 [C4 errv1]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ERR1|]. intros a Ha. cbn in Ha |- *. lia. }
    clear MUc WMc BA1 EX1 ST MI ES AUX SSP LXS IMG WOKW NB2 ERR1 SG1.
    pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
    eapply implM_bind.
    { apply implM_leaves. unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 6144513) (B := usp0) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P2 | right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR2 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 [PO LEAF].
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    unfold RATP in ERR3. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR3 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR3. cbn [Z.add] in ERR3.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x15ba4)) with (Z_to_bv 64 0x15ba4) by (symmetry; rpc).
    rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) eq_refl ND) in HPR3, HEAP3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA2| exact HPR3| exact MI3| unfold LO; exact ST3| exact AUX3| exact HEAP3]).
    assert (EX3 : EXTRA m3 s2) by (eapply (EXTRA_heap sp0); [exact HPR3| exact SOE3| exact EX2]).
    assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR3| exact FR2| left; cbn; lia]).
    assert (SG3 : STG m3) by (eapply (STG_heap sp0); [exact HPR3| exact SG2]).
    assert (NB3 : rw_cells usegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply rheap_pres_rw_cells; [exact HPR3| |].
      - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'|].
        cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia. exact NB2'.
      - right; right. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    assert (HA3 : A' = ptr_addr s2 nb).
    { rewrite HEXP. symmetry. apply (rfree_keeps_ptr_proof s1 s2 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2 (rd_buf st) A (rd_cap st) (nb, A', rd_cap st * 2)); [exact P2| right; left; reflexivity| exact LEAF|].
      rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) eq_refl ND). left; reflexivity. }
    clear HPR3 FR1 NB1' NB2' LEAF.
    apply implM_retb. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP GEOM EARGV HT FPR FWX SWF fd P1v (mkRd nb (rd_cap st * 2) (rd_content st)) s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HP1 | exact HC | exact SG3 | exact FR3 | exact BA3 | exact EX3 | unfold RMallocRep.RERRNO; exact ERR3 | exact FRM | lia | idtac].
    split; [exact HEAP3|]. split; [exact HA3|]. split; [exact NB3|].
    assert (CAP2 : rd_cap st * 2 <= 67108864).
    { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR'].
  Qed.

  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => at_exit ps_so 2 s ms
    | RdDone b c => RDBRK' fd P1v b c s ms
    end.

  Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) 1 = Some (Z_to_bv 64 P1v) ->
    RDHEAD' fd P1v st s ms ->
    implM usegs (mloop fuel (read_loop_body io raw_malloc raw_free ustage fd (map bv_unsigned arg1)) st) s (POSTLOOP fd P1v) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1v st s ms FD HP1 RI.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply implM_mono; [apply rd_body; [exact FD| exact HP1| exact RI]|].
      intros [st'|[|b c]] s' ms' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact HP1| exact PO].
      + apply evt_done. exact PO.
      + apply evt_done. exact PO.
  Qed.

End B2.
End WithCeiling0.
End Drv_main_B2.


Module Drv_main_B3.
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Lemma implM_unfold__ : forall {St A : Type} (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment)
  (c : @OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M St A) (s : St)
  (Q : A -> St -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state -> Prop) ms,
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.implM segs c s Q ms ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree.impl segs (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes.at_node segs) (c s)
    (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree.epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros St A segs c s Q ms H. exact H. Qed.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section B3.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis GEOM : launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (img_at sp0 argv envp uid).
  Notation RDHEAD' := (RDHEAD sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTLOOP' := (POSTLOOP sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Definition RDONE (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap P1v fd : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x15bd4 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ EXTRA mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTB (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => at_exit ps_so 2 s ms
    | RdDone b c => RDONE b c s ms
    end.

  Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem),
    FRAME' mm -> BASE' mm -> RHEAP (ps_init (reservedZ usegs)) [] mm -> EXTRA mm (ps_init (reservedZ usegs)) ->
    rw_cells usegs mm RMallocRep.RERRNO [C4 (Z_to_bv 64 0)] -> STG mm -> frm0 fc ->
    implM usegs (read_all io raw_malloc raw_free ustage (map bv_unsigned arg1)) (ps_init (reservedZ usegs)) POSTB
      (MS (mkR (Z_to_bv 64 RMAIN_RET) (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
               (Z_to_bv 64 RMAIN) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 RP1) fc None mm (seg_rom usegs)).
  Proof.
    intros until mm. intros FR BA HP0 EX ERR SG FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE). pose proof (IMGB_bound sp0 argv envp uid VSP VARGV VENVP GEOM) as IL. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. unfold MFRAME in FR.
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    unfold RMAIN_RET, RMAIN, RP1.
    destruct (argv_cstring sp0 argv envp uid mm IMG GEOM 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1). pose proof (str_base_lo sp0 argv envp GEOM) as SBL1. unfold argc, envc in SBL1.
    destruct (stack_pieces sp0 argv envp uid mm IMG GEOM) as (_ & ARGVP & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (STR1' : bytes_at usegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    pose proof SSP as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
    unfold read_all. unfold implM. iprefix.
    pose proof (rd_u64s_g usegs mm (usp0 + 8) (argv_ptrs (ed_top run_draw) argv envp run_execfn ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    remember READ_FUEL as rf eqn:Erf. clear Erf.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm (ps_init (reservedZ usegs)) POSTB msx) end.
    replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').
    eapply implM_bind.
    { eapply implM_of_enode.
      eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.open_spec with (lo := usp0 - 6144513) (errv := Z_to_bv 64 0) (canary := rr_guard);
        [ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
        | rewrite (unsigned_lit P1v) by lia; exact STR1'
        | unfold RATP; rewrite (unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); exact ERR
        | exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | ..].
      all: unfold RATP, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.got_ssp, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.ssp_guard, RMallocRep.RATP; rewrite ?(unsigned_lit 250880) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; cbn [Z.add]; lia. }
    cbv beta. intros r s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
    unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc by (unfold RMallocRep.RATP; lia). rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia).
    unfold RMallocRep.RATP in MUc, ERR1. cbn [Z.add] in MUc, ERR1.
    replace (ret_pc (Z_to_bv 64 0x15b18)) with (Z_to_bv 64 0x15b18) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 112, usp0 + -128); (250716, 250716 + 4)]).
    { unfold WOK, LO, RMallocRep.RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (HP1' : RHEAP (ps_init (reservedZ usegs)) [] m1).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact HP0]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    assert (EX1 : EXTRA m1 (ps_init (reservedZ usegs))) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX]).
    assert (FR1 : rw_cells usegs m1 (usp0 + -128) [CB 8 PAD; C8 S7; C8 S6; C8 S5; C8 S4; C8 (wz (envp_addr sp0 argv)); C8 (wz Driver_iface.RMAIN); C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz Drv_main_defs.RMAIN_RET)]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact FR|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (STR2 : bytes_at usegs m1 P1v (arg1 ++ Z_to_bv 8 0 :: slack1)).
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact STR1|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (SG1 : STG m1) by (eapply STG_munch; [exact MUc| exact WMc| intros a Ha; cbn; lia| exact SG]).
    clear MUc WMc BA WOKW HP0 G1 G2 ST MI ES AUX SSP LXS IMG EX FR STR1 STR1' SG.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    unfold implM. iprefix.
    destruct r as [e|fd]; cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.open_ret OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.open_errno] in *.
    -
      pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; [| exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm (ps_init (reservedZ usegs)) POSTB msx) end.
      cbn [io_diag io io_S].
      eapply (fprintf_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FPR FWX SWF (DCannotOpen (map bv_unsigned arg1)));
        [| exact BA1| exact HP1'| exact EX1| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
      split; [exact STR2|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    -
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
      zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm (ps_init (reservedZ usegs)) POSTB msx) end.
      eapply implM_bind.
      { unfold rmalloc_stmt in MALLOC.
        eapply MALLOC with (lo := usp0 - 6144513) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          unfold RMallocRep.RATP; cbn [Z.add];
          first [ exact HP1' | exact AUX | exact ST | exact ERR1 | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros r s1 ms1 PO.
      destruct PO as (v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      unfold RATP in ERR2. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR2 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR2. cbn [Z.add] in ERR2.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x15b2c)) with (Z_to_bv 64 0x15b2c) by (symmetry; rpc).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR1| left; cbn; lia]).
      assert (SG2 : STG m2) by (eapply (STG_heap sp0); [exact HPR| exact SG1]).
      destruct r as [buf|].
      2:{
          destruct RR as [-> HEAP2].
          assert (BA2 : BASE' m2) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2| exact HEAP2]).
          assert (EX2 : EXTRA m2 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX1]).
          clear FR1 ST MI ES AUX SSP LXS IMG ERR1.
          pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
          pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
          unfold implM. iprefix.
          zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
          zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
          lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s1 POSTB msx) end.
          cbn [io_diag io io_S].
          eapply (fwrite_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FWR);
            [exact BA2| exact HEAP2| exact EX2| intros ms'' AE; apply implM_ret; apply evt_done; exact AE]. }
      destruct RR as (A & junk & -> & BR & HEAP2 & BLK & HEXP).
      specialize (HEXP ltac:(apply raddr_exposed_init; reflexivity)).
      assert (BA2 : BASE' m2) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2| exact HEAP2]).
      assert (EX2 : EXTRA m2 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX1]).
      clear FR1 ST MI ES AUX SSP LXS IMG ERR1 SG1.
      pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      unfold implM. iprefix.
      zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
      zstep. zstep. zstep. zstep. zstep. if_true. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s1 POSTB msx) end.
      destruct rf as [|rf]; [eapply (@implM_bind _ _ _ _ _ _ _ (fun _ _ _ => False)); [cbn [mloop]; apply implM_unr| intros ? ? ? []]|].
      eapply implM_bind.
      { apply implM_loop_S. rewrite read_loop_body_eq. unfold rd_grow_part. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
        replace (0 =? 65536) with false by reflexivity. apply implM_retb. cbv beta iota.
        eapply implM_mono.
        - change 0 with (zlength (rd_content (mkRd buf 65536 []))).
          eapply (rd_read sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP GEOM EARGV HT FPR FWX SWF fd P1v (mkRd buf 65536 []) s1)
            with (A := A) (DATA := []) (junk := junk) (errv := errv2);
            cbn [rd_content rd_cap rd_buf zlength length Z.of_nat]; first [lia | exact HP1 | reflexivity | exact SG2 | exact FR2 | exact BA2 | exact EX2 | exact ERR2 | exact FRM | idtac].
          split; [exact HEAP2|]. split; [exact HEXP|]. cbn [length Z.of_nat Z.sub].
          split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
          + apply rw_cells_CB0. lia.
          + unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR].
        - intros [st'|[|b c]] s3 ms3 PO; cbn [POSTBODY POSTLOOP] in PO |- *.
          + apply (rd_loop sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP GEOM EARGV HT MALLOC FREE FPR FWX SWF FWR rf fd P1v); [lia| exact HP1| exact PO].
          + apply evt_done. exact PO.
          + apply evt_done. exact PO. }
      cbv beta. intros res s2 ms2 PO.
      destruct res as [|b c]; cbn [POSTLOOP] in PO.
      { apply implM_ret. apply evt_done. exact PO. }
      clear dependent m2.
      destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x23 & w3 & w4 & w5 & w6 & F2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3 & errv3
                      & -> & HC3 & BU3 & SG3 & FR3 & BA3 & EX3 & ERR3 & FRM3).
      pose proof BA3 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR3. unfold MFRAME in FR3.
      pose proof BU3 as (P3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3).
      pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
      unfold implM. iprefix. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s2 POSTB msx) end.
      eapply implM_bind.
      { eapply implM_of_enode.
        eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.close_spec with (lo := usp0 - 6144513) (errv := errv3); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          unfold RMallocRep.RATP; cbn [Z.add];
          first [ exact ST | exact ERR3 | exact MI | lia ]. }
      cbv beta. intros r3 s3 ms3 [PO ->].
      destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
      unfold RATP in MUc, ERR4. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc by (unfold RMallocRep.RATP; lia). rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR4 by (unfold RMallocRep.RATP; lia).
      unfold RMallocRep.RATP in MUc, ERR4. cbn [Z.add] in MUc, ERR4.
      replace (ret_pc (Z_to_bv 64 0x15bd4)) with (Z_to_bv 64 0x15bd4) by (symmetry; rpc).
      assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 32, usp0 + -128); (250716, 250716 + 4)]).
      { unfold WOK, LO, RMallocRep.RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (P4 : RHEAP s2 [(b, A3, cap3)] m4).
      { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact P3]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
      assert (BA4 : BASE' m4) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA3| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; exact ST4]).
      assert (EX4 : EXTRA m4 s2) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX3]).
      assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact FR3]).
      assert (BLK4 : rw_cells usegs m4 A3 [CB (length DATA3) DATA3; CB (Z.to_nat (cap3 - Z.of_nat (length DATA3))) junk3]).
      { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact BLK3|]. intros a Ha. cbn in Ha |- *. lia. }
      apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
      do 17 eexists. exists F2, fc2, m4, A3, cap3, P1v, fd, DATA3. exists junk3, (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit.Drv_sys.close_errno r3 errv3).
      split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact FR4| split; [exact BA4| split; [exact EX4| split; [exact ERR4| exact FRM3]]]]].
      split; [exact P4|]. split; [exact HA3|]. split; [exact BLK4|]. split; [exact CAP3|]. split; [exact LEN3| exact BRR3].
  Qed.
End B3.
End WithCeiling0.
End Drv_main_B3.


Module Drv_main_C.
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
Lemma signed_byte : forall b : byte, bv_signed b = sx8 (bv_unsigned b).
Proof.
  intros b. pose proof (byte_range b) as R. unfold bv_signed, sx8. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small; lia.
  - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

Lemma list6 : forall (l : list byte), (6 <= length l)%nat -> exists d0 d1 d2 d3 d4 d5 r, l = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: r.
Proof.
  intros l H. destruct l as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 r]]]]]]; cbn in H; try lia. do 7 eexists. reflexivity.
Qed.
Lemma skipn4 : forall (l : list byte) n, (n + 4 <= length l)%nat -> exists q0 q1 q2 q3 r, skipn n l = q0 :: q1 :: q2 :: q3 :: r.
Proof.
  intros l n H. pose proof (length_skipn n l) as L.
  destruct (skipn n l) as [|q0 [|q1 [|q2 [|q3 r]]]]; cbn in L; try lia. do 5 eexists. reflexivity.
Qed.
Lemma land15_mod : forall x, Z.land x 32767 = x mod 32768.
Proof. intros. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_shiftl_small : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.land (Z.shiftl b k) a = 0.
Proof.
  intros a b k Hk Ha. rewrite Z.shiftl_mul_pow2 by lia.
  replace a with (Z.land a (Z.ones k)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite (Z.land_comm a), Z.land_assoc, Z.land_ones by lia. rewrite Z_mod_mult. apply Z.land_0_l.
Qed.
Lemma lor_shiftl_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (Z.shiftl b k) a = a + b * 2^k.
Proof.
  intros a b k Hk Ha. rewrite <- Z.lxor_lor by (apply land_shiftl_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small; lia). rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lor_mul_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (b * 2^k) a = a + b * 2^k.
Proof. intros a b k Hk Ha. rewrite <- Z.shiftl_mul_pow2 by lia. rewrite lor_shiftl_add by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma le16_cons : forall d0 d1 (r : list byte), le16 (map bv_unsigned (d0 :: d1 :: r)) = bv_unsigned d0 + bv_unsigned d1 * 256.
Proof. intros. reflexivity. Qed.
Lemma znth2_cons : forall d0 d1 d2 (r : list byte), znth (map bv_unsigned (d0 :: d1 :: d2 :: r)) 2 = bv_unsigned d2.
Proof. intros. reflexivity. Qed.
Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
  intros c0 c1 H0 H1. rewrite Z.testbit_eqb by lia. change (2 ^ 15) with 32768.
  replace ((c0 + c1 * 256) / 32768) with (c1 / 128) by (Z.div_mod_to_equations; nia).
  destruct (Z.leb_spec 128 c1).
  - replace (c1 / 128) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - replace (c1 / 128) with 0 by (Z.div_mod_to_equations; nia). reflexivity.
Qed.

Lemma cfg15_Z : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
  Z.lor (Z.shiftr (Z.land (Z.shiftl ((sx8 u1) mod 2^64) 57) 18446744073709551615) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
  intros u0 u1 H0 H1.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite land15_mod.
  assert (E : (sx8 u1 mod 2 ^ 64 * 2 ^ 57) mod 2 ^ 64 / 2 ^ 49 = (u1 mod 128) * 2^8).
  { unfold sx8. destruct (Z.ltb_spec u1 128).
    - rewrite (Z.mod_small u1) by lia. rewrite (Z.mod_small u1) by lia.
      rewrite Z.mod_small by (split; [lia|]; change (2^64) with (2^7 * 2^57); apply Z.mul_lt_mono_pos_r; lia).
      change (2^57) with (2^49 * 2^8). rewrite Z.mul_assoc, (Z.mul_comm u1), <- Z.mul_assoc. rewrite Z.mul_comm.
      rewrite Z.div_mul by lia. lia.
    - replace ((u1 - 256) mod 2^64) with (2^64 - 256 + u1) by (Z.div_mod_to_equations; nia).
      replace ((2 ^ 64 - 256 + u1) * 2 ^ 57) with ((u1 - 128) * 2^57 + (2^57 - 1) * 2^64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
      replace (u1 mod 128) with (u1 - 128) by (Z.div_mod_to_equations; lia).
      change (2^57) with (2^8 * 2^49). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E. rewrite lor_mul_add by lia. Z.div_mod_to_equations. lia.
Qed.

Section C.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (img_at sp0 argv envp uid).
  Notation RDONE' := (RDONE sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition RQEXIT (code : Z) (s : PState) : machine_state -> Prop := at_exit ps_so code s.

  Definition main_tail (buf : bptr) (cw cfg : Z) (payload : list Z) : M PState Z :=
    status <- run cfg payload ;;
    status' <- (if Z.testbit cw 15 then
                  n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                else mret status) ;;
    raw_free buf ;;;
    mret status'.

  Definition main_rest (buf : bptr) (content : list Z) : M PState Z :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag io DShortHdr ;;; raw_free buf ;;; mret 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag io DCfgOverrun ;;; raw_free buf ;;; mret 2
      else
        let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
        let payload := skipn (Z.to_nat (6 + config_len)) content in
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        alloc_init bitmap ;;; main_tail buf cfg_word cfg payload.

  Lemma main_model_eq : main_model io raw_malloc raw_free ustage alloc_init run alloc_count (argv_Z argv)
    = (ra <- read_all io raw_malloc raw_free ustage (map bv_unsigned arg1) ;;
       match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end).
  Proof. unfold main_model, argv_Z. rewrite EARGV. reflexivity. Qed.

  Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
    6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ rblock_range A cap
    /\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  Definition RUN0 (bufp : bptr) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (junk : list byte) (errv : word),
      ms = GST 0x15c38 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw L cfg sc
      /\ RHEAP s [(bufp, A, cap)] mm
      /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ FRAME' mm /\ BASE' mm /\ EXTRA mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= code < 2^64 ->
    FRAME' mm -> stk usegs mm LO' (usp0 + -128) ->
    ESTAT TID mm -> RHEAP s LB mm -> stdout_file mm (ps_so s) -> stderr_file mm -> mem_inv usegs mm -> rdrv_statics mm ->
    evt usegs (at_exit ps_so code s)
      (GST 0x15cd4 x1 t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros CR FR ST ES HP SOF SEF MI ATX. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold MFRAME in FR.
    unfold Drv_main_defs.RMAIN_RET, RMAIN in FR. cbv delta [MallocRep.wz] in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x22dd8)) with (Z_to_bv 64 0x22dd8) by (symmetry; rpc).
    zstep.
    replace (ret_pc (Z_to_bv 64 0x22ddc)) with (Z_to_bv 64 0x22ddc) by (symmetry; rpc).
    apply evt_done. eapply (at_exit_intro TID HT code s LB); [exact ST| lia| lia| lia| exact ES| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.

  Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    s_diag (St:=PState) d = stderr_fwrite msg -> ro_bytes_b usegs PA (to_bytes msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x2b000 ->
    RHEAP s [(bufp, A, cap)] mm -> EXTRA mm s -> FRAME' mm -> BASE' mm -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] ->
    implM usegs (s_diag d ;;; raw_free bufp ;;; mret 2) s RQEXIT
      (GST 0x15cc8 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros ED RO ML RNG LOA HIA P0 EX FR BA ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof EX as (SOF & SE & FL & IB).
    pose proof (RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    rewrite ED.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 6144513) (canary := rr_guard) (s := msg);
        [exact SE| rewrite unsigned_lit by lia; change (map _ msg) with (to_bytes msg); apply rodata_bytes; [exact MI| exact RO| lia| lia]
        | exact RNG | rewrite ML; lia| rewrite ML; reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite !unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; lia
        | exact SSP| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & SEW & SSP1 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x15ccc)) with (Z_to_bv 64 0x15ccc) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 6144513, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    assert (P1 : RHEAP s [(bufp, A, cap)] m1).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (EX1 : EXTRA m1 s) by (eapply (EXTRA_stdio sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact SEW| exact EX]).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact FR0]).
    assert (ERR1 : rw_cells usegs m1 250716 [C4 errv]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ERR|]. intros a Ha. cbn in Ha |- *. lia. }
    clear MUc WMc ST MI ES AUX SSP LXS IMG.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 6144513) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P1 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR1 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x15cd4)) with (Z_to_bv 64 0x15cd4) by (symmetry; rpc).
    rewrite (lb_remove_head bufp A cap [] ltac:(cbn; constructor; [intros []| constructor])) in HEAP3, HPR3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR3| exact MI3| unfold LO; exact ST3| exact AUX3| exact HEAP3]).
    assert (EX3 : EXTRA m3 s2) by (eapply (EXTRA_heap sp0); [exact HPR3| exact SOE3| exact EX1]).
    pose proof BA3 as (ST4 & MI4 & ES4 & _). pose proof EX3 as (SOF4 & SE4 & _ & IB4).
    apply implM_ret. unfold RQEXIT.
    eapply (main_return 2 s2 []); [lia| eapply (MFRAME_heap sp0 argv); [exact HPR3| exact FR1]| exact ST4| exact ES4| exact HEAP3| exact SOF4| apply stderr_wfile0_file; exact SE4| exact MI4| exact IB4].
  Qed.

  Lemma phaseC : forall bufp content s ms,
    RDONE' bufp content s ms ->
    (forall DATA A cap cw L cfg sc s1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw L cfg sc s1 ms1 ->
       implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) content)) s1 RQEXIT ms1) ->
    implM usegs (main_rest bufp content) s RQEXIT ms.
  Proof.
    intros bufp content s ms RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & P1v & fd & DATA & junk & errv
                    & -> & HC & BU & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. pose proof ERR as ERR0. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof BU as (P0 & HA & BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_rest. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
    unfold implM. iprefix. zstep. zstep. if_cases K0; zify_cond K0.
    {
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io io_S].
      eapply (diagC_exit DShortHdr s_short S_SHORT); [reflexivity| apply s_short_ro| reflexivity| apply lit_range
        | unfold S_SHORT; lia| unfold S_SHORT; lia| exact P0| exact EX| exact FR0| exact BA| exact ERR0]. }
    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read usegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as L eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io io_S].
      eapply (diagC_exit DCfgOverrun s_over S_OVER); [reflexivity| apply s_over_ro| reflexivity| apply lit_range
        | unfold S_OVER; lia| unfold S_OVER; lia| exact P0| exact EX| exact FR0| exact BA| exact ERR0]. }
    replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.
    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + L)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at usegs mm (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + L) in X by (cbn [length] in *; lia). exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read usegs mm _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x15c38)) with (Z_to_bv 64 0x15c38) by (symmetry; rpc).
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    unfold alloc_init. apply implM_retb.
    replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 20 eexists. exists junk, errv. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? L); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [exact P0|]. split; [rewrite HnD in BLK; exact BLK|]. split; [exact FR0|]. split; [exact BA|]. split; [exact EX|]. split; [exact ERR0| exact FRM].
  Qed.
End C.
End WithCeiling0.
End Drv_main_C.


Module Drv_main_D.
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Layout Exit Startup Stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Drv_facts Drv_main_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section D.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TRUN : rtarget_run_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (img_at sp0 argv envp uid).
  Notation RUN0' := (RUN0 sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RQEXIT := (Drv_main_C.RQEXIT).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition BASE2 (mm : mem) : Prop :=
    stk usegs mm LO' (usp0 + -128) /\ mem_inv usegs mm /\ ESTAT TID mm /\ rauxv_ok mm usp0 /\ stderr_wfile mm
    /\ rdrv_statics mm.

  Lemma free_return : forall (code : Z) (s : PState) (LK : list block) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    0 <= code < 2^64 ->
    RHEAP s (LK ++ [(bufp, A, cap)]) mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] ->
    implM usegs (raw_free bufp ;;; mret code) s RQEXIT
      (GST 0x15ccc x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros CR P0 FR (ST & MI & ES & AUX & SE & ATX) SOF ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(apply in_or_app; right; left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 6144513) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P0 | apply in_or_app; right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x15cd4)) with (Z_to_bv 64 0x15cd4) by (symmetry; rpc).
    pose proof (agree_of_heap_pres _ _ _ _ HPR3) as AG.
    apply implM_ret. unfold Drv_main_C.RQEXIT.
    eapply (main_return sp0 argv TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL HT code s2 (lb_remove bufp (LK ++ [(bufp, A, cap)]))); [lia| eapply (MFRAME_heap sp0 argv); [exact HPR3| exact FR0]| unfold LO; exact ST3| | exact HEAP3| | | exact MI3| ].
    - eapply (ESTAT_agree TID _ _ _ AG); [| exact ES]. intros a Ha. right; left.
      unfold estat_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    - rewrite SOE3. eapply stdout_file_agree; [exact AG| | exact SOF]. intros a Ha. right; left.
      unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    - apply stderr_wfile_file. eapply stderr_wfile_agree; [exact AG| | exact SE]. intros a Ha. right; left.
      unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    - eapply rdrv_statics_agree; [exact AG| | exact ATX]. intros a Ha. right; left.
      unfold drv_addr, RINIT_FLAG, RATX_FIN, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
  Qed.

  Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv
                    & -> & HD & P0 & BLK & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. pose proof ERR as ERR0. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof EX as (SOF & SE & FL & IB).
    pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GOT).
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rtarget_run_stmt, RTARGET_RUN in TRUN.
      eapply TRUN with (lo := usp0 - 6144513) (B := usp0) (p := bufp) (cap := cap) (errv := errv);
        rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      - exact P0.
      - left; reflexivity.
      - unfold to_bytes. rewrite zbytes_map_unsigned'. exact BLKB.
      - apply map_unsigned_range.
      - unfold zlength. rewrite length_map. lia.
      - lia.
      - lia.
      - unfold zlength. rewrite length_map. lia.
      - exact LXS.
      - exact FL.
      - exact SE.
      - exact SSP.
      - exact SOF.
      - exact IB.
      - exact GOT.
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold GLOBALS_TOP. lia.
      - unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK. lia.
      - unfold RATP. cbv delta [MallocRep.wz]. rewrite (unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP. cbn [Z.add]. exact ERR.
      - reflexivity.
      - exact MI.
      - exact FRM.
      - lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - cbv delta [MallocRep.wz]. f_equal. unfold zlength. rewrite length_map. lia. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & [LK1 P1] & LXS1 & FL1 & SE1 & SSP1 & SOF1 & IB1 & DP).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. cbv delta [MallocRep.wz] in ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR1. cbn [Z.add] in ERR1.
    cbv delta [MallocRep.wz].
    replace (ret_pc (Z_to_bv 64 0x15c4c)) with (Z_to_bv 64 0x15c4c) by (symmetry; rpc).
    pose proof (agree_of_drv_pres _ _ _ _ DP) as AG.
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. cbn in Ha. apply stack_client; [lia|].
      unfold DRVW, LXW_ZH, LXW_STDERR, ZH_STATICS, LX_STDERR_FILE, RINIT_FLAG, RATX_FIN. cbn. lia. }
    assert (ES1 : ESTAT TID m1).
    { eapply (ESTAT_agree TID _ _ _ AG); [| exact ES]. intros a Ha. split.
      - unfold DRVW, LXW_ZH, LXW_STDERR, ZH_STATICS, LX_STDERR_FILE, RINIT_FLAG, RATX_FIN. cbn. unfold estat_addr in Ha. lia.
      - right; right. unfold estat_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    assert (BA2 : BASE2 m1) by (split; [unfold LO; exact ST1| split; [exact MI1| split; [exact ES1| split; [exact AUX1| split; [exact SE1| exact (rdrv_statics_of _ _ IB1)]]]]]).
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    -
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      zstep. zstep. zstep.
      replace (ret_pc (Z_to_bv 64 0x15c5c)) with (Z_to_bv 64 0x15c5c) by (symmetry; rpc).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      apply implM_bind_assoc. unfold alloc_count. apply implM_retb. apply implM_retb. unfold COUNT_MAX. cbn [Z.ltb].
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      eapply free_return; [lia| exact P1| exact FR1| exact BA2| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1].
    -
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 RQEXIT msx) end.
      eapply free_return; [lia| exact P1| exact FR1| exact BA2| exact SOF1| unfold RMallocRep.RERRNO; exact ERR1].
  Qed.
End D.
End WithCeiling0.
End Drv_main_D.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Startup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_facts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_main.Drv_main_D.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_example_small_fuzzer_ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Main.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TRUN : rtarget_run_stmt.

  Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) ms,
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp ->
    (* the launch's geometry, handed on from rmain_stmt *)
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    argv = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 sp0 argv envp uid TID ms ->
    implM usegs (ra <- read_all io raw_malloc raw_free ustage (map bv_unsigned arg1) ;;
                 match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
          (ps_init (reservedZ usegs)) (fun code s' ms' => at_exit ps_so code s' ms') ms.
  Proof.
    intros sp0 argv envp uid arg0 arg1 TID ms VSP CEIL VARGV VENVP GEOM EARGV HT HP1.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & mm & pad
                     & -> & FR & BA & HP & ERR & SOF & SE & FL & IFL & SG).
    eapply implM_bind.
    { eapply (main_read_all sp0 argv envp uid arg0 arg1 TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV VENVP GEOM EARGV HT MALLOC FREE FPR FWX SWF FWR);
        [exact FR| exact BA| exact HP| | | exact SG| ].
      - split; [exact SOF|]. split; [exact SE|]. split; [exact FL| exact IFL].
      - unfold RATP in ERR. cbv delta [MallocRep.wz] in ERR. unfold errno_addr in ERR. rewrite (unsigned_lit RMallocRep.RATP) in ERR by (unfold RMallocRep.RATP; lia).
        unfold RMallocRep.RERRNO. unfold RMallocRep.RATP in ERR. cbn [Z.add] in ERR. exact ERR.
      - reflexivity. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implM_ret. apply evt_done. exact PB.
    - eapply (phaseC sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE FWR); [exact PB|].
      intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
      exact (phaseDE sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
  Qed.

  Theorem main_proof : rmain_stmt.
  Proof.
    unfold rmain_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS GEOM AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{ unfold main_model. replace (Z.of_nat (length (argv_Z argv)) =? 2) with false by (symmetry; apply Z.eqb_neq; unfold argv_Z; rewrite length_map; exact NE2). cbn [negb].
        exact (main_usage_proof FPR FWX SWF sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS GEOM NE2 AM). }
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    rewrite (main_model_eq argv arg0 arg1 EARGV).
    destruct (main_to_P1_proof sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS GEOM ltac:(rewrite EARGV; reflexivity) AM) as (TID & HT & EV).
    eapply implM_evt; [exact EV|]. cbv beta. intros ms' HP1.
    exact (main_from_P1 sp0 argv envp uid arg0 arg1 TID ms' VSP CEIL VARGV VENVP GEOM EARGV HT HP1).
  Qed.
End Main.
End WithCeiling0.
