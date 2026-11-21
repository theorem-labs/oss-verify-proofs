(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the input's kernel build and exec file name; the start-up facts stated over the launch's ProcInput; the larger auxiliary vector and its CONFIG_RSEQ entries; the write-certified stack window); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue InitMem Layout Exit Startup Printf_lib Printf_stdio_iface Fz_iface Driver_iface Drv_kit Drv_main_defs.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Exit_walk.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Exit_ax.     (* [comment removed for export] *)
From OSSVerify.openssl.pem.images Require Import Plain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Plain.M.phdrs.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.  (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call psegs m mm MU WM end end.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Variables (sp : word) (inp : ProcInput) (mbase : word) (m : mem).
  Notation usp := (bv_unsigned sp).
  (* LPS 08b1429: the entry stack is [entry_stack_image]; the launch places its strings below the
     stack top ([InitMem.launch_hsp]) *)
  Hypothesis IMGH : bytes_at psegs m usp (entry_stack_image inp mbase pph PENTRY sp run_draw)
                    /\ (usp + InitMem.head_size inp <= bv_unsigned (ed_top run_draw) - 8 - InitMem.str_len inp)%Z.

  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc inp))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs inp run_draw ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc inp + 2)) (u64s (envp_ptrs inp run_draw ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc inp + envc inp + 3)) (u64s (auxv_words inp mbase pph PENTRY sp run_draw)) /\
    bytes_at psegs m (str_base inp run_draw) (flatten_strings (in_argv inp)) /\
    bytes_at psegs m (env_base inp run_draw) (flatten_strings (in_envp inp)) /\
    bytes_at psegs m (rnd_addr inp sp) (at_random_bytes (ed_random run_draw)).
  Proof. exact (image_pieces psegs inp mbase pph PENTRY sp run_draw (proj2 IMGH) m (proj1 IMGH)). Qed.

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error (in_argv inp) i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs inp run_draw) i = Some (Z_to_bv 64 p) /\ str_base inp run_draw <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (entry_stack_image inp mbase pph PENTRY sp run_draw)) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn _. exact (image_argv_string psegs inp mbase pph PENTRY sp run_draw (proj2 IMGH) m (proj1 IMGH) i s Hn).
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithCeiling0.
Ltac img_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside crt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
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
Lemma find_seg3__ : forall a, (0x2d7000 <= a < 0x30d000)%Z -> find_segment psegs a 1 = Some Plain_segment_003.
Proof.
  intros a Ha. unfold Image.psegs, Plain.M.loaded_segments, Plain_loaded_segments.
  cbn [find_segment seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003 Z.of_N].
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  try reflexivity;
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H : (_ && _)%bool = false |- _ => apply andb_false_iff in H; destruct H
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
  end; lia.
Qed.


(* LPS 08b1429: the whole auxv, as [StackLayout.auxv_entries] writes it, is what
   [MallocTree.auxv_list] names: 24 fixed pairs, AT_RANDOM, AT_EXECFN, the two rseq pairs when
   [la_rseq] is set, then AT_NULL.  musl's [getauxval(AT_RANDOM)] walks it to the terminator,
   which is why the rseq pairs have to be in the list and not in an unconstrained tail. *)
Lemma auxv_words_prefix : forall inp mbase ph entry sp draw,
  exists V ex, auxv_words inp mbase ph entry sp draw
               = auxv_list V (rnd_addr inp sp) ex (la_rseq (launch_auxv inp sp mbase)).
Proof.
  intros inp mbase ph entry sp draw. set (la := launch_auxv inp sp mbase). set (c := la_cache la).
  exists (mkAuxv (bv_unsigned (la_sysinfo_ehdr la))
           (bv_unsigned (cw_l1i_size c))
           (bv_unsigned (cw_l1i_geom c))
           (bv_unsigned (cw_l1d_size c))
           (bv_unsigned (cw_l1d_geom c))
           (bv_unsigned (cw_l2_size c))
           (bv_unsigned (cw_l2_geom c))
           (bv_unsigned (cw_l3_size c))
           (bv_unsigned (cw_l3_geom c))
           (bv_unsigned (la_minsigstksz la))
           (bv_unsigned (in_hwcap inp))
           (4096)
           (100)
           (Z.of_N (ph_addr ph))
           (Z.of_N (ph_ent ph))
           (Z.of_N (ph_num ph))
           (0)
           (0)
           (bv_unsigned entry)
           (bv_unsigned (in_uid inp))
           (bv_unsigned (in_uid inp))
           (bv_unsigned (in_gid inp))
           (bv_unsigned (in_gid inp))
           (0)).
  eexists. unfold auxv_words, auxv_entries, auxv_list. fold la. fold c.
  (* the two rseq pairs are in the vector exactly when [la_rseq] is set *)
  destruct (la_rseq la);
    cbn [flat_map fst snd app map ax_sysinfo ax_l1i ax_l1ig ax_l1d ax_l1dg ax_l2 ax_l2g ax_l3 ax_l3g ax_minsig ax_hwcap
         ax_pagesz ax_clktck ax_phdr ax_phent ax_phnum ax_base ax_flags ax_entry ax_uid ax_euid ax_gid ax_egid ax_secure];
    (* the model writes the keys as named constants; they are the same literals *)
    cbv [AT_NULL AT_PHDR AT_PHENT AT_PHNUM AT_PAGESZ AT_BASE AT_FLAGS AT_ENTRY AT_UID AT_EUID AT_GID AT_EGID AT_HWCAP AT_CLKTCK AT_SECURE AT_RANDOM AT_EXECFN AT_RSEQ_FEATURE_SIZE AT_RSEQ_ALIGN AT_SYSINFO_EHDR AT_L1I_CACHESIZE AT_L1I_CACHEGEOMETRY AT_L1D_CACHESIZE AT_L1D_CACHEGEOMETRY AT_L2_CACHESIZE AT_L2_CACHEGEOMETRY AT_L3_CACHESIZE AT_L3_CACHEGEOMETRY AT_MINSIGSTKSZ];
    unfold MallocRep.wz; rewrite !Z_to_bv_bv_unsigned; reflexivity.
Qed.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section InitFacts.
  Variables (sp0 : word) (inp : ProcInput) (mbase : word) (m : mem).
  Hypothesis NONE : forall a : word, (0x27a000 <= bv_unsigned a < 0x30d000)%Z -> outside (crt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0x30b458 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0x30b460 [C8 (Z_to_bv 64 (auxv_addr inp sp0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0x2d6e70 [C8 (Z_to_bv 64 0x30b208)].
  Hypothesis GUARD : rw_cells psegs m 0x30b208 [C8 rr_guard].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMGH : bytes_at psegs m (bv_unsigned sp0) (entry_stack_image inp mbase pph PENTRY sp0 run_draw)
                    /\ (bv_unsigned sp0 + InitMem.head_size inp <= bv_unsigned (ed_top run_draw) - 8 - InitMem.str_len inp)%Z.
  Hypothesis SPLO : sp_window_lo <= bv_unsigned sp0.
  Hypothesis CEIL : ceil_ok sp0.     (* [comment removed for export] *)

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs)) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr inp sp0))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    intros a Ha. apply NONE; [lia|]. unfold crt_written. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rauxv_ok_init : rauxv_ok m (bv_unsigned sp0).
  Proof.
    destruct (stack_pieces sp0 inp mbase m IMGH) as (_ & _ & _ & AUXW & _ & _ & RND).
    destruct (auxv_words_prefix inp mbase pph PENTRY sp0 run_draw) as (V & ex & EW).
    rewrite EW in AUXW.
    pose proof (proj2 IMGH) as HSP. unfold sp_window_lo in SPLO.
    pose proof (head_size_eq inp mbase pph PENTRY sp0 run_draw) as HE.
    rewrite (length_auxv_words inp mbase pph PENTRY sp0 run_draw) in HE.
    pose proof (u64_range (ed_top run_draw)) as TR.
    assert (AC : (2 * auxv_count (kb_rseq (in_kernel inp)) >= 54)%nat) by (unfold auxv_count; destruct (kb_rseq _); lia).
    exists (auxv_addr inp sp0), V, (rnd_addr inp sp0), ex, (la_rseq (launch_auxv inp sp0 mbase)).
    split; [apply (proj2 heap_init)|].
    split; [exact AUXW|].
    split. { (* [comment removed for export] *)
             rewrite at_random_bytes_split in RND. apply bytes_at_app in RND.
             destruct RND as [_ R]. exact R. }
    unfold ceil_ok in CEIL.
    unfold auxv_addr, rnd_addr, sp_window_lo, stack_max_size, InitMem.str_len, auxv_vec_bytes in *;
      try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (Nat2Z.is_nonneg (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
    unfold argc, envc in *.
    (* LPS 08b1429: the vector's length is [auxv_count (kb_rseq ...)]; the witness's flag
       [la_rseq (launch_auxv inp sp mbase)] is that same flag, so align them before counting. *)
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
    destruct (kb_rseq (in_kernel inp)); unfold auxv_count in *; cbn iota in *; repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stderr_init : rw_cells psegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x30b8a0 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)).
  Proof.
    unfold file_cells.
    img_chunk0 NONE m 0x2d8310 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x30b8a0 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)) H.
    unfold file_cells in H. exact H.
  Qed.
  Lemma stderr_wfile0_init : stderr_wfile0 m.
  Proof.
    exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (zeros 80). split; [apply stderr_init|].
    split; [vm_compute; reflexivity|]. split; [left; reflexivity| lia].
  Qed.
  Lemma stderr_wfile_init : stderr_wfile m.
  Proof. apply stderr_wfile0_wfile, stderr_wfile0_init. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma malloc_impl_init : rw_cells psegs m LX_STORAGE_FN [C8 (wz FZ_CRYPTO_MALLOC)].
  Proof. unfold LX_STORAGE_FN, FZ_CRYPTO_MALLOC. img_chunk0 NONE m 0x2d7ee0 [C8 (wz 0xe1d70)] H. exact H. Qed.
  Lemma free_impl_init : rw_cells psegs m (LX_STORAGE_FN + 16) [C8 (wz FZ_CRYPTO_FREE)].
  Proof. unfold LX_STORAGE_FN, FZ_CRYPTO_FREE. img_chunk0 NONE m 0x2d7ef0 [C8 (wz 0xe2104)] H. exact H. Qed.
  Lemma got_free_init : rw_cells psegs m (LX_GOT_FLAGS + 16) [C8 (wz FZ_CRYPTO_FREE)].
  Proof. unfold LX_GOT_FLAGS, FZ_CRYPTO_FREE. img_chunk0 NONE m 0x2d6a90 [C8 (wz 0xe2104)] H. exact H. Qed.
  Lemma flags_init : lx_flags m (wz 0).
  Proof. unfold lx_flags, LX_FLAGS. exists (Z_to_bv 8 0). img_chunk0 NONE m 0x2e8870 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  Lemma base_inited0_init : rw_cells psegs m 0x2e8680 [C1 (Z_to_bv 8 0)].     (* [comment removed for export] *)
  Proof. img_chunk0 NONE m 0x2e8680 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  Lemma base_inited_init : rw_cells psegs m 0x2e8684 [C1 (Z_to_bv 8 0)].      (* [comment removed for export] *)
  Proof. img_chunk0 NONE m 0x2e8684 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  Lemma stdin_init : stdin_file m.
  Proof.
    exists (map (Z_to_bv 8) [9; 0; 0; 0; 0; 0; 0; 0]%Z), (map (Z_to_bv 8) [20; 223; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z), (map (Z_to_bv 8) [0; 0; 0; 0; 0; 0; 0; 0]%Z), (map (Z_to_bv 8) [64; 223; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 88; 224; 38; 0; 0; 0; 0; 0; 168; 184; 48; 0; 0; 0; 0; 0; 0; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z), (map (Z_to_bv 8) [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z).
    img_chunk0 NONE m 0x2d8400 [CB 8 (map (Z_to_bv 8) [9; 0; 0; 0; 0; 0; 0; 0]%Z); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (map (Z_to_bv 8) [20; 223; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z); C8 (Z_to_bv 64 0);
                                CB 8 (map (Z_to_bv 8) [0; 0; 0; 0; 0; 0; 0; 0]%Z); C8 (Z_to_bv 64 0); CB 76 (map (Z_to_bv 8) [64; 223; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 88; 224; 38; 0; 0; 0; 0; 0; 168; 184; 48; 0; 0; 0; 0; 0; 0; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z); C4 (Z_to_bv 64 0xffffffff);
                                CB 88 (map (Z_to_bv 8) [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z)] H. exact H.
  Qed.
  Lemma initflag_init : rw_cells psegs m RINIT_FLAG [C1 (Z_to_bv 8 0)].
  Proof. unfold RINIT_FLAG. img_chunk0 NONE m 0x2e8650 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  (* [comment removed for export] *)
  Lemma axstat_init : AXSTAT false m.
  Proof.
    unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells. cbn [Z.add].
    split; [| split].
    - img_chunk0 NONE m 0x2e8654 [C1 (Z_to_bv 8 0)] H. exact H.
    - img_chunk0 NONE m 0x30b218 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                                C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H. exact H.
    - img_chunk0 NONE m 0x30b338 [C8 (Z_to_bv 64 0)] H. exact H.
  Qed.
  Lemma dso_init : rw_cells psegs m RDSO [C8 (wz RDSO)].
  Proof. unfold RDSO. img_chunk0 NONE m 0x2d7eb0 [C8 (wz 0x2d7eb0)] H. exact H. Qed.
  (* [comment removed for export] *)
  Lemma axstat_init_lit :
    rw_cells psegs m 0x2e8654 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0x30b218 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x30b338 [C8 (Z_to_bv 64 0)].
  Proof. pose proof axstat_init as H. unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells in H. cbn [Z.add] in H. tauto. Qed.
  Lemma dso_init_lit : rw_cells psegs m 0x2d7eb0 [C8 (wz RDSO)].
  Proof. pose proof dso_init as H. unfold RDSO in H at 1. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stage_init : stk psegs m RSTAGE (RSTAGE + 65536).
  Proof.
    apply (PERF_HEX__.stk_of_seg__ psegs m Plain_segment_003 Plain_seg_bytes_003).
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

(* [comment removed for export] *)
End WithCeiling1.
Ltac open_at_main AM :=
  destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & EMS
                 & MI & ST & TDa & ERR & TDb & LCa & LCb & MT & SI & G2 & HW & ENVC & DS & GU & GD & GOT0 & GCX & GSE & GFZ & GDF & GOT3 & GIN & GG & GFI
                 & INA & FIA & SEP & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & WR & HP0 & NONE & Ht).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem main_to_P1_proof : forall C : cli_sig, main_to_P1_stmt C.
Proof.
  unfold main_to_P1_stmt. intros C CLI0AT sp0 inp mbase ms VSP CEIL VARGV VENVP FITS HSP ARGC2 AM.
  pose proof AM as AM0.
  open_at_main AM. subst ms. unfold STK_DEPTH in ST.
  pose proof (CLI0AT _ _ _ _ _ _ _ _ _ _ AM0) as CL0. clear AM0.
  exists t. split; [exact Ht|].
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
  assert (HC2 : argc inp = 2) by (unfold argc; lia).
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
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (NONE' : forall a : word, (0x27a000 <= bv_unsigned a < 0x30d000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
      by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
    destruct (heap_init sp0 inp mf NONE' LCa LCb GG GU MI) as [HEAP AUXC];
    pose proof (rauxv_ok_init sp0 inp mbase mf NONE' LCa LCb GG GU MI (conj IMG HSP) ltac:(unfold sp_window_lo; lia) CEIL) as RAUX;
    pose proof (stderr_wfile0_init mf NONE') as SWF;
    pose proof (malloc_impl_init mf NONE') as MIMPL;
    pose proof (free_impl_init mf NONE') as FIMPL;
    pose proof (got_free_init mf NONE') as GFR;
    pose proof (base_inited_init mf NONE') as BI0;
    pose proof (stdin_init mf NONE') as STDIN0;
    pose proof (flags_init mf NONE') as FLG;
    pose proof (initflag_init mf NONE') as IFL;
    pose proof (axstat_init mf NONE') as AX0;      (* [comment removed for export] *)
    pose proof (dso_init mf NONE') as DSO0;        (* [comment removed for export] *)
    pose proof (stage_init mf NONE') as STG0
  end.
  apply evt_done. unfold P1.
  exists t0, t1, t2, a3, a4, a5, a6, a7, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6. eexists. eexists.
  split. { unfold Drv_main_defs.RMAIN_RET, RP1, RATP, RMAIN. cbv delta [mkR]. reflexivity. }
  split. { unfold MFRAME, RMAIN, Drv_main_defs.RMAIN_RET. rewrite HC2. exact FR. }
  split.
  { unfold BASE, LO, ESTAT, RGOT_LLVMINIT. split; [exact ST|]. split; [exact MI|].
    split. { split_spine; first [hyp_by_addr | exact STDIN0]. }
    split; [exact RAUX|]. split; [split; [exact GG| exact GU]|]. split; [| exact (conj IMG HSP)].
    unfold lx_statics. split_spine; [exact GSE | exact SEP | exact GDF | exact MIMPL | exact GFR | exact FIMPL |].
    (* [comment removed for export] *)
    intros a Ha. apply NONE'; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; [lia| cbn [outside crt_written]; lia]. }
  split; [exact HEAP|].
  split. { unfold RATP. replace (bv_unsigned (wz 0x2eb1c8) + -164)%Z with 0x2eb124%Z by (unfold wz; rewrite unsigned_lit by lia; reflexivity). exact ERR. }
  split. { exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
           exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6))))). }
  split; [exact SWF|]. split; [exists (wz 0); exact FLG|]. split; [exact IFL|]. split; [exact STG0|].
  split; [| exact AX0].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply (cli0_stable C); [exact CL0|]. intros a Ha Hw.
  assert (HO : outside [(bv_unsigned sp0 - 6144513, bv_unsigned sp0 + -48)]%Z a).
  { unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in Hw. cbn in Hw. cbn [outside]. lia. }
  split; [apply MU; unfold wa; rewrite unsigned_lit by lia; exact HO| intros Hv; apply WM; exact Hv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
  (* [comment removed for export] *)
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Theorem main_usage_proof : main_usage_stmt.
  Proof.
    unfold main_usage_stmt. intros sp0 inp mbase ms VSP CEIL VARGV VENVP FITS HSP ARGCN AM.
    open_at_main AM. subst ms. unfold STK_DEPTH in ST.
    pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
    (* LPS 08b1429: [argv_cstring] now states its bounds with [launch_string_bytes] while
       [HSP] still spells them [InitMem.str_len]/[InitMem.head_size]; the two are convertible
       but opaque to [lia], and the frame's disjointness check needs them in one spelling,
       so put HSP into the unfolded form before the first framing step. *)
    unfold InitMem.str_len, InitMem.head_size in HSP.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (HCR : 0 <= argc inp <= 1024 /\ argc inp <> 2) by (unfold argc; lia).
    (* [comment removed for export] *)
    assert (Harg0 : exists arg0 rest, in_argv inp = arg0 :: rest).
    { destruct (in_argv inp) as [|a r]; [cbn in VA1; lia | exists a, r; reflexivity]. }
    destruct Harg0 as (arg0 & rest & EARGV).
    assert (Hnth : nth_error (in_argv inp) 0 = Some arg0) by (rewrite EARGV; reflexivity).
    destruct (argv_cstring sp0 inp mbase m (conj IMG HSP) 0 arg0 Hnth ltac:(clear - SP16; Z.div_mod_to_equations; lia))
      as (p & slack & HP & PLO & PHI & STR0 & SLK).
    rewrite HP0 in HP. assert (EW : Z_to_bv 64 P0 = Z_to_bv 64 p) by congruence. clear HP.
    pose proof (image_length inp mbase pph PENTRY sp0 run_draw HSP) as BSL. pose proof (u64_range (ed_top run_draw)) as TOPR.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMB. unfold str_base, InitMem.str_len in PLO.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Hnth)) as NONUL0. cbn beta in NONUL0.
    pose proof (proj1 (Forall_forall _ _) VA3 arg0 (nth_error_In _ _ Hnth)) as LEN0. cbn beta in LEN0.
    (* [comment removed for export] *)
    destruct (stack_pieces sp0 inp mbase m (conj IMG HSP)) as (_ & ARGV & _).
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
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    pose proof (rd_u64s_g psegs _ (bv_unsigned sp0 + 8) _ 0 _ (Z_to_bv 64 (bv_unsigned sp0 + 8)) ARGV
                  ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite EW. lstep. lstep. lstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (0x27a000 <= bv_unsigned a < 0x30d000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
      pose proof (stderr_wfile_init mf NONE') as SWF; pose proof (base_inited_init mf NONE') as BI0; pose proof (base_inited0_init mf NONE') as BIB;
      (* [comment removed for export] *)
      (* LPS 08b1429: [axstat_init_lit] now also discharges the section's stack-image
         hypothesis, so it takes [sp0 inp mbase m NONE IMGH]. *)
      destruct (axstat_init_lit sp0 inp mbase mf NONE' (conj IMG HSP))
        as (INCB0 & AXC0 & AXA0);
      pose proof (dso_init_lit mf NONE') as DSO0;
      destruct (stdin_init mf NONE') as (ij0 & ij1 & ij2 & ij3 & ij4 & SINC); clear NONE NONE'
    end.
    apply evt_done.
    (* [comment removed for export] *)
    change (io_diag io (DUsage (nth 0 (argv_Z (in_argv inp)) []))) with (s_diag (St:=PState) (DUsage (nth 0 (argv_Z (in_argv inp)) []))).
    replace (nth 0 (argv_Z (in_argv inp)) []) with (map bv_unsigned arg0) by (rewrite EARGV; reflexivity).
    assert (ESP112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -128)) = bv_unsigned sp0 + -128) by (apply unsigned_lit; lia).
    eapply implM_bind.
    { eapply (FPR (DUsage (map bv_unsigned arg0))) with (lo := bv_unsigned sp0 - 6144513) (canary := rr_guard);
        [ exact FWE | exact FLS | exact SWF | reflexivity | 
        | rewrite ESP112; exact ST | rewrite ESP112; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite ESP112; lia
        | split; [exact GG | exact GU] | exact MI | vm_compute; reflexivity ].
      rewrite ?ESP112. cbn [diag_args]. split; [reflexivity|]. exists slack.
      rewrite unsigned_lit by lia.
      rewrite zb_map_unsigned. unfold zlength. rewrite length_map.
      split; [exact STR0|]. split; [apply map_unsigned_pos; exact NONUL0|]. split; [exact SLK|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 & -> & MU1 & WM1 & MI1 & FRM1 & FREGS & ST1 & SWF1 & SSP1 & ->).
    rewrite (ret_pc_even _) by (cbn; lia). rewrite ESP112 in MU1, ST1.
    clear MU WM. lazymatch type of MU1 with munch _ ?mprev m2 => transport_after_call psegs mprev m2 MU1 WM1 end.
    apply implM_ret.
    (* [comment removed for export] *)
    step. step. do 9 step. step. step.
    try rewrite (ret_pc_even _) by (cbn; lia).
    step.
    release_frame FR ST1 (bv_unsigned sp0 + -48).
    apply evt_done.
    destruct SWF1 as (eflags & emode & ee & ewend & etail & SEF1 & _).
    destruct SSP1 as [GG1 GU1]. unfold got_ssp, ssp_guard in GG1, GU1.
    unfold at_exit.
    do 31 eexists. exists Ft, fc', m2, (bv_unsigned sp0 - 6144513), t. do 4 eexists. exists rr_guard. do 4 eexists. exists false.   (* [comment removed for export] *)
    split. { cbv delta [mkR]. reflexivity. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -48)) = bv_unsigned sp0 + -48) by (apply unsigned_lit; lia).
    rewrite !ESP.
    split; [exact ST1|].
    split; [exact TDa|]. split; [exact EXL|]. split; [exact GFI|]. split; [exact FIA|]. split; [exists (Z_to_bv 8 0); exact BIB|]. split; [exact BI0|]. split; [exact FIN|]. split; [exact GCX|].
    split; [exact LCa|]. split; [exact OFL|]. split; [exact SIN|]. split; [exists ij0, ij1, ij2, ij3, ij4; exact SINC|]. split; [exact SOU|]. split; [exact SEU|].
    split. { cbn [ps_so ps_init]. exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
             split; [exact SOF1|]. split; [exact SOF2|]. split; [exact SOF3|]. split; [exact SOF4|]. split; [exact SOF5| exact SOF6]. }
    split. { exists eflags, emode, ee, ewend, etail. exact SEF1. }
    split; [exact GG1|]. split; [exact GU1|]. split; [exact MI1|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|]. split; [lia|]. split; [lia|].
    (* [comment removed for export] *)
    split.
    { unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells. cbn [Z.add].
      split; [exact INCB0|]. split; [exact AXC0| exact AXA0]. }
    unfold RDSO at 1. exact DSO0.
  Qed.
End Usage.
End WithCeiling2.
