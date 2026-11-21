(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the stack image is pimg under the run_ok premise, the auxv is the launch's pair list for either rseq case, and the stack region's lower bound is 4 MiB below the entry sp instead of 8 MiB; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef): the stack pieces and the auxv pair list are read at the section's own stack pointer; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/P/Drv_main_A.v, 91 lines within its lines 103-569. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue InitMem Layout Exit Startup Printf_lib Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_main_defs.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Plain.M.phdrs.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import CeilWin.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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
Local Ltac OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
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

(* The launch's auxv as the pair list [rauxv_ok] takes: [auxv_entries] minus its
   AT_NULL, for either rseq case (26 or 28 pairs). *)
Definition zpair (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma map_wz_flat_pairs_zpair : forall es : list (word * word),
  map wz (flat_pairs (map zpair es)) = flat_map (fun e : word * word => [fst e; snd e]) es.
Proof.
  induction es as [|[a b] es IH]; [reflexivity|]. cbn [map flat_pairs zpair flat_map fst snd app].
  rewrite IH. unfold MallocRep.wz. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma auxv_pairs_words : forall la ph entry uid gid hw r x,
  map wz (flat_pairs (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) ++ [0; 0])
  = flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la ph entry uid gid hw r x).
Proof.
  intros. remember (auxv_entries la ph entry uid gid hw r x) as es eqn:Ees.
  assert (E : es = removelast es ++ [(AT_NULL, Z_to_bv 64 0)])
    by (subst es; unfold auxv_entries; destruct (la_rseq la); reflexivity).
  rewrite E at 2. rewrite flat_map_app, map_app, map_wz_flat_pairs_zpair. reflexivity.
Qed.

Lemma auxv_pairs_length : forall la ph entry uid gid hw r x,
  (length (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) + 1 = auxv_count (la_rseq la))%nat.
Proof. intros. rewrite length_map. unfold auxv_entries, auxv_count. destruct (la_rseq la); reflexivity. Qed.

Lemma auxv_pairs_facts : forall la ph entry uid gid hw r x,
  let L := map zpair (removelast (auxv_entries la ph entry uid gid hw r x)) in
  Forall (fun p => fst p <> 0) L /\ last_assoc 25 L = Some (bv_unsigned r)
  /\ Forall (fun p => fst p = 25 -> snd p = bv_unsigned r) L
  /\ Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L.
Proof.
  intros. subst L.
  assert (RG : forall w : word, 0 <= bv_unsigned w < 2^64)
    by (intros w; pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold auxv_entries; destruct (la_rseq la); cbn [removelast map zpair fst snd app];
    unfold AT_SYSINFO_EHDR, AT_L1I_CACHESIZE, AT_L1I_CACHEGEOMETRY, AT_L1D_CACHESIZE, AT_L1D_CACHEGEOMETRY,
      AT_L2_CACHESIZE, AT_L2_CACHEGEOMETRY, AT_L3_CACHESIZE, AT_L3_CACHEGEOMETRY, AT_MINSIGSTKSZ, AT_HWCAP,
      AT_PAGESZ, AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID, AT_GID,
      AT_EGID, AT_SECURE, AT_RANDOM, AT_EXECFN, AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN;
    (* [cbn] above leaves [zpair] folded over each pair: unfold it, so each conjunct below
       sees the [bv_unsigned] literals. *)
    (try unfold zpair); cbn [fst snd];
    (split; [repeat (apply Forall_cons; [cbn [fst snd]; rewrite unsigned_lit by lia; lia|]); apply Forall_nil|]);
    (split; [reflexivity|]);
    (split; [repeat (apply Forall_cons; [cbn [fst snd]; intros HK; first [reflexivity | rewrite unsigned_lit in HK by lia; lia]|]);
             apply Forall_nil|]);
    repeat (apply Forall_cons; [cbn [fst snd]; split; [rewrite unsigned_lit by lia; lia| apply RG]|]); apply Forall_nil.
Qed.

Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid : word) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at psegs m usp (pimg sp argv envp uid).
  Hypothesis ROK : run_ok sp argv envp.

  (* The auxv conjunct is left as [auxv_words] and [rnd_addr] keeps the flag:
     [run_ok] does not fix [la_rseq (run_la_at sp)], so a caller that needs the closed
     table case-splits on the flag and picks [auxv29_auxv_words] or
     [auxv27_auxv_words]. *)
  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs run_top argv envp run_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (auxv_addr sp argv envp)
      (u64s (auxv_words (run_la_at sp) pph pentry sp run_top argv envp run_execfn uid run_gid run_hw)) /\
    bytes_at psegs m (rnd_addr (la_rseq (run_la_at sp)) sp argv envp) (at_random_bytes run_rnd).
  Proof.
    destruct ROK as (G & _).
    destruct (img_pieces psegs (run_la_at sp) pph pentry sp run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG G)
      as (B0 & B1 & _ & B3 & B4 & _).
    exact (conj B0 (conj B1 (conj B3 B4))).
  Qed.

  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs run_top argv envp run_execfn) i = Some (Z_to_bv 64 p) /\ str_base run_top argv envp run_execfn <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (pimg sp argv envp uid)) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn _. destruct ROK as (G & _).
    exact (img_argv_cstring psegs (run_la_at sp) pph pentry sp run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG G i s Hn).
  Qed.

  (* Where argv[0] and the other strings sit relative to [sp]. *)
  Lemma str_base_lo : usp + 8 * (argc argv + envc envp + 3) + 448 <= str_base run_top argv envp run_execfn.
  Proof.
    destruct ROK as (G & _). pose proof (str_base_ge _ _ _ _ _ _ G) as SB.
    pose proof (head_len_ge (la_rseq (run_la_at sp)) argv envp) as HL. lia.
  Qed.

  Lemma pimg_end : usp + Z.of_nat (length (pimg sp argv envp uid)) = bv_unsigned run_top /\ bv_unsigned run_top <= 0x800000000000.
  Proof.
    destruct ROK as (G & TW). unfold sp_window_hi in TW.
    pose proof (img_length (run_la_at sp) pph pentry sp run_top argv envp run_execfn uid run_gid run_hw run_draw G) as L.
    unfold pimg. split; lia.
  Qed.
End Pieces.

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
Lemma find_seg3__ : forall a, (0xce000 <= a < 0x101000)%Z -> find_segment psegs a 1 = Some Plain_segment_003.
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

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section InitFacts.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (m : mem).
  Hypothesis NONE : forall a : word, (0xc7000 <= bv_unsigned a < 0x101000)%Z -> outside (crt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0x1003f8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0x100400 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0xcd328 [C8 (Z_to_bv 64 0x1003d8)].
  Hypothesis GUARD : rw_cells psegs m 0x1003d8 [C8 rr_guard].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMG : bytes_at psegs m (bv_unsigned sp0) (pimg sp0 argv envp uid).
  Hypothesis ROK : run_ok sp0 argv envp.
  Hypothesis CEIL : ceil_ok sp0.

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs)) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| | exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    all: intros a Ha; apply NONE; [lia|]; unfold crt_written; cbn; lia.
  Qed.

  (* The pair list is the launch's own [auxv_entries] (both rseq cases): the
     proof reads only the block geometry, not the rseq flag. *)
  Lemma rauxv_ok_init : rauxv_ok m (bv_unsigned sp0).
  Proof.
    destruct (pimg_end sp0 argv envp uid ROK) as [PE TW].
    pose proof (str_base_lo sp0 argv envp ROK) as SBL.
    destruct ROK as (G & _).
    destruct (img_pieces psegs (run_la_at sp0) pph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG G)
      as (_ & _ & _ & AUXW & RND & _).
    pose proof (str_base_ge _ _ _ _ _ _ G) as SB. pose proof (head_len_eq (la_rseq (run_la_at sp0)) argv envp) as HL.
    pose proof (head_len_ge (la_rseq (run_la_at sp0)) argv envp) as HG.
    pose proof (lsb_eq argv envp run_execfn) as LE.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (bv_unsigned_in_range 64 sp0) as RS0. unfold bv_modulus in RS0. cbn in RS0.
    pose proof (bv_unsigned_in_range 64 run_top) as RT0. unfold bv_modulus in RT0. cbn in RT0.
    unfold ceil_ok in CEIL.
    pose proof (auxv_pairs_length (run_la_at sp0) pph pentry uid run_gid run_hw
                  (Z_to_bv 64 (rnd_addr (la_rseq (run_la_at sp0)) sp0 argv envp)) (Z_to_bv 64 (xfn_base run_top argv envp run_execfn))) as PL.
    destruct (auxv_pairs_facts (run_la_at sp0) pph pentry uid run_gid run_hw
                (Z_to_bv 64 (rnd_addr (la_rseq (run_la_at sp0)) sp0 argv envp)) (Z_to_bv 64 (xfn_base run_top argv envp run_execfn)))
      as (NZ & LA & R25 & RNG).
    assert (HR0 : 0 <= rnd_addr (la_rseq (run_la_at sp0)) sp0 argv envp < 2^64)
      by (unfold rnd_addr, str_base, argc, envc in *; lia).
    rewrite (unsigned_lit _ HR0) in LA, R25.
    exists (auxv_addr sp0 argv envp),
      (map zpair (removelast (auxv_entries (run_la_at sp0) pph pentry uid run_gid run_hw
         (Z_to_bv 64 (rnd_addr (la_rseq (run_la_at sp0)) sp0 argv envp)) (Z_to_bv 64 (xfn_base run_top argv envp run_execfn))))),
      (rnd_addr (la_rseq (run_la_at sp0)) sp0 argv envp).
    split; [apply (proj2 heap_init)|].
    split; [rewrite auxv_pairs_words; exact AUXW|].
    split.
    { rewrite at_random_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R].
      rewrite ?length_le8 in R. exact R. }
    split; [|exact (conj NZ (conj LA (conj R25 RNG)))].
    unfold auxv_addr, rnd_addr, str_base, argc, envc in *.
    try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    repeat split; lia.
  Qed.

  Lemma stderr_init : rw_cells psegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x100950 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)).
  Proof.
    unfold file_cells.
    img_chunk0 NONE m 0xce428 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x100950 0 2 (Z_to_bv 64 0) 0xffffffff (zeros 80)) H.
    unfold file_cells in H. exact H.
  Qed.
  Lemma stderr_wfile0_init : stderr_wfile0 m.
  Proof.
    exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (zeros 80). split; [apply stderr_init|].
    split; [vm_compute; reflexivity|]. split; [left; reflexivity| lia].
  Qed.
  Lemma stderr_wfile_init : stderr_wfile m.
  Proof. apply stderr_wfile0_wfile, stderr_wfile0_init. Qed.

  Lemma got_nothrow_init : rw_cells psegs m SJ_GOT_NOTHROW [C8 (wz SJ_NOTHROW_TAG)].
  Proof. unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG. img_chunk0 NONE m 0xcd230 [C8 (wz 0x1c1d8)] H. exact H. Qed.
  Lemma impl_vt24_init : rw_cells psegs m SJ_IMPL_VT24 [C8 (wz SJ_CREATE_DPI)].
  Proof. unfold SJ_IMPL_VT24, SJ_CREATE_DPI. img_chunk0 NONE m 0xc7b28 [C8 (wz 0x3ca08)] H. exact H. Qed.
  Lemma dpi_vtable_init : rw_cells psegs m SJ_DPI_VPTR [C8 (wz SJ_DPI_PARSE); C8 (wz SJ_DPI_STAGE1); C8 (wz SJ_DPI_STAGE2); C8 (wz SJ_DPI_STAGE2_NEXT);
                                   C8 (wz SJ_DPI_PARSE_STRING); C8 (wz SJ_DPI_PARSE_WOBBLY); C8 (wz SJ_DPI_SET_CAPACITY);
                                   C8 (wz SJ_DPI_SET_MAX_DEPTH); C8 (wz SJ_DPI_DTOR); C8 (wz SJ_DPI_DTOR_DEL)].
  Proof.
    unfold SJ_DPI_VPTR, SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT, SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY,
      SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL.
    img_chunk0 NONE m 0xc7b78 [C8 (wz 0x4cfd4); C8 (wz 0x3cb08); C8 (wz 0x3e01c); C8 (wz 0x45504); C8 (wz 0x4ca60); C8 (wz 0x4cd40); C8 (wz 0x4d1a0);
                               C8 (wz 0x4d264); C8 (wz 0x4d320); C8 (wz 0x4d388)] H. exact H.
  Qed.

  Lemma pj_consts_init : pj_consts m.
  Proof.
    unfold pj_consts.
    img_chunk0 NONE m 0xc79d8 [C8 (wz 0x73730); C8 (wz 0x3b29c); C8 (wz 8)] H1.
    img_chunk0 NONE m 0xcb0b0 [C8 (wz 0x9a250)] H2.
    img_chunk0 NONE m 0xcd1f8 [C8 (wz 0xcaed0); C8 (wz 0xcaf50)] H3.
    img_chunk0 NONE m 0xcd238 [C8 (wz 0xdec60)] H4.
    img_chunk0 NONE m 0x1004d0 [C4 (wz 0)] H5.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    intros a Ha. apply NONE; unfold wa; rewrite unsigned_lit by lia; [lia| cbn [outside crt_written]; lia].
  Qed.

  Lemma el_consts_init : rw_cells psegs m EL_TPLOC [C8 (wz EL_GLOC)] -> el_consts m.
  Proof.
    intros TL. unfold el_consts.
    img_chunk0 NONE m 0xce380 [C8 (wz 0x6d6cc)] H1.
    img_chunk0 NONE m 0xce390 [C8 (wz 0x504cc); C8 (wz 0x505d8)] H2.
    img_chunk0 NONE m 0x100918 [C4 (wz 0); C4 (wz 0)] H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact TL].
  Qed.

  Lemma flags_init : sj_statics m false.
  Proof.
    unfold sj_statics, sj_cells, SJ_STATICS_LO. img_chunk0 NONE m 0xde6c8 [CB 168 (zeros 168)] H.
    img_chunk0 NONE m 0xde9a8 [CB 3760 (zeros 3760)] HL.
    img_chunk0 NONE m 0xde778 [C8 (wz 0); C4 (wz 0)] HE. img_chunk0 NONE m 0xe0090 [CB 8 (zeros 8)] HU.
    split; [exact H|]. split; [left; exact HL|]. split; [exact HE| exists false; exact HU].
  Qed.
  Lemma initflag_init : rw_cells psegs m RINIT_FLAG [C1 (Z_to_bv 8 0)].
  Proof. unfold RINIT_FLAG. img_chunk0 NONE m 0xde680 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  Lemma dso_init : rw_cells psegs m 0xce358 [C8 (wz 0xce358)].
  Proof. img_chunk0 NONE m 0xce358 [C8 (wz 0xce358)] H. exact H. Qed.
  Lemma aex_init : rw_cells psegs m 0x1001b0 [C1 (Z_to_bv 8 0)] /\ rw_cells psegs m 0x1001b4 [C4 z64; C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x1001c0 [C8 (Z_to_bv 64 0); C8 z64; C8 (Z_to_bv 64 0)] /\ rw_cells psegs m 0x1002d0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0xde680 [C1 (Z_to_bv 8 0)] /\ rw_cells psegs m 0xde684 [C1 (Z_to_bv 8 0)].
  Proof.
    img_chunk0 NONE m 0x1001b0 [C1 (Z_to_bv 8 0)] H1. img_chunk0 NONE m 0x1001b4 [C4 z64; C4 (Z_to_bv 64 0)] H2.
    img_chunk0 NONE m 0x1001c0 [C8 (Z_to_bv 64 0); C8 z64; C8 (Z_to_bv 64 0)] H3. img_chunk0 NONE m 0x1002d0 [C8 (Z_to_bv 64 0)] H4.
    img_chunk0 NONE m 0xde680 [C1 (Z_to_bv 8 0)] H5. img_chunk0 NONE m 0xde684 [C1 (Z_to_bv 8 0)] H6.
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
  Qed.
  Lemma aex_inv_init : aex_inv m.
  Proof. exists 0. split; [lia|]. exact aex_init. Qed.

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

End WithCeiling1.
Ltac open_at_main AM :=
  destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & EMS
                 & MI & ST & TDa & ERR & TDb & LCa & LCb & MT & SI & G2 & HW & ENVC & DS & GU & GD & GOT0 & GCX & GSE & GFZ & GDF & GOT3 & GIN & GG & GFI
                 & INA & FIA & SEP & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & WR & HP0 & NONE & Ht).

Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem main_to_P1_proof : main_to_P1_stmt.
Proof.
  unfold main_to_P1_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS ROK ARGC2 AM.
  open_at_main AM. subst ms.
  exists t. split; [exact Ht|].
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
  assert (HC2 : argc argv = 2) by (unfold argc; lia).

  assert (TL : rw_cells psegs m EL_TPLOC [C8 (Z_to_bv 64 EL_GLOC)]).
  { lazymatch type of TDb with rw_cells _ _ ?A0 (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      pose proof (proj1 (rw_cells_app psegs m A0 [c1; c2; c3; c4] (c5 :: rest)) TDb) as [_ T2];
      pose proof (proj1 (rw_cells_app psegs m _ [c5] rest) T2) as [T3 _];
      cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in T3;
      lazymatch type of T3 with rw_cells _ _ ?A1 _ => replace A1 with (EL_TPLOC)%Z in T3 by (cbn; lia) end;
      exact T3 end. }
  clear SEF WR INA INI GOT0 GOT3 GIN GD DS ENVC HW G2 SI MT TDb.
  destruct SOF as (sflags & smode & stail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
  unfold file_cells in SOF1. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add] in SOF1.
  pose proof (munch_refl [(bv_unsigned sp0 - 4194304, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  rewrite HC2.
  carve_frame 80%nat ST.
  zidle_beginZ (bv_unsigned sp0) 128%Z MUz WMz.
  do 12 lstep.
  zidle_end MUz WMz.
  if_false.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (NONE' : forall a : word, (0xc7000 <= bv_unsigned a < 0x101000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
      by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
    destruct (heap_init sp0 argv envp mf NONE' LCa LCb GG GU MI) as [HEAP AUXC];
    pose proof (rauxv_ok_init sp0 argv envp uid mf NONE' LCa LCb GG GU MI IMG ROK CEIL) as RAUX;
    pose proof (stderr_wfile0_init mf NONE') as SWF;
    pose proof (got_nothrow_init mf NONE') as GNT;
    pose proof (impl_vt24_init mf NONE') as VT24;
    pose proof (dpi_vtable_init mf NONE') as DPIV;
    pose proof (pj_consts_init mf NONE') as PJC;
    pose proof (el_consts_init mf NONE' TL) as ELC;

    pose proof (flags_init mf NONE') as FLG;
    pose proof (initflag_init mf NONE') as IFL;
    pose proof (dso_init mf NONE') as DSO;
    pose proof (aex_inv_init mf NONE') as AEXI;
    pose proof (stage_init mf NONE') as STG0
  end.
  apply evt_done. unfold P1.
  exists t0, t1, t2, a3, a4, a5, a6, a7, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6. eexists. eexists.
  split. { unfold Drv_main_defs.RMAIN_RET, RP1, RATP, RMAIN. cbv delta [mkR]. reflexivity. }
  split. { unfold MFRAME, RMAIN, Drv_main_defs.RMAIN_RET. rewrite HC2. exact FR. }
  split.
  { unfold BASE, LO, ESTAT, RGOT_LLVMINIT. split; [exact ST|]. split; [exact MI|].
    split. { split_spine; first [hyp_by_addr | exact AEXI]. }
    split; [exact RAUX|]. split; [split; [exact GG| exact GU]|]. split; [| exact IMG].
    unfold lx_statics. split_spine; [exact GSE | exact SEP | exact GNT | exact VT24 | exact DPIV | exact PJC | exact ELC]. }
  split; [exact HEAP|].
  split. { unfold RATP. replace (bv_unsigned (wz 0xe0168) + -164)%Z with 0xe00c4%Z by (unfold wz; rewrite unsigned_lit by lia; reflexivity). exact ERR. }
  split. { exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
           exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6))))). }
  split; [exact SWF|]. split; [exists false; exact FLG|]. split; [exact IFL| exact STG0].
Qed.

Section Usage.

  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Theorem main_usage_proof : main_usage_stmt.
  Proof.
    unfold main_usage_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS ROK ARGCN AM.
    open_at_main AM. subst ms.
    pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (HCR : 0 <= argc argv <= 1024 /\ argc argv <> 2) by (unfold argc; lia).

    assert (Harg0 : exists arg0 rest, argv = arg0 :: rest).
    { destruct argv as [|a r]; [cbn in VA1; lia | exists a, r; reflexivity]. }
    destruct Harg0 as (arg0 & rest & EARGV).
    assert (Hnth : nth_error argv 0 = Some arg0) by (rewrite EARGV; reflexivity).
    destruct (argv_cstring sp0 argv envp uid m IMG ROK 0 arg0 Hnth ltac:(clear - SP16; Z.div_mod_to_equations; lia))
      as (p & slack & HP & PLO & PHI & STR0 & SLK).
    rewrite HP0 in HP. assert (EW : Z_to_bv 64 P0 = Z_to_bv 64 p) by congruence. clear HP.
    pose proof (pimg_end sp0 argv envp uid ROK) as [PE TW]. pose proof (str_base_lo sp0 argv envp ROK) as SBL.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMB. unfold argc, envc in SBL.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Hnth)) as NONUL0. cbn beta in NONUL0.
    pose proof (proj1 (Forall_forall _ _) VA3 arg0 (nth_error_In _ _ Hnth)) as LEN0. cbn beta in LEN0.

    destruct (stack_pieces sp0 argv envp uid m IMG ROK) as (_ & ARGV & _).
    destruct SOF as (sflags & smode & stail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    unfold file_cells in SOF1. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add] in SOF1.
    clear SEF WR INA INI GOT0 GOT3 GIN GD DS ENVC HW G2 SI MT TDb.
    pose proof (munch_refl [(bv_unsigned sp0 - 4194304, bv_unsigned sp0 + -48)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
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
      assert (NONE' : forall a : word, (0xc7000 <= bv_unsigned a < 0x101000)%Z -> outside crt_written (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a) by (cbn [outside]; lia); apply NONE; [exact Ha| exact Ho]);
      pose proof (stderr_wfile_init mf NONE') as SWF;
      pose proof (dso_init mf NONE') as DSO;
      pose proof (aex_init mf NONE') as AEXC; destruct AEXC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6);
      clear NONE NONE'
    end.
    apply evt_done.

    change (io_diag io (DUsage (nth 0 (argv_Z argv) []))) with (s_diag (St:=PState) (DUsage (nth 0 (argv_Z argv) []))).
    replace (nth 0 (argv_Z argv) []) with (map bv_unsigned arg0) by (rewrite EARGV; reflexivity).
    assert (ESP112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -128)) = bv_unsigned sp0 + -128) by (apply unsigned_lit; lia).
    eapply implM_bind.
    { eapply (FPR (DUsage (map bv_unsigned arg0))) with (lo := bv_unsigned sp0 - 4194304) (canary := rr_guard);
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
    do 31 eexists. exists Ft, fc', m2, (bv_unsigned sp0 - 4194304), t. do 4 eexists. exists rr_guard. do 4 eexists.
    split. { cbv delta [mkR]. reflexivity. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -48)) = bv_unsigned sp0 + -48) by (apply unsigned_lit; lia).
    rewrite !ESP.
    split; [exact ST1|].
    split; [exact TDa|]. split; [exact EXL|]. split; [exact GFI|]. split; [exact FIA|]. split; [exact FIN|]. split; [exact GCX|].
    split; [exact DSO|].
    split; [exact LCa|].
    split. { exists 0. split; [lia|]. unfold aex_cells. cbn [Z.eqb Pos.eqb]. exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 Q6))))). }
    split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split. { cbn [ps_so ps_init]. exists sflags, smode, stail, bufb. unfold file_cells. cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length Z.of_nat Z.add].
             split; [exact SOF1|]. split; [exact SOF2|]. split; [exact SOF3|]. split; [exact SOF4|]. split; [exact SOF5| exact SOF6]. }
    split. { exists eflags, emode, ee, ewend, etail. exact SEF1. }
    split; [exact GG1|]. split; [exact GU1|]. split; [exact MI1|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|]. split; lia.
  Qed.
End Usage.
End WithCeiling2.

