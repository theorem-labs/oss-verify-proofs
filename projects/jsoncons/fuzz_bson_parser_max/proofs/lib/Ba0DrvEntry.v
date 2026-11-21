(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv, the 6 MiB zero-filled stack window): changed ES, L0, WINDOW and 10 more; added STR0, auxvp; removed auxv_listA; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvEntry.v, 60 lines within its lines 14-218. *)
(* LPS 727298f3: a recorded stack window was measured UP from sp at the released model (f1006fe8 Run.v init_machine_state) and is measured DOWN from the stack VMA end at LPS 727298f3 (Run.v stack_window_lo), so a window of 8388608 bytes below sp claims up to 2101782 bytes the model answers None for. Shortened by gen_kwin_plain.py to stack_max_size - max (TOP - SP) = 6144513, keeping the window's TOP unchanged; every number read out of the model, see the tool's four control legs. *)
(* LPS 727298f3: the recorded libc.auxv cell held argv[0] - 160, the auxv base at the released model only; at LPS 727298f3 the base is usp + 8*argc + 8*envc + 24 and argv[0] is STR0, which carries the arch_align_stack pad. The base is now slot 5 of the main environment, which was an unused zero, so no variable index moves. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapIface HeapIfaceA HeapIfaceABx As0DrvKitA.
(* [auxv_atA] is stated in [LibIface.auxv_launch]'s terms, qualified *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr_mainA : list expr :=
  [ELit 0; ELit 0x115b04; spx (-48); ELit 0x10800; ELit 0x671880; EVar 11; EVar 12; EVar 13;
   spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
   EVar 22; EVar 23; ELit 0xa773c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_mainA : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   (* The zero window is [StoreOk.stack_window_depth] = 6144513 deep
      ([AsanPlanCoreK.v:3801-3830]); it was 8388608, which 727298f3 makes false
      (as in jsoncons/fuzz_bigint).  [Bo0DrvEntry.v] carries the twin. *)
   KWr (SA (EVar 0) (-6144513)) (6144513);
   KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KImg 0x10000 0x136000; KImg 0x66fe10 0x6717b0;          (* [comment removed for export] *)
   KImg 0x1397e0 0x1398d0; KImg 0x1398d0 0x1399b8; KImg 0x1399b8 0x13a0e0;   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x6918c0) 8 (EVar 3);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x6717b8) 8 (ELit 0x6717b8); KWord (SA (ELit 0) 0x6717d8) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 0x671870) 8 (EVar 3); KWord (SA (ELit 0) 0x671850) 8 (ELit 0x691b48);
   (* The auxv base is its own environment slot, [EVar 5], as [Src0MainEntry.v:122]
      holds [auxvp] in slot 3 of its environment.  Was [EVar 1 - 160], "argv[0]
      pointer minus 160", true when [p0] was [auxv_end] at the released model and
      false at 727298f3, where [p0] is [STR0] and the auxv base is
      [usp + 8*argc + 8*envc + 24] ([Ba0DrvEntryK.v:988 val_auxp]); no constant
      offset from [p0] is the auxv base (as in jsoncons/fuzz_bigint). *)
   KWord (SA (ELit 0) 0x691b18) 8 (EVar 5);
   KImg 0x139710 0x1397b8; KImg 0x691b48 0x691b78;
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 6888176) 4 (ELit 0); KWord (SA (ELit 0) 6888211) 1 (ELit 0); KWord (SA (ELit 0) 6887648) 8 (ELit 6887656); KWord (SA (ELit 0) 6887640) 4 (ELit 1);
   KWord (SA (ELit 0) 6887664) 8 (ELit 1139320); KWord (SA (ELit 0) 6887920) 8 (ELit 618908); KWord (SA (ELit 0) 6887636) 4 (ELit 0); KWord (SA (ELit 0) 6887656) 8 (ELit 0);
   KWord (SA (ELit 0) 6889608) 8 (ELit 0); KWord (SA (ELit 0) 6887632) 1 (ELit 0); KWord (SA (ELit 0) 6888432) 4 (ELit 0)].
(* [comment removed for export] *)
Definition XC9_CELLS : list (Z * nat * Z) :=
  [(6888176, 4%nat, 0); (6888211, 1%nat, 0); (6887648, 8%nat, 6887656); (6887640, 4%nat, 1); (6887664, 8%nat, 1139320); (6887920, 8%nat, 618908); (6887636, 4%nat, 0); (6887656, 8%nat, 0);
   (6889608, 8%nat, 0); (6887632, 1%nat, 0); (6888432, 4%nat, 0)].      (* [comment removed for export] *)

(* The auxiliary vector at [auxvp] (the value of [libc.auxv], slot 5 of
   [vals_mainA]), as the LPS 727298f3 launch writes it: [LibIface.auxv_vec],
   27 pairs or 29 under CONFIG_RSEQ, the shape [LibIface.auxv_launch] asks of
   [__auxv], with this image's program headers (0x10040, 56, 11).  It replaces
   the old ten-pair [auxv_listA], which is not what the launch writes at this
   revision.  Proved at the main entry by [Ba0DrvEntryInst.as0_main_auxv]. *)
Definition auxv_atA (sp auxvp : word) (M0 : word -> option byte) : Prop :=
  exists (uidz rnd hwz : Z) (la : StackLayout.LaunchAuxv) (ph : PhdrInfo) (entry gid ae : word),
    Z.of_N (ph_addr ph) = 0x10040 /\ Z.of_N (ph_ent ph) = 56 /\ Z.of_N (ph_num ph) = 11
    /\ bv_unsigned auxvp + 16 * Z.of_nat (StackLayout.auxv_count (StackLayout.la_rseq la)) <= 2 ^ 47
    /\ (forall j, (j < 2 * StackLayout.auxv_count (StackLayout.la_rseq la))%nat ->
          LibIface.cellz ASEGS M0 (bv_unsigned auxvp + 8 * Z.of_nat j) 8 (nth j (LibIface.auxv_vec la ph entry gid ae uidz rnd hwz) 0))
    /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ bv_unsigned sp <= rnd /\ rnd + 16 <= 2 ^ 64
    /\ bv_unsigned sp <= bv_unsigned auxvp /\ bv_unsigned auxvp mod 8 = 0.

Definition NX_MAIN : nat := 38.
Definition vals_mainA (sp p0 p1 can tid auxvp : word) (R : bvmap 5 word) : list word := [sp; p0; p1; can; tid; auxvp] ++ junk_vals R.
Definition env_mainA (sp p0 p1 can tid auxvp : word) (R : bvmap 5 word) : env := Env (vals_ev (vals_mainA sp p0 p1 can tid auxvp R)) (blobs_ev []).

Definition all_regsA : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma nth_all_regsA : forall n, (n < 32)%nat -> nth n all_regsA 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_indexA : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section Pack.
  (* [STR0] is a PARAMETER, not a value: at 727298f3 the string base is
     [usp + cat_string_off rseq sp top argv envp execfn], which carries the
     [arch_align_stack] pad and so is NOT a function of [envc]/[L0].  This
     Section is deliberately the numeric layer [main_regs_okA]/[main_know_okA]
     are proved in, so the launch (rseq, ed_top, argv, envp, execfn) stays out
     of it and the caller instantiates [STR0].  Was the closed form
     [usp + 8*envc + 200], which is false at this revision. *)
  Variables (sp : word) (envc L0 STR0 : Z).
  Variable R : bvmap 5 word.
  Variable MV : word -> option byte.
  #[local] Notation usp := (bv_unsigned sp).
  Hypothesis Hsp : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Hypothesis Hb : 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
  (* [comment removed for export] *)
  Hypothesis REGS : forall r v, In (r, v)
    [(1, 0x115b04); (2, usp - 48); (3, 0x10800); (4, 0x671880); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xa773c); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)] ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Hypothesis WORDS :
    rdn ASEGS MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 STR0))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (STR0 + L0 + 1))).
  (* [StoreOk.stack_window_depth], not the literal 8388608 -- [ent_window] is
     stated in those terms at [Ba0DrvEntryK.v:609-610]. *)
  Hypothesis WINDOW : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= stack_window_depth -> store_ok ASEGS MV (Z_to_bv 64 (usp - stack_window_depth + d)) m = true.
  Variable can : word.
  Hypothesis GUARD : rdn ASEGS MV (Z_to_bv 64 0x6918c0) 8 = Some (word_to_le_bytes 8 can).
  Hypothesis IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x137028); (0x137044, 0x13a0e0); (0x65fe0a, 0x6717b0); (0x691b48, 0x691b78)] -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  (* [comment removed for export] *)
  Variable tid : word.
  Hypothesis TIDR : 1 <= bv_unsigned tid <= 4194303.
  Hypothesis LIBW :
    rdn ASEGS MV (Z_to_bv 64 0x6717b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6717b8))
    /\ rdn ASEGS MV (Z_to_bv 64 0x6717d8) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS MV (Z_to_bv 64 0x671870) 8 = Some (word_to_le_bytes 8 can)
    /\ rdn ASEGS MV (Z_to_bv 64 0x671850) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x691b48))
    (* The auxv base, spelled as [ent_libcells] spells it
       ([Ba0DrvEntryK.v:992-997]): [usp + 8*argc + 8*envc + 24].  This path has
       [argv = [a0s; path]], so [argc = 2] and [8*2 + 24 = 40] -- the same
       address as the old [usp + 8*envc + 40], now written so it cannot drift
       when argc does.  The caller bridges the two spellings by [lia]. *)
    /\ rdn ASEGS MV (Z_to_bv 64 0x691b18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * 2 + 8 * envc + 24))).

  (* [comment removed for export] *)
  Hypothesis XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS.

  Let p0 : word := Z_to_bv 64 STR0.
  Let p1 : word := Z_to_bv 64 (STR0 + L0 + 1).
  (* The auxv base at [argc = 2], spelled as the callers ([Ba0DrvEntryInst.v],
     [Ba0MainPhaseA.v]) spell it; [LIBW]'s last cell is the same address. *)
  Let auxvp : word := Z_to_bv 64 (usp + 8 * envc + 40).
  Let ES : env := env_mainA sp p0 p1 can tid auxvp R.

  #[using="Type"] Lemma ev_junkA : forall i, (i < 32)%nat -> ev ES (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold ES, env_mainA, vals_mainA. cbn [ev]. unfold vals_ev.
    change (6 + i)%nat with (length [sp; p0; p1; can; tid; auxvp] + i)%nat. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  #[using="Type"] Lemma spx_valA : forall k, edenot ES (spx k) = Z_to_bv 64 (usp + k).
  Proof.
    intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev ES 0) with sp.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  #[using="REGS"] Theorem main_regs_okA : regs_ok ES sr_mainA R.
  Proof.
    apply regs_ok_by_indexA. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_mainA Z.of_nat Pos.of_succ_nat Pos.succ].
    all: try solve [rewrite ?spx_valA; cbn [edenot]; apply REGS; cbn [In]; repeat (first [left; reflexivity | right])].
    all: try (match goal with |- getr R (Z_to_bv 5 ?z) = edenot ES (EVar _) =>
                let k := eval cbv in (Z.to_nat z) in exact (eq_sym (ev_junkA k ltac:(lia))) end).
    (* [comment removed for export] *) cbn [edenot]. reflexivity.
  Qed.

  #[using="Type"] Lemma adenot_flat : forall E a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros E a n Hf. rewrite <- (flat_u E a n Hf). symmetry. apply Z_to_bv_bv_unsigned. Qed.

  #[using="Type"] Lemma estart_sp : forall off, estart ES (SA (EVar 0) off) = usp + off.
  Proof. intros off. unfold estart. cbn [a_base a_off edenot]. reflexivity. Qed.

  #[using="Hsp Hb WORDS WINDOW GUARD IMG TIDR LIBW XCW"] Theorem main_know_okA : know_ok ASEGS ES MV kn_mainA.
  Proof.
    destruct Hsp as (S1 & S2). destruct Hb as (B1 & B2). destruct WORDS as (W0 & W8 & W16). destruct LIBW as (L1 & L2 & L3 & L4 & L5).
    assert (FLIT : forall a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 63 -> flat ES (SA (ELit 0) a) n).
    { intros a n H1 H2 H3. unfold flat, estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. lia. }
    assert (ALIT : forall a, 0 <= a < 2 ^ 63 -> adenot ES (SA (ELit 0) a) = Z_to_bv 64 a).
    { intros a Ha. rewrite (adenot_flat ES (SA (ELit 0) a) 0 ltac:(apply FLIT; lia)). unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. reflexivity. }
    assert (FL : forall off n, -8388608 <= off -> 0 <= n -> off + n <= 4096 -> flat ES (SA (EVar 0) off) n).
    { intros off n H1 H2 H3. unfold flat. rewrite estart_sp. lia. }
    assert (XC : forall (i : nat) c, nth_error XC9_CELLS i = Some c ->
                   rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c))))
      by (intros i c Hn; exact (proj1 (Forall_forall _ _) XCW c (nth_error_In _ _ Hn))).
    unfold kn_mainA, know_ok. repeat (apply Forall_cons); [ .. | apply Forall_nil]; cbn [kentry_ok].
    - split; [lia | exact S2].
    - cbn [edenot]. change (ev ES 0) with sp. lia.
    (* [WINDOW] is stated in [stack_window_depth], as [ent_window] is, and the
       entry above carries the same 6144513. *)
    - split; [apply FL; lia|]. intros d m Hd Hm. rewrite estart_sp.
      assert (SWD : stack_window_depth = 6144513) by (vm_compute; reflexivity). rewrite SWD in WINDOW.
      replace (usp + -6144513 + d) with (usp - 6144513 + d) by ring. apply WINDOW; assumption.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 0) 8 ltac:(apply FL; lia)), estart_sp, Z.add_0_r. exact W0.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 8) 8 ltac:(apply FL; lia)), estart_sp. exact W8.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 16) 8 ltac:(apply FL; lia)), estart_sp. exact W16.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x10000 0x137028); [left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x65fe0a 0x6717b0); [right; right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x137044 0x13a0e0); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x137044 0x13a0e0); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x137044 0x13a0e0); [right; left; reflexivity | lia].
    - split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
      rewrite adenot_lit0. exact GUARD.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L1.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L2.
    - cbn [edenot]. change (ev ES 4) with tid. lia.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L3.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L4.
    (* The auxv cell: [KWord (SA (ELit 0) 0x691b18) 8 (EVar 5)], and slot 5 of
       [ES] is [auxvp], which is [LIBW]'s value for that cell. *)
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia.
      cbn [edenot]. change (ev ES 5) with auxvp. unfold auxvp.
      replace (usp + 8 * envc + 40) with (usp + 8 * 2 + 8 * envc + 24) by ring. exact L5.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x137044 0x13a0e0); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x691b48 0x691b78); [right; right; right; left; reflexivity | lia].
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 0%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 1%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 2%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 3%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 4%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 5%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 6%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 7%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 8%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 9%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 10%nat _ eq_refl).
  Qed.
End Pack.
End FPX_1.
