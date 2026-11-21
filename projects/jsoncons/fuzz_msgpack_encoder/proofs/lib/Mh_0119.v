(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed ES, L0, S_mono and 87 more; added STR0, auxvp, model_rt_rdr and 2 more; removed auxv_listA; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvLib.v, 445 lines within its lines 22-963. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module Na0DrvEntry.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
Local Ltac lia := L5FastLia.plia.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr_mainA : list expr :=
  [ELit 0; ELit 0x137500; spx (-48); ELit 0x10800; ELit 0x693b00; EVar 11; EVar 12; EVar 13;
   spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
   EVar 22; EVar 23; ELit 0xaea2c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_mainA : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) (6144513);
   KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KImg 0x10000 0x158000; KImg 0x6920d0 0x693a30;          (* [comment removed for export] *)
   KImg 0x15b5a0 0x15b690; KImg 0x15b690 0x15b778; KImg 0x15b778 0x15c3a0;   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x6b3b40) 8 (EVar 3);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x693a38) 8 (ELit 0x693a38); KWord (SA (ELit 0) 0x693a58) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 0x693af0) 8 (EVar 3); KWord (SA (ELit 0) 0x693ad0) 8 (ELit 0x6b3dc8);
   KWord (SA (ELit 0) 0x6b3d98) 8 (EVar 5);
   KImg 0x15b4d0 0x15b578; KImg 0x6b3dc8 0x6b3df8;
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 7028080) 4 (ELit 0); KWord (SA (ELit 0) 7028115) 1 (ELit 0); KWord (SA (ELit 0) 7027552) 8 (ELit 7027560); KWord (SA (ELit 0) 7027544) 4 (ELit 1);
   KWord (SA (ELit 0) 7027568) 8 (ELit 1277044); KWord (SA (ELit 0) 7027824) 8 (ELit 648332); KWord (SA (ELit 0) 7027540) 4 (ELit 0); KWord (SA (ELit 0) 7027560) 8 (ELit 0);
   KWord (SA (ELit 0) 7029512) 8 (ELit 0); KWord (SA (ELit 0) 7027536) 1 (ELit 0); KWord (SA (ELit 0) 7028336) 4 (ELit 0)].
(* [comment removed for export] *)
Definition XC9_CELLS : list (Z * nat * Z) :=
  [(7028080, 4%nat, 0); (7028115, 1%nat, 0); (7027552, 8%nat, 7027560); (7027544, 4%nat, 1); (7027568, 8%nat, 1277044); (7027824, 8%nat, 648332); (7027540, 4%nat, 0); (7027560, 8%nat, 0);
   (7029512, 8%nat, 0); (7027536, 1%nat, 0); (7028336, 4%nat, 0)].      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition auxv_atA (sp auxvp : word) (M0 : word -> option byte) : Prop :=
  exists (uidz rnd hwz : Z) (la : StackLayout.LaunchAuxv) (ph : PhdrInfo) (entry gid ae : word),
    Z.of_N (ph_addr ph) = 0x10040 /\ Z.of_N (ph_ent ph) = 56 /\ Z.of_N (ph_num ph) = 11
    /\ bv_unsigned auxvp + 16 * Z.of_nat (StackLayout.auxv_count (StackLayout.la_rseq la)) <= 2 ^ 47
    /\ (forall j, (j < 2 * StackLayout.auxv_count (StackLayout.la_rseq la))%nat ->
          OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface.cellz ASEGS M0 (bv_unsigned auxvp + 8 * Z.of_nat j) 8
            (nth j (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface.auxv_vec la ph entry gid ae uidz rnd hwz) 0))
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
  Variables (sp : word) (envc L0 STR0 : Z).
  Variable R : bvmap 5 word.
  Variable MV : word -> option byte.
  #[local] Notation usp := (bv_unsigned sp).
  Hypothesis Hsp : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Hypothesis Hb : 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
  (* [comment removed for export] *)
  Hypothesis REGS : forall r v, In (r, v)
    [(1, 0x137500); (2, usp - 48); (3, 0x10800); (4, 0x693b00); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xaea2c); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)] ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Hypothesis WORDS :
    rdn ASEGS MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 STR0))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (STR0 + L0 + 1))).
  Hypothesis WINDOW : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= stack_window_depth -> store_ok ASEGS MV (Z_to_bv 64 (usp - stack_window_depth + d)) m = true.
  Variable can : word.
  Hypothesis GUARD : rdn ASEGS MV (Z_to_bv 64 0x6b3b40) 8 = Some (word_to_le_bytes 8 can).
  Hypothesis IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x158de8); (0x158e04, 0x15c3a0); (0x6820ca, 0x693a30); (0x6b3dc8, 0x6b3df8)] -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  (* [comment removed for export] *)
  Variable tid : word.
  Hypothesis TIDR : 1 <= bv_unsigned tid <= 4194303.
  Hypothesis LIBW :
    rdn ASEGS MV (Z_to_bv 64 0x693a38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x693a38))
    /\ rdn ASEGS MV (Z_to_bv 64 0x693a58) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS MV (Z_to_bv 64 0x693af0) 8 = Some (word_to_le_bytes 8 can)
    /\ rdn ASEGS MV (Z_to_bv 64 0x693ad0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6b3dc8))
    /\ rdn ASEGS MV (Z_to_bv 64 0x6b3d98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * 2 + 8 * envc + 24))).

  (* [comment removed for export] *)
  Hypothesis XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS.

  Let p0 : word := Z_to_bv 64 STR0.
  Let p1 : word := Z_to_bv 64 (STR0 + L0 + 1).
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
cbn [edenot]. reflexivity.
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
- split; [apply FL; lia|]. intros d m Hd Hm. rewrite estart_sp.
assert (SWD : stack_window_depth = 6144513) by (vm_compute; reflexivity). rewrite SWD in WINDOW.
replace (usp + -6144513 + d) with (usp - 6144513 + d) by ring. apply WINDOW; assumption.
- split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 0) 8 ltac:(apply FL; lia)), estart_sp, Z.add_0_r. exact W0.
- split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 8) 8 ltac:(apply FL; lia)), estart_sp. exact W8.
- split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 16) 8 ltac:(apply FL; lia)), estart_sp. exact W16.
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x10000 0x158de8); [left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x6820ca 0x693a30); [right; right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
rewrite adenot_lit0. exact GUARD.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L1.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L2.
- cbn [edenot]. change (ev ES 4) with tid. lia.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L3.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L4.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia.
cbn [edenot]. change (ev ES 5) with auxvp. unfold auxvp.
replace (usp + 8 * envc + 40) with (usp + 8 * 2 + 8 * envc + 24) by ring. exact L5.
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x6b3dc8 0x6b3df8); [right; right; right; left; reflexivity | lia].
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

End Na0DrvEntry.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
Module Na0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition STOPSA : list Z := [0x80740; 0x8073c; 0x7ebb8; 0x6a2b8; 0x6a2bc; 0x6a2d4; 0x6a2e4; 0x137cc8; 0xaeecc].
Definition FUELA : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition runA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPSA scr ss [].
End FPX_1.
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition IMG_CLIENT_A : list (Z * Z) :=
  [(0x10000, 0x158000); (0x15b4b8, 0x15c3a0); (0x6820d0, 0x693aa8); (0x693ab0, 0x693af8); (0x693b14, 0x693b28); (0x693b30, 0x6b4fb8);
   (0x6b4fc0, 0x6b6000)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_W_A : list (Z * Z) :=
  [(0x15b5a0, 0x15b8a0); (0x6820d0, 0x693aa8); (0x693ab0, 0x693af8); (0x693b14, 0x693b28); (0x693b30, 0x6b4fb8); (0x6b4fc0, 0x6b6000)].
Lemma img_client_rng : forall lo hi, In (lo, hi) IMG_CLIENT_A -> 0x10000 <= lo /\ hi <= 0x6b6000 /\ lo <= hi.
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi'.
Proof.
  intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
    [exists 0x15b4b8, 0x15c3a0 | exists 0x6820d0, 0x693aa8 | exists 0x693ab0, 0x693af8 | exists 0x693b14, 0x693b28
     | exists 0x693b30, 0x6b4fb8 | exists 0x6b4fc0, 0x6b6000];
    (split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.
(* [comment removed for export] *)
Definition IMG_RW_A : list (Z * Z) := [(0x6820d0, 0x6920d0)].
(* [comment removed for export] *)
Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
(* [comment removed for export] *)
Definition kn_blkA (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0x6a6000 (SA (EVar v) 0) n].

Lemma asegs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xaea2c sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x149d44 srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.

End Na0Drv_defs.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0119 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06I46Stdlib9micromega7EnvRing5PExpr00K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega=RingMicromega5Psatz02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7find_nzC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3CPaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3SCaC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_01199Na0DrvLib9dla_sptopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=sub_blockA_hzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibBhzA_of_block_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_clientC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs>img_client_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint05K47Corelib4Init7Decimal4uint07K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs<IMG_CLIENT_AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8IMG_RW_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init7Decimal4uint01c59OSSVerify5KrLib7Mh_01199Na0DrvLib:wseg_stageC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses3injK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib5Lists7ListDef6repeatC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt3RDAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead6rd_MV2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt9RDA_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead;rd_MV2_slotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_0101;Na0ReadIcptCread_icpt_post0_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead9rd_M2_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryc59OSSVerify5KrLib7Mh_0119:Na0DrvRead7rd_cellC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead<stage_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoc59OSSVerify5KrLib7Mh_0119:Na0DrvRead<rd_MV2_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned?rt_layout_globsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List:nth_repeatC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_01199Na0DrvLib?rdn_of_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt6c2_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt9out_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt8slots_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt2FRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcptBread_icpt_post_runC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses5mkappC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned9keeps_butC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2c59OSSVerify5KrLib7Mh_0119:Na0DrvRead5w_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib7Mh_0119:Na0DrvRead5STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt4RIPLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead8RD_CELLSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned2SBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned7HIGHENDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned6LOWENDC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst:eq_pos_injC59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned7HIGHBEGC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityK46Stdlib;setoid_ring<Ring_polynom5PExpr03I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3minC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC56Stdlib6ZArith6BinInt1Z3minC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:has_windowC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead:keep_readAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_haltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_minvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1c59OSSVerify5KrLib7Mh_01199Na0DrvLib?window_store_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead9avoid_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct@rdn_mrestrict_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcptAwrap_read_pre_runC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:nolazy_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=nolazy_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA;sbm_lazy_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib;with_fds_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib7Mh_00437FileSim@length_file_readC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK@with_fds_vm_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib>ahid_same_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@with_fds_halted'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<minv_same_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead7rd_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead;rd_M2_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_vmlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib;vml_same_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8ahid_sbmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3CWAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=vals_ev_junkAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib>window_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA?know_keep_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<with_fds_fdsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib7Mh_01199Na0DrvLib;with_fds_fsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib7Mh_0119:Na0DrvRead>rd_stage_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA<rz_msteps_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK?rz_read_file_lzC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC47Corelib4Init5Logic6or_indI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_minC49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00c59OSSVerify5KrLib7Mh_01199Na0DrvLib;c_kept_no0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead;IMG_NOSTAGEC1?~~~~~~~~~~~~~~~".
Module Na0DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvLib () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib7Mh_01167DrvKitA7find_nzC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint05K47Corelib4Init7Decimal4uint07K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init7Decimal4uint01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx9aiob_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib9dla_sptopC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:nolazy_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01C46Stdlib5Lists4List2Inc59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibBhzA_of_block_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface@callee_saved_idxC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthC47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula07C46Stdlib5Lists4List9nth_errorc59OSSVerify5KrLib7Mh_01199Na0DrvLib:has_windowC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA:kentry_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA=kentry_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorI69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib>has_window_nthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_01059SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib7Mh_00368AsanAcctHfind_segment1_none_aboveC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib7Mh_01199Na0DrvLib;segs_belowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_01199Na0DrvLib?window_store_okC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C59OSSVerify5KrLib7Mh_0116:As0DrvKitAEstore_ok_of_mrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib;setoid_ring<Ring_polynom3Mon00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modK46Stdlib9micromega7EnvRing5PExpr06C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib7Mh_01199Na0DrvLib>window_definedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9astack_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7kn_blkAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith4Znat5Nat2Z8inj_succI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00368AsanAcct>lazy_cover_mkHC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs9img_w_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs>img_client_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib7Mh_0119;Na0Drv_defs<IMG_CLIENT_AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3CWAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<block_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx7aiob_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib7Mh_01199Na0DrvLib<img_w_clientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;art_privateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_clientC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_ro_imgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6dla_roC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib?cwa_not_bshadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9aclient_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib?cwa_not_privateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx:aiob_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=sub_blockA_hzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib7Mh_01167DrvKitA8log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib>regions_writeAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitAAmem_denot_frame_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z;div_le_monoK46Stdlib;setoid_ring<Ring_polynom5PExpr09c59OSSVerify5KrLib7Mh_01199Na0DrvLib6STKTOPC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_minvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_haltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<lzinv_of_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib9stksh_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8hish_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:ainv_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8di_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8di_stkshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=stksh_not_cwaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_hishC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<hish_not_cwaC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib;block_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_vmlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_frameC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateAvmst_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State9vmst_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State9vmst_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC59OSSVerify5KrLib7Mh_00368AsanAcct3mkHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA;sbm_lazy_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib>ahid_same_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib;vml_same_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<minv_same_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib?model_rt_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs;keep_allocAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibBdinv_stack_definedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib7dla_scrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_scr_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;hl_scr_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:hl_scr_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx;aiob_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6dla_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibCastack_ok_of_windowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_01199Na0DrvLib=vals_ev_junkAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib@aclient_scr_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibDregs_preserved_keptAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appc59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:kn_blkA_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3CPaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib3SCaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib=regions_callAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA?know_keep_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib9dinv_callC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib;c_kept_no0AC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8IMG_RW_AC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_01199Na0DrvLib?in_lb_remove_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx9aiob_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib?in_block_removeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6u16_u8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib<aacc_of_blkAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA>aic_img_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib6S_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLibCablock_range_prefixC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_0089:IcptIfaceA?aic_memcpy_libcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8amem_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9amem_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_memcpyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posc59OSSVerify5KrLib7Mh_01199Na0DrvLib>aclient_removeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC46Stdlib5Lists4List=nth_error_nthC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_01199Na0DrvLib?rdn_of_bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eq".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma no_bls : forall (P : nat -> Z -> Prop) i nb, DrvKitA.find_nz i [] = Some nb -> P i nb.
Proof. intros P i nb H. discriminate H. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Section DrvLayoutA.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.

  (* [comment removed for export] *)
  Record drv_layoutA : Prop := DLA {
    dla_segs : hl_segs L = ASEGS;
    dla_malloc : hl_malloc L = 0x80740; dla_free : hl_free L = 0x8073c; dla_memcpy : icl_memcpy IL = 0x7ebb8;
    dla_tp : hl_tp L = 0x693b00;
    dla_img_lo : hl_img_lo L = 0x10000; dla_img_hi : hl_img_hi L = 0x6b6000;
    dla_sptop : ar_sptop ar = bv_unsigned sp0;
    dla_scr : 0 <= hl_scr_malloc L <= 4096 /\ 0 <= hl_scr_free L <= 4096 /\ 0 <= hl_scr_mem L <= 4096;
    (* [comment removed for export] *)
    dla_client : forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> ~ hl_rt_static L a;
    (* [comment removed for export] *)
    dla_ro : forall lo hi a, In (lo, hi) IMG_W_A -> lo <= a < hi -> ~ hl_rt_ro L a;
    dla_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x6b6000
  }.
  Hypothesis DL : drv_layoutA.

  Lemma wseg_stage : wseg_ok ASEGS (Z_to_bv 64 0x6820d0) 65536 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvLib ()) ["FPX_1"; "DrvLayoutA"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8p1002lp4p70p1003\p4p710R0p8p1004:p4p70P0p8p1004hp4p710P0p8p1005Cp4p710P0p8p1006Dp4p70P0p8g00=aj2=Tg00>;j17Tg00>Yj11Tg00?>j12Tg00?cj1;Tg00@Aj2:Tg00@gj13Tg00AEj16Tg00Acj14Tg00BAj15Tg00B^j18Tg00C=j39Tg00::j3<Tf0#2#2p=0g00D;R0g00D[R1'=g00E;g00FPR2#0#0#0#7%12#2#1#2#0#0#1#2#0#0#1#1#2#1#0#0#;':g00G5#3#6#4#4#3#5#839=<01do"). Qed.

  (* [comment removed for export] *)
  Lemma vis_of_inv : forall LB FF LK cr A M model a,
    ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a < 2 ^ 64 ->
    (a < 0x6b6000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) ->
    ahid A model (Z_to_bv 64 a) = false.
  Proof.
    intros LB FF LK cr A M model a HH Ha Hc.
    destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [exfalso | reflexivity].
    unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
    specialize (LZ (Z_to_bv 64 a) Hl). cbv zeta in LZ. rewrite u_small in LZ by lia.
    rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
    destruct Hc as [Hc|[Hc|Hc]]; [lia | lia | exact (Z3 Hc)].
  Qed.

  (* [comment removed for export] *)
  Lemma nolazy_of_inv : forall LB FF LK cr A M (model : Model) (a : word) n,
    ri_inv HI LB FF LK cr A M (vml_of model) -> bv_unsigned a + n <= 2 ^ 64 ->
    (forall k, 0 <= k < n -> bv_unsigned a + k < 0x6b6000 \/ bv_unsigned sp0 - 8388608 <= bv_unsigned a + k \/ in_block LB (bv_unsigned a + k)) ->
    nolazy_rng (m_vm_lazy model) a n.
  Proof.
    intros LB FF LK cr A M model a n HH Hn Hc k Hk. pose proof (u64_range a) as Ua.
    destruct (page_in_ranges (page_base_of (bv_unsigned a + k)) (m_vm_lazy model)) eqn:Hp; [exfalso | reflexivity].
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
    specialize (LZ (Z_to_bv 64 (bv_unsigned a + k))). unfold page_base in LZ. rewrite u_small in LZ by lia.
    specialize (LZ Hp). cbv zeta in LZ. rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
    destruct (Hc k Hk) as [H1|[H1|H1]]; [lia | lia | exact (Z3 H1)].
  Qed.

  (* [comment removed for export] *)
  Definition CPa (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
    aclient L ar LB FF sp scr a /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.
  Definition SCa (sp scr : Z) (a : Z) : Prop := sp - scr <= a < sp.

  (* [comment removed for export] *)
  Definition sub_blockA (LB : list (Z * Z)) (A nb : Z) : Prop :=
    exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ ablock_range L ar A cap.

  Definition hzA (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0x6b6000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
  Lemma hzA_of_block_range : forall A n, ablock_range L ar A n -> hzA A n.
  Proof.
    clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5 & B6). rewrite (dla_img_lo DL), (dla_img_hi DL) in B2. rewrite (dla_sptop DL) in B5.
    unfold hzA. repeat split; lia.
  Qed.
  Lemma sub_blockA_hz : forall LB A nb, sub_blockA LB A nb -> hzA A nb.
  Proof. clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hzA_of_block_range in HB. unfold hzA in *. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma regions_callA : forall vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model',
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> 0 <= scr <= 4096 ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
    (forall a, in_block LBc a -> in_block LB a) -> (forall a, in_block LBc a -> in_block LB' a) ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LBc (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    regions_ok ASEGS 0 so scr bls vbnd [] IMG_CLIENT_A IMG_RW_A E
               (CPa LBc FF (bv_unsigned sp0 + so) scr (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) scr).
  Proof.
    intros vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hsub Hsub' Hbl Hvb.
    pose proof Hsp as Hsp'.
    assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x6b6000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LBc a) ->
                  ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
    { intros a Ha Hc. split.
      - apply (vis_of_inv _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
      - apply (vis_of_inv _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPa. split; [|apply VIS; lia].
      unfold aclient. right. left. rewrite (dla_sptop DL). lia.
    - intros z Hz. right. unfold SCa. lia.
    - intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz.
      assert (IB : in_block LBc (bv_unsigned (vals_ev vals i) + z)).
      { exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
      unfold CPa. split; [left; exact IB | apply VIS; [lia | right; right; exact IB]].
    - exact Hvb.
    - intros i [].
    - intros lo hi Hin. pose proof (dla_client DL lo hi) as NS. destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CPa. split; [|apply VIS; lia]. unfold aclient. right. right. left.
      rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. exact (NS a Hin Ha).
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x6820d0) (Z_to_bv 64 d) 65536%nat m 0x6820d0 0x6920d0);
        first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma regs_preserved_keptA : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
  Proof.
    intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
    repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
  Qed.
  Lemma c_kept_no0A : ~ In (0%bv : reg) c_kept.
  Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.

  Lemma vals_ev_junkA : forall vals R' i, (i < 32)%nat ->
    vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
  Qed.

  Lemma aclient_scr_mono : forall LB FF sp scr scr' a, 0 <= scr' <= scr -> aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr' a.
  Proof.
    intros LB FF sp scr scr' a Hs Hc. unfold aclient, aclient_g in *.
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; split; [tauto | lia] | right; right; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-6144513)) (6144513))) kn.
  Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (-6144513)) (6144513)).
  Proof.
    intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  Lemma window_store_ok : forall vals ebs MV kn (z : Z) (m : nat),
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    (* [comment removed for export] *)
    - 6144513 <= z -> z + Z.of_nat m <= 0 ->
    store_ok ASEGS MV (Z_to_bv 64 (bv_unsigned sp0 + z)) m = true.
  Proof.
    intros vals ebs MV kn z m E HK Hw P0 Hz Hm. destruct (has_window_nth kn Hw) as [i Hn].
    pose proof (kwr_store_ok ASEGS E MV kn i (EVar 0) (-6144513) 6144513 z m HK Hn ltac:(lia) ltac:(lia)) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W. exact W.
  Qed.

  Lemma segs_belowA : segs_below_b ASEGS 0x6b6000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvLib ()) ["FPX_1"; "DrvLayoutA"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8p1002lp4p70p1003\p4p710R0p8p1004:p4p70P0p8p100GSp4p70P0p8p1004hp4p710P0p8p1005Cp4p710P0p8p1006Dp4p70P0p8g00=aj26Tg00>Yj12Tg00?>j10Tg00?cj15Tg01lGj24Tg00::j33Tf0#0#0p=1g00D;R0g00D[R1'6g00E;g00FP#2#0#2#0#2#2#0#2#2#0#1#1#1#1#1#1#5'4=301do"). Qed.

  (* [comment removed for export] *)
  Lemma store_ok_defined : forall (Mx : word -> option byte) a, 0x6b6000 <= a < 2 ^ 64 ->
    store_ok ASEGS Mx (Z_to_bv 64 a) 1 = true -> Mx (Z_to_bv 64 a) <> None.
  Proof.
    intros Mx a Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
    destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
    rewrite (find_segment1_none_above ASEGS 0x6b6000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite u_small by lia; lia). discriminate.
  Qed.

  Lemma window_defined : forall vals ebs (H : word -> bool) M kn,
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    forall a, bv_unsigned sp0 - 6144513 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None.
  Proof.
    intros vals ebs H M kn E HK Hw P0 a Ha. pose proof Hsp as Hsp'.
    pose proof (window_store_ok vals ebs _ kn (a - bv_unsigned sp0) 1 HK Hw P0 ltac:(lia) ltac:(lia)) as W.
    replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by ring.
    apply (store_ok_of_mrestrict ASEGS) in W. apply store_ok_defined; [lia | exact W].
  Qed.

  (* [comment removed for export] *)
  Lemma astack_ok_of_window : forall vals ebs (H : word -> bool) M kn so scr LB FF LK cr A V,
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 -> 0 <= scr <= 4096 ->
    ri_inv HI LB FF LK cr A M V ->
    defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0) ->
    astack_ok L ar M scr (bv_unsigned sp0 + so).
  Proof.
    intros vals ebs H M kn so scr LB FF LK cr A V E HK Hw P0 Hso Hsoal Hscr HH Hdef. pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    unfold astack_ok. rewrite (dla_sptop DL), (dla_segs DL).
    split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros d m Hd Hm. apply (store_ok_of_mrestrict ASEGS H).
      replace (bv_unsigned sp0 + so - scr + d) with (bv_unsigned sp0 + (so - scr + d)) by ring.
      apply (window_store_ok vals ebs _ kn _ m HK Hw P0); lia.
    - intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlt|Hge].
      + apply (window_defined vals ebs H M kn HK Hw P0). lia.
      + replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kn_blkA_ok : forall vals ebs Mx v n u,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
    ablock_range L ar u n -> defined Mx u n ->
    know_ok ASEGS E Mx (kn_blkA v n).
  Proof.
    intros vals ebs Mx v n u E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
    pose proof (hzA_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    assert (EA : bv_unsigned (edenot E (EVar v)) = u) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
    unfold kn_blkA, know_ok.
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
    apply Forall_cons.
    { cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
      destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (Hdef (bv_unsigned x - u) ltac:(lia)). replace (u + (bv_unsigned x - u)) with (bv_unsigned x) in Hdef by lia.
      rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (Mx x); [discriminate | exfalso; apply Hdef; reflexivity]. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
                         change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
                         change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma lzinv_of_inv : forall LB FF LK cr A M model,
    ri_inv HI LB FF LK cr A M (vml_of model) -> MInv A model -> m_halted model = None ->
    lzinv ASEGS (ahid A model) A model.
  Proof.
    intros LB FF LK cr A M model HH HM Hh.
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
    unfold lzinv. split.
    { intros a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl _].
      apply (find_segment1_none_above ASEGS 0x6b6000 _ segs_belowA).
      pose proof (LZ a Hl) as (Z1 & _). cbv zeta in Z1. rewrite (dla_img_hi DL) in Z1. exact Z1. }
    split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
    split; [exact AWF|]. split; [exact HM | exact Hh].
  Qed.

  Lemma model_rt_halted : forall m m', model_rt m m' -> m_halted m' = m_halted m.
  Proof. intros m m' ->. destruct m; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CWA (LB : list (Z * Z)) (a : Z) : Prop :=
    (* [comment removed for export] *)
    in_block LB a \/ bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).

  Lemma img_w_client : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi' /\ 0x10000 <= lo /\ hi <= 0x6b6000.
  Proof.
    intros lo hi Hin. destruct (img_w_sub lo hi Hin) as (lo' & hi' & Hin' & H1 & H2). destruct (img_client_rng lo' hi' Hin') as (I1 & I2 & I3).
    exists lo', hi'. split; [exact Hin'|]. split; [exact H1|]. split; [exact H2|].
    unfold IMG_W_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma cwa_not_bshadow : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> CWA LB a -> ~ block_shadow LB a.
  Proof.
    intros LB FF LK cr A M V a HH HC (b' & Hb' & X'). pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
    destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
    unfold in_shadow_of, S, SB in X'. rewrite (dla_sptop DL) in Q4. pose proof Hsp as HSP.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma cwa_not_private : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> 0 <= a < 2 ^ 64 -> CWA LB a -> ~ art_private L ar LB FF a.
  Proof.
    intros LB FF LK cr A M V a HH Ha HC [NC|[RO|BS]]; [| |exact (cwa_not_bshadow _ _ _ _ _ _ _ a HH HC BS)].
    - apply NC. unfold aclient. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
      + left. exact HB.
      + right. left. rewrite (dla_sptop DL). pose proof Hsp. lia.
      + right. right. left. destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4).
        rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. apply (dla_client DL lo' hi' a Hin'). lia.
    - pose proof (dla_ro_img DL a RO) as RI. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
      + destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
        destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
      + pose proof Hsp. lia.
      + exact (dla_ro DL lo hi a Hin Hr RO).
  Qed.

  (* [comment removed for export] *)
  Lemma ainv_frame : forall LB FF LK cr A M M' (model model' : Model),
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    vml_of model' = vml_of model ->
    ri_inv HI LB FF LK cr A M' (vml_of model').
  Proof.
    intros LB FF LK cr A M M' model model' HH FR GR EV. rewrite EV.
    apply (aiob_frame _ _ _ _ _ HIok LB FF LK cr A M M' _ HH); [|exact GR].
    intros a Ha HP. apply FR; [exact Ha|]. intros HC. exact (cwa_not_private _ _ _ _ _ _ _ a HH Ha HC HP).
  Qed.

  Lemma sbm_vml : forall m m', same_but_materialized m m' -> vml_of m' = vml_of m.
  Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
  Lemma sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
  Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. split; reflexivity. Qed.
  Lemma model_rt_fds : forall m m', model_rt m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
  Proof. intros m m' ->. destruct m; split; reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma sbm_rdrA : forall m m', same_but_materialized m m' -> m_channel_reader m' = m_channel_reader m.
  Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
  Lemma model_rt_rdr : forall m m', model_rt m m' -> m_channel_reader m' = m_channel_reader m.
  Proof. intros m m' ->. destruct m; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma regions_writeA : forall vals ebs bls LB FF LK cr A M V,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    ri_inv HI LB FF LK cr A M V ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A [] E (CWA LB) (fun _ => True).
  Proof.
    intros vals ebs bls LB FF LK cr A M V E P0 HH Hbl. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CWA. right. left. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). split; [lia|]. intros z Hz. unfold CWA. left.
      exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CWA. right. right. exists lo, hi. auto.
    - intros lo hi [].
  Qed.

  (* [comment removed for export] *)
  Lemma block_frame : forall vals ebs bls LB FF LK cr A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ (forall a : word, M a <> None -> M' a <> None).
  Proof.
    intros vals ebs bls LB FF LK cr A M M' model log E P0 HH Hbl Hlog EQM EQH.
    pose proof (regions_writeA vals ebs bls LB FF LK cr A M _ P0 HH Hbl) as RG.
    split.
    - intros a Ha HC. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
      assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
      rewrite E1, EQM.
      rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A _ (CWA LB) (fun _ => True) [] RG _ log a Hlog Ha HC).
      unfold mrestrict. rewrite Hh. reflexivity.
    - intros a Hd. destruct (ahid A model a) eqn:Hh; [rewrite (EQH a Hh); exact Hd|].
      assert (E1 : M' a = mrestrict (ahid A model) M' a) by (unfold mrestrict; rewrite Hh; reflexivity).
      rewrite E1, EQM. apply (mem_denot_grows E (mrestrict (ahid A model) M) log a). unfold mrestrict. rewrite Hh. exact Hd.
  Qed.

  (* [comment removed for export] *)
  Variable M0 : word -> option byte.
  (* [comment removed for export] *)
  Definition STKTOP : Z := Z.max (ar_sptop ar) (ar_stack_top ar).
  Lemma stksh_rng : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V -> in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x ->
    0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x.
  Proof.
    intros LB FF LK cr A M V x HH HS. pose proof Hsp as Hsp'.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    unfold in_shadow_of, S, SB, STKTOP in *. rewrite (dla_sptop DL) in *.
    assert (X2 : x <= 0x7fff8000 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8).
    { destruct HS as [_ HS]. replace (bv_unsigned sp0 - 8388608 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - (bv_unsigned sp0 - 8388608)) - 1)
        with (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) in HS by ring. lia. }
    assert (D1 : (0x7fff80000000 - 8388608) / 8 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) by ring.
    change ((0x7fff80000000 - 8388608) / 8) with 0xfffeff00000 in D1. change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2 |- *. lia.
  Qed.

  Record dinv (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := DINV {
    di_inv : ri_inv HI LB [] LK cr A M (vml_of model);
    di_minv : MInv A model;
    di_halt : m_halted model = None;
    di_above : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
    di_stksh : forall x, in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> byte_at M x 0;
    (* [comment removed for export] *)
    di_hish : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> byte_at M x 0;
    (* [comment removed for export] *)
    di_rdr : m_channel_reader model = true
  }.

  Lemma dinv_lzinv : forall LB LK cr A M model, dinv LB LK cr A M model -> lzinv ASEGS (ahid A model) A model.
  Proof. intros LB LK cr A M model D. exact (lzinv_of_inv _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) (di_minv _ _ _ _ _ _ D) (di_halt _ _ _ _ _ _ D)). Qed.

  (* [comment removed for export] *)
  Lemma stksh_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
    in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> ~ CWA LB x.
  Proof.
    intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (stksh_rng _ _ _ _ _ _ _ x HH HS) as ((X1 & X2) & _).
    destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
      destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
  Qed.

  Lemma hish_rng : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> 0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff.
  Proof.
    intros x HS. pose proof Hsp as Hsp'. unfold in_shadow_of, S, SB, ahl_ceil in *. rewrite (dla_sptop DL) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    clear - HS Hsp'. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma hish_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
    in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> ~ CWA LB x.
  Proof.
    intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (hish_rng x HS) as (X1 & X2).
    destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
      destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_frame : forall LB LK cr A M M' (model model' : Model),
    dinv LB LK cr A M model ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    vml_of model' = vml_of model -> MInv A model' -> m_halted model' = None ->
    m_channel_reader model' = m_channel_reader model ->
    dinv LB LK cr A M' model'.
  Proof.
    intros LB LK cr A M M' model model' D FR GR EV MI HL RD. pose proof Hsp as Hsp'. constructor.
    - exact (ainv_frame _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) FR GR EV).
    - exact MI.
    - exact HL.
    - intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply FR; [lia|].
      intros [HB|[HSt|(lo & hi & Hin & Hr)]].
      + destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (WF & _).
        destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
      + lia.
      + destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
    - intros x Hx. unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | | exact (stksh_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
      destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & _). lia.
    - intros x Hx. unfold byte_at. rewrite FR; [exact (di_hish _ _ _ _ _ _ D x Hx) | | exact (hish_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
      pose proof (hish_rng x Hx). lia.
    - rewrite RD. exact (di_rdr _ _ _ _ _ _ D).
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_block : forall vals ebs bls LB LK cr A M M' (model model' : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    lzinv ASEGS (ahid A model) A model' -> same_but_materialized model model' ->
    dinv LB LK cr A M' model'.
  Proof.
    intros vals ebs bls LB LK cr A M M' model model' log E P0 D Hbl Hlog EQM EQH HZ SBM.
    destruct (block_frame vals ebs bls LB [] LK cr A M M' model log P0 (di_inv _ _ _ _ _ _ D) Hbl Hlog EQM EQH) as (FR & GR).
    destruct HZ as (_ & _ & _ & MI & HL).
    exact (dinv_frame _ _ _ _ _ _ _ _ D FR GR (sbm_vml _ _ SBM) MI HL (sbm_rdrA _ _ SBM)).
  Qed.

  (* [comment removed for export] *)
  Lemma minv_same_vm : forall A (m m' : Model), m_vm m' = m_vm m -> MInv A m -> MInv A m'.
  Proof.
    intros A m m' EV [I1 I2 I3 I4 I5].
    constructor; unfold m_vm_materialized, m_vm_lazy, m_vmmaps, eager_used, m_vmmaps, m_vm_lazy in *; rewrite EV; assumption.
  Qed.
  Lemma vml_same_vm : forall (m m' : Model), m_vm m' = m_vm m -> vml_of m' = vml_of m.
  Proof. intros m m' EV. unfold vml_of, m_vmmaps, m_vm_lazy. rewrite EV. reflexivity. Qed.
  Lemma with_fds_vm : forall f (m : Model), m_vm (with_fds f m) = m_vm m.
  Proof. intros f m. destruct m. reflexivity. Qed.
  Lemma with_fds_fs : forall f (m : Model), m_fs (with_fds f m) = m_fs m.
  Proof. intros f m. destruct m. reflexivity. Qed.
  Lemma with_fds_fds : forall f (m : Model), m_fds (with_fds f m) = f.
  Proof. intros f m. destruct m as [[t p] v i fsy pr l tm]. reflexivity. Qed.
  Lemma with_fds_rdr : forall f (m : Model), m_channel_reader (with_fds f m) = m_channel_reader m.
  Proof. intros f m. destruct m. reflexivity. Qed.

  Lemma ahid_same_lazy : forall A (m m' : Model), m_vm_lazy m' = m_vm_lazy m -> ahid A m' = ahid A m.
  Proof. intros A m m' EL. unfold ahid. rewrite EL. reflexivity. Qed.
  Lemma ahid_sbm : forall A (m m' : Model), same_but_materialized m m' -> ahid A m' = ahid A m.
  Proof. intros A m m' SB. apply ahid_same_lazy. exact (sbm_lazy_eq _ _ SB). Qed.

  Lemma dinv_model : forall LB LK cr A M (model model' : Model),
    dinv LB LK cr A M model -> m_vm model' = m_vm model -> m_halted model' = None ->
    m_channel_reader model' = m_channel_reader model -> dinv LB LK cr A M model'.
  Proof.
    intros LB LK cr A M model model' D EV HL RD.
    apply (dinv_frame LB LK cr A M M model model' D); [reflexivity | auto | exact (vml_same_vm _ _ EV) | exact (minv_same_vm _ _ _ EV (di_minv _ _ _ _ _ _ D)) | exact HL | exact RD].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).

  Lemma dinv_stack_defined : forall LB LK cr A M model, dinv LB LK cr A M model ->
    defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Proof.
    intros LB LK cr A M model D i Hi.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    rewrite (di_above _ _ _ _ _ _ D) by lia. apply M0_def. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_call : forall LB LBc LB' LK LK' cr cr' A A' M M' (model model' : Model) sp scr,
    dinv LB LK cr A M model -> sp <= bv_unsigned sp0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBc [] sp scr a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    ri_inv HI LB' [] LK' cr' A' M' (vml_of model') -> MInv A' model' -> model_rt model model' ->
    dinv LB' LK' cr' A' M' model'.
  Proof.
    intros LB LBc LB' LK LK' cr cr' A A' M M' model model' sp scr D Hsp1 PR HH' MI RT. pose proof Hsp as Hsp'. constructor.
    - exact HH'.
    - exact MI.
    - rewrite (model_rt_halted _ _ RT). exact (di_halt _ _ _ _ _ _ D).
    - intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply PR; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
    - intros x Hx. destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & XC).
      unfold byte_at. rewrite PR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact XC].
    - intros x Hx. pose proof (hish_rng x Hx) as X.
      unfold byte_at. rewrite PR; [exact (di_hish _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx].
    - rewrite (model_rt_rdr _ _ RT). exact (di_rdr _ _ _ _ _ _ D).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma amalloc_site : forall vals ebs sr kn R M (model : Model) LB LK cr A n so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 4 = Z_to_bv 64 0x693b00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A' (u : Z),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 u ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (kn_blkA (length vals + 10) n ++ keep_allocA so 4096 bls vbnd kn) ->
       dinv ((u, n) :: LB) LK (adebit L cr n) A' M' model' -> model_rt model model' -> incl A A' ->
       ablock_range L ar u n -> blocks_apart u n LB -> shadow_blk M' u n ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x80740) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    pose proof (aiob_malloc _ _ _ _ _ HIok fx R M model LB FF LK cr A n K) as MS.
    cbv zeta in MS. rewrite (dla_segs DL), (dla_malloc DL), (dla_tp DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
    - unfold amalloc_post. intros R' M' model' A' u HA HP HBR HAP HFA HDEF HSHB HPRES HRT HINC HMI' HH'.
      rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 u) by (rewrite vals_ev_junkA by lia; exact HA).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_malloc L) a)
        by (intros a; apply aclient_scr_mono; lia).
      apply (CONT R' M' model' A' u HL' HA'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) apply Forall_app. split.
        * eapply kn_blkA_ok; [exact HA' | exact P0' | exact HBR |].
          intros i Hi. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH'); [apply HDEF; exact Hi | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; lia |].
          right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
        * unfold keep_allocA.
          pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
          refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                    (Env (vals_ev (vals ++ junk_vals R')) ebs)
                    (CPa LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                    _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
          -- eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB ((u, n) :: LB) FF FF LK LK cr (adebit L cr n) A A' M M' model model');
               [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
             ++ intros a Ha; exact Ha.
             ++ intros a (b & Hb & Hr). exists b. split; [right; exact Hb | exact Hr].
             ++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
             ++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
          -- intros a HS. unfold SCa in HS. unfold mrestrict.
             rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
             destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_malloc L)) as [Hlo|Hhi].
             ++ rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
                unfold aclient. right. left. rewrite (dla_sptop DL). lia.
             ++ apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB LB ((u, n) :: LB) LK LK cr (adebit L cr n) A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_malloc L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin Ha)].
  Qed.
  Lemma in_lb_remove_in : forall u (LB : list (Z * Z)) b, In b (lb_remove u LB) -> In b LB.
  Proof.
    intros u LB b. induction LB as [|c LB' IH]; [intros []|]. cbn [lb_remove].
    destruct (Z.eqb (fst c) u); [intros H; right; exact H|]. intros [<-|H]; [left; reflexivity | right; apply IH; exact H].
  Qed.
  Lemma in_block_remove : forall u LB a, in_block (lb_remove u LB) a -> in_block LB a.
  Proof. intros u LB a (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma afree_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (u n : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    In (u, n) LB -> getr R 10 = Z_to_bv 64 u ->
    getr R 4 = Z_to_bv 64 0x693b00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA (lb_remove u LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinv (lb_remove u LB) LK cr A' M' model' -> model_rt model model' -> incl A A' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block (lb_remove u LB) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x8073c) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A u n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    pose proof (aiob_free _ _ _ _ _ HIok fx R M model LB FF LK cr A u n K) as MS.
    cbv zeta in MS. rewrite (dla_segs DL), (dla_free DL), (dla_tp DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
    - intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
      rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 a ->
                              aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
        by (intros a; apply aclient_scr_mono; lia).
      apply (CONT R' M' model' A' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove u LB) LB (lb_remove u LB) FF FF LK LK cr cr A A' M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact (in_block_remove u LB a Ha).
          -- intros a Ha; exact Ha.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
          -- rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
             unfold aclient. right. left. rewrite (dla_sptop DL). lia.
          -- apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB (lb_remove u LB) (lb_remove u LB) LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.

  Lemma rdn_of_bytes_at : forall (Mx : word -> option byte) n (a : word) bs,
    length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall j, (j < n)%nat -> Mx (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
    rdn ASEGS Mx a n = Some bs.
  Proof.
    intros Mx n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
    - destruct bs; [reflexivity | cbn in Hlen; lia].
    - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen. cbn [rdn].
      pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
      rewrite H0.
      destruct n as [|n']; [destruct bs'; [reflexivity | cbn in Hlen; lia]|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      rewrite (IH (a + 1)%bv bs'); [reflexivity | lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (Datatypes.S j)) by lia.
      exact (Hpt (Datatypes.S j) ltac:(lia)).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma aacc_of_blkA : forall M u n p m, shadow_blk M u n -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + n -> aacc M p m.
  Proof.
    intros M u n p m [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
    assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
    destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
    - left. rewrite E. apply SZ. lia.
    - right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
      split; [rewrite E, G; apply SP; exact NZ | lia].
  Qed.
  Lemma u16_u8 : forall u, u mod 16 = 0 -> u mod 8 = 0.
  Proof. intros u H. lia. Qed.
  Lemma S_mono : forall a b, a <= b -> S a <= S b.
  Proof. intros a b H. unfold S. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma src_blk_aacc : forall LB FF LK cr A M V (As caps src n : Z),
    ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> aacc M src n.
  Proof.
    intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (As, caps) Hin) as (HBR & _ & HSB & _). cbn [fst snd] in HBR, HSB. destruct HBR as (B1 & _ & B3 & _).
    apply (aacc_of_blkA M As caps src n HSB (u16_u8 _ B3)); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma src_blk_app_rng : forall LB FF LK cr A M V (As caps src n : Z),
    ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> app_rng ar src n.
  Proof.
    intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (As, caps) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & _ & _ & _ & B5 & (_ & BAM & _)).
    unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
  Qed.
  Lemma src_stage_app_rng : forall (src n : Z), 0x6820d0 <= src -> src + n <= 0x6920d0 -> app_rng ar src n.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvLib ()) ["FPX_1"; "DrvLayoutA"] "h02Hah14__p1h24__p2h34__x1h44__x2h51Hh62H1h72H2h87__arithh94__ffh:6__sat3h;6__sat4h<6__sat5h=8__varmaph>5__with?1nh@3srchA1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8p1002lp4p70g003\R0p4p710R1p8p1004:p4p70P1p8p100GSp4p70P1p8p1004hp4p710P1p8p1005Cp4p710P1p8p1006Dp4p70P1p8g00?cj16Tg00MMj21Tg00ZEj27Tg00?>j10Tg00>;j1BTg00LFj2JTg00KMj2hTg00Toj2?Tg00Nhj2ATg00Zbj2XTg00Kjj2ITg00[Jj3VTg00[nj2UTg00\_j2TTg008<j1RTg00HNj1QTg00]?j2PTg00g4j1OTg00gRj4NTg00]]j1MTg00^;j1LTg00_Ij2CTg018Zj3DTg00^fj2:Tg00a3j1KTg00_lj3STg00aUj2gTg00=aj2fTg00b7j2eTg00::j3cTg00bcj3bTg00cBj4^Tg00XHj1]Tg00f4j1\TP0j6[Tg05XWj3ZTg00>Yj13Tg00hlj4YTg00iWj7_Tg00j_j6`Tg01@Lj7aTg00`Oj7WTg00j;j8dTf0R0#3#0p=4%00#0#0#0p=2%30#3p=@%00#3p=>%00#0p=9%30#3#3#3p=8%00#0#0#0#0#0#0#0p=;g00kCR1/10p=5g00;nR2f1R3g00kaP0CYp=<P3g00lHR4g00lgR5P5g00mGR6P0g00mgF_p==P3P4P5P5P6P0E`p=Ef2R7P4P5P5P6P3P0Fap=HP7P4P5P5P6P3P0FWp=Ff3R8P4P5P5P6P7P3P0Gdp=Gg00FPR4#4#4#2#4#2#@#>#2#6R9/13R:1773%44#4#>#9#4#2#@#>#2#6R;'1p,3Hsp%@4#8#8#8R<#4#9#2#;#;#;#6%04R=#0#9R>#9R?#Bp,3sp0'JR@'1%6=RA%8=RB#6RC'hRD,1@'?P2P@f5RE#5f4RF,7ERG%><#@#2#;#6R<'1%9?#2#>#@#8#8#8#4#9#2#;#6R?/1E'A11G0%6>R>,7G/1D'A'?'?XA21XAC1I1A%5C1I1D[[%5ARGg00<iRHAVAC3UW0%5D\H^0G1U@>%5@%5>1T@>#5[[p-0RGg013?RH#R%QHP21P27P3%O2CN%M2%L2RH1C24R41C2=5D2R=1:2;'<,=H%K5R5PH1:29/<4,=HP51:21/<4,=H1:2<,<=,=H1EHF5HH1EHE1:2>9D2=1:2A%BB5S2'<,=H5HH5FH5FHCGCG1gH6P0P7g00D;RHg00D[R6'f1e07=cH6dAb213C^b9b=b>X32X42X1GW21703/1;%571778R7/1</AF177>/1D,AE'?'?\:[^32^42^1G^2GP0f8R0f7RG'7/1@11?0PGP0PEf6O6b8b:b;b<p,2arRE#]p,2DL#\E[AZEF8eb5W7W6X?2X@2o"). Qed.
  (* [comment removed for export] *)
  Lemma src_stage_aacc : forall LB FF LK cr A M V (src n : Z),
    ri_inv HI LB FF LK cr A M V -> 0x6820d0 <= src -> src + n <= 0x6920d0 -> aacc M src n.
  Proof.
    intros LB FF LK cr A M V src n HH H1 H2 a Ha. left.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH src n) as (Z0 & _).
    - rewrite (dla_img_lo DL). lia.
    - rewrite (dla_img_hi DL). lia.
    - lia.
    - rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply Z0. unfold in_shadow_of. split; apply S_mono; lia.
  Qed.

  Lemma aclient_remove : forall u LB FF sp scr a, aclient L ar (lb_remove u LB) FF sp scr a -> aclient L ar LB FF sp scr a.
  Proof.
    intros u LB FF sp scr a Hc. unfold aclient, aclient_g in *.
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; [left; exact (in_block_remove u LB a Hc) | tauto | tauto | tauto | tauto | tauto |].
    right. right. right. right. right. right. destruct Hc as (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr].
  Qed.

  Lemma ablock_range_prefix : forall u n nb, ablock_range L ar u n -> 0 < nb <= n -> ablock_range L ar u nb.
  Proof. intros u n nb (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)) Hnb. unfold ablock_range, app_mem. repeat split; lia. Qed.

  (* [comment removed for export] *)
  Lemma kn_blkA_of_inv : forall vals ebs LB LK cr A M (model : Model) v (u cap nb : Z),
    let E := Env (vals_ev vals) ebs in
    dinv LB LK cr A M model -> In (u, cap) LB -> 0 < nb <= cap ->
    vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
    know_ok ASEGS E (mrestrict (ahid A model) M) (kn_blkA v nb).
  Proof.
    intros vals ebs LB LK cr A M model v u cap nb E D Hin Hnb Pv P0.
    pose proof (di_inv _ _ _ _ _ _ D) as HH.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (u, cap) Hin) as (HBR & HDEF & _). cbn [fst snd] in HBR, HDEF.
    eapply kn_blkA_ok; [exact Pv | exact P0 | exact (ablock_range_prefix _ _ _ HBR Hnb) |].
    intros i Hi. unfold mrestrict.
    rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH); [apply HDEF; lia | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; pose proof Hsp; lia |].
    right. right. exists (u, cap). split; [exact Hin | cbn [fst snd]; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma amemcpy_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (Ad capd dst src n : Z) (bs : list byte) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 dst -> getr R 11 = Z_to_bv 64 src -> getr R 12 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    getr R 4 = Z_to_bv 64 0x693b00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    In (Ad, capd) LB -> Ad <= dst -> dst + n <= Ad + capd ->
    aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> 0x10000 <= src + i < 0x6b6000 \/ in_block LB (src + i)) ->      (* [comment removed for export] *)
    rdn ASEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (dst + n <= src \/ src + n <= dst) ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA (lb_remove Ad LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinv LB LK cr A M' model' -> model_rt model model' ->
       rdn ASEGS M' (Z_to_bv 64 dst) (Z.to_nat n) = Some bs ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x7ebb8) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A Ad capd dst src n bs so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R11 R12 Hn R4 R1 Hra Hra2 DI Hin Hd1 Hd2 Hacc Hs0 Hs1 Happ Hsrc Hrd Hdj Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (Ad, capd) Hin) as (HBR & HDEF & HSB & _ & HAP & _). cbn [fst snd] in HBR, HDEF, HSB, HAP.
    pose proof (hzA_of_block_range _ _ HBR) as (Y1 & Y2 & Y3). pose proof HBR as (_ & _ & B3 & _ & _ & (_ & BAM & _)).
    assert (INB : forall i, 0 <= i < n -> in_block LB (dst + i)).
    { intros i Hi. exists (Ad, capd). split; [exact Hin | cbn [fst snd]; lia]. }
    pose proof (aic_memcpy_libc _ _ _ _ _ ICok fx R M model LB FF LK cr A dst src n bs K) as MS.
    unfold amemcpy_libc_spec, amemcpy_spec_at in MS. rewrite (dla_segs DL), (dla_memcpy DL) in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) unfold amem_pre. rewrite (dla_tp DL), (dla_segs DL), R1, R2, u_small by lia.
      split; [exact HH|]. split; [exact Hh|]. split; [exact HMI|]. split; [exact R10|]. split; [exact R12|]. split; [lia|].
      split; [exact R4|]. split; [apply ret_ok_even; rewrite u_small by lia; exact Hra2|].
      split; [eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia|].
      split; [apply (aacc_of_blkA M Ad capd dst n HSB (u16_u8 _ B3)); lia|].
      split; [intros i Hi; left; exact (INB i Hi)|].
      split; [|split; [exact HK0 | unfold app_rng; rewrite (dla_sptop DL); lia]].                      (* [comment removed for export] *)
      intros i m Hi Hm. destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (HDEF (bv_unsigned x - Ad) ltac:(lia)). replace (Ad + (bv_unsigned x - Ad)) with (bv_unsigned x) in HDEF by lia.
      rewrite Z_to_bv_bv_unsigned in HDEF. unfold wview. destruct (M x); [discriminate | exfalso; apply HDEF; reflexivity].
    - split; assumption.
    - intros i Hi. destruct (Hsrc i Hi) as [X|X]; [left; rewrite (dla_img_lo DL), (dla_img_hi DL); exact X | right; left; exact X].     (* [comment removed for export] *)
    - intros _. exact Hdj.
    - (* [comment removed for export] *) unfold amem_post. cbv zeta. intros R' M' model' HA HP HNEW HPRES HSCR HRT HMI' HH'.
      rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES, HSCR by lia.
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      (* [comment removed for export] *)
      assert (NDST : forall a, aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> ~ (dst <= a < dst + n)).
      { intros a Hc Hr. unfold aclient, aclient_g in Hc. rewrite (dla_img_lo DL), (dla_img_hi DL), (dla_sptop DL) in Hc.
        destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
        - destruct Hc as (b & Hb & Hbr). destruct (HAP b Hb) as [Q|Q]; lia.
        - lia.
        - lia.
        - destruct Hc as (f & [] & _).
        - unfold in_shadow_of, S, SB in Hc. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
          assert (D0 : 0 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_pos; lia).
          replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) in Hc by ring.
          change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in Hc. lia.
        - destruct Hc as (f & [] & _).
        - destruct Hc as (b & Hb & Hbr). pose proof (in_lb_remove_in _ _ _ Hb) as Hb'.
          destruct (WF b Hb') as ((C1 & _ & _ & C4 & C5 & (_ & _ & C8)) & _).
          unfold in_shadow_of, S, SB in Hbr. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
          assert (D0 : 0 <= fst b / 8) by (apply Z.div_pos; lia).
          assert (D2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
          change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2. lia. }
      assert (PR1 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hc. apply HPRES; [exact Ha | | exact (NDST a Hc)].
        apply (aclient_scr_mono _ _ _ 4096 (hl_scr_mem L)); [lia|]. exact (aclient_remove Ad LB FF _ _ a Hc). }
      apply (CONT R' M' model' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A model') M') _ _ kn HK1).
        * eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove Ad LB) LB LB FF FF LK LK cr cr A A M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact (in_block_remove Ad LB a Ha).
          -- intros a Ha. exact (in_block_remove Ad LB a Ha).
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; assumption.
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_mem L)) as [Hlo|Hhi].
          -- rewrite HPRES; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia | | lia].
             unfold aclient. right. left. rewrite (dla_sptop DL). lia.
          -- apply HSCR. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB (lb_remove Ad LB) LB LK LK cr cr A A M M' model model' (bv_unsigned sp0 + so) 4096 DI ltac:(lia)); assumption.
      + (* [comment removed for export] *)
        pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
        apply rdn_of_bytes_at; [exact Hlen | rewrite u_small by lia; lia |].
        intros j Hj. rewrite u_small by lia.
        destruct (HNEW (Z.of_nat j) ltac:(lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id in Hnth.
        unfold byte_at in Hb. rewrite Hb. f_equal. symmetry. apply nth_error_nth. exact Hnth.
      + (* [comment removed for export] *) intros a Ha Hb Hnd. apply HPRES; [exact Ha | left; exact Hb | exact Hnd].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
  Qed.
End DrvLayoutA.
End FPX_1.
End Na0DrvLib.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.
Module Na0DrvRead.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0ReadIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvRead () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init6Specif7sumbool00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt3RDAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt7RDA_outC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic3and00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib7Mh_0116:As0DrvKitAEmrestrict_munrestrictC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib=SymExec2Sound4SX2S:wbytes_outC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib7Mh_0119:Na0DrvRead5STAGEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt9RDA_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead;rd_M2_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffc59OSSVerify5KrLib7Mh_0119:Na0DrvRead=rd_MV2_framesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx<aiob_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9asc_cellsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_segsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead8RD_CELLSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4woffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct<range_avoidsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA>aic_img_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0119:Na0DrvRead>vis_of_allowedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsigned".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition RD_CELLS : list (Z * Z * Z) :=
  [(0x160758, 1, 1); (0x158bf0, 8, 0x14f76c);
   (0x156d98, 8, 0x15fa78); (0x15fa78, 8, 0x7fff8000); (0x156da0, 8, 0x160768); (0x160768, 8, 0); (0x156da8, 8, 0x160770); (0x160770, 8, 0);
   (0x156db0, 8, 0x160760); (0x160760, 8, 0x7fffffffffff)].

Definition STAGE : Z := 0x6820d0.
(* [comment removed for export] *)
Definition IMG_NOSTAGE : list (Z * Z) :=
  [(0x10000, 0x158000); (0x15b4b8, 0x15c3a0); (0x6920d0, 0x693aa8); (0x693ab0, 0x693af8); (0x693b14, 0x693b28); (0x693b30, 0x6b4fb8);
   (0x6b4fc0, 0x6b6000)].
Definition keep_readA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ReadMem.
  (* [comment removed for export] *)
  Variable H : word -> bool.
  Variable M : word -> option byte.
  Variables (s : Z) (raw : word) (R : bvmap 5 word) (bs : list byte).
  Hypothesis Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64.
  Hypothesis Hbs : Z.of_nat (length bs) <= 65536.
  Hypothesis Hvis_fr : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false.
  Hypothesis Hvis_st : forall x : word, STAGE <= bv_unsigned x < STAGE + 65536 -> H x = false.
  Hypothesis Hfar : STAGE + 65536 <= s - 2200.

  Let MV := mrestrict H M.
  Let Ma := RDA MV raw s R.
  Let M1 := munrestrict H M Ma.
  Let M2 := wbytes M1 (Z_to_bv 64 STAGE) bs.
  Let MV2 := mrestrict H M2.

  Definition rd_M1 := M1. Definition rd_M2 := M2. Definition rd_MV2 := MV2.

  Lemma rd_M1_restrict : mrestrict H M1 = Ma.
  Proof.
    apply mrestrict_munrestrict. intros a Ha. unfold Ma.
    destruct (Z_lt_le_dec (bv_unsigned a) (s - 2144)) as [L1|L1]; [rewrite (RDA_out MV raw s Hs R a) by lia; unfold MV, mrestrict; rewrite Ha; reflexivity|].
    destruct (Z_lt_le_dec (bv_unsigned a) s) as [L2|L2]; [rewrite (Hvis_fr a) in Ha by lia; discriminate|].
    rewrite (RDA_out MV raw s Hs R a) by lia. unfold MV, mrestrict. rewrite Ha. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_M2_out : forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> ~ (STAGE <= bv_unsigned x < STAGE + 65536) -> M2 x = M x.
  Proof.
    intros x N1 N2. unfold M2. unfold STAGE in *.
    rewrite wbytes_out by (rewrite u_small by lia; lia).
    unfold M1, munrestrict. destruct (H x) eqn:Hx; [reflexivity|].
    unfold Ma. rewrite (RDA_out MV raw s Hs R x) by lia. unfold MV, mrestrict. rewrite Hx. reflexivity.
  Qed.
  Lemma rd_M2_grows : forall x : word, M x <> None -> M2 x <> None.
  Proof.
    intros x Hd. unfold M2. apply wbytes_grows. unfold M1, munrestrict. destruct (H x) eqn:Hx; [exact Hd|].
    unfold Ma. apply RDA_grows. unfold MV, mrestrict. rewrite Hx. exact Hd.
  Qed.
  Lemma rd_MV2_grows : mem_grows MV MV2.
  Proof.
    intros x Hd. unfold MV2, mrestrict. unfold MV, mrestrict in Hd. destruct (H x) eqn:Hx; [exact Hd|]. apply rd_M2_grows. exact Hd.
  Qed.
  (* [comment removed for export] *)
  Lemma rd_MV2_frames : forall x : word, s - 2200 <= bv_unsigned x < s -> MV2 x = Ma x.
  Proof.
    intros x Hx. unfold MV2, mrestrict. rewrite (Hvis_fr x Hx). unfold M2, STAGE in *.
    rewrite wbytes_out by (rewrite u_small by lia; lia).
    unfold M1, munrestrict. rewrite (Hvis_fr x Hx). reflexivity.
  Qed.
  Lemma rd_MV2_slot : forall k, 8 <= k <= 2200 -> rdn ASEGS MV2 (Z_to_bv 64 (s - k)) 8 = rdn ASEGS Ma (Z_to_bv 64 (s - k)) 8.
  Proof.
    intros k Hk. apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. cbn in Hx.
    apply rd_MV2_frames. lia.
  Qed.
  Lemma rd_stage_bytes : rdn ASEGS M2 (Z_to_bv 64 STAGE) (length bs) = Some bs.
  Proof. unfold M2. apply rdn_wbytes_hit. unfold STAGE. rewrite u_small by lia. lia. Qed.
End ReadMem.

Section DrvRead.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).

  #[local] Notation dinvA := (dinv ar HI sp0 M0).

  Lemma rd_cell : forall LB FF LK cr A M V a n v, ri_inv HI LB FF LK cr A M V -> In (a, n, v) RD_CELLS ->
    cell_is ASEGS M a (Z.to_nat n) v.
  Proof.
    intros LB FF LK cr A M V a n v HH Hin.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    exact (proj1 (Forall_forall _ _) CS (a, n, v) (Hcells _ Hin)).
  Qed.

  (* [comment removed for export] *)
  Lemma avoid_img : forall LB FF LK cr A M (model : Model) a (n : nat),
    ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a -> a + Z.of_nat n <= 0x6b6000 ->
    range_avoids (ahid A model) (Z_to_bv 64 a) n.
  Proof.
    intros LB FF LK cr A M model a n HH Ha Hn k Hk. unfold woff. rewrite (u_small a) by lia.
    apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (a + Z.of_nat k) HH); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vis_of_allowed : forall A (model : Model) a n x, shadow_allowed A a n -> in_shadow_of a n x -> ahid A model (Z_to_bv 64 x) = false.
  Proof.
    intros A model a n x SA Hx. unfold ahid, mkH. rewrite (SA x Hx). apply andb_false_r.
  Qed.

  (* [comment removed for export] *)
  Lemma stage_shadow : forall LB FF LK cr A M (model : Model), ri_inv HI LB FF LK cr A M (vml_of model) ->
    forall x, in_shadow_of 0x6820c0 0x10050 x -> byte_at M x 0 /\ ahid A model (Z_to_bv 64 x) = false.
  Proof.
    intros LB FF LK cr A M model HH x Hx.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x6820c0 0x10050) as (Z0 & SA).
    - rewrite (dla_img_lo _ _ _ _ DL). lia.
    - rewrite (dla_img_hi _ _ _ _ DL). lia.
    - lia.
    - rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - split; [exact (Z0 x Hx) | exact (vis_of_allowed A model _ _ x SA Hx)].
  Qed.

  Lemma w_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
  Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Lemma rd_post : forall LB FF LK cr A M (model : Model) (s : Z) (raw : word) R R2 bs,
    let H := ahid A model in
    let MV2 := rd_MV2 H M s raw R bs in
    let n := Z.of_nat (length bs) in
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    n <= 65536 -> bv_unsigned sp0 - 4194304 - 4096 <= s <= bv_unsigned sp0 ->
    store_ok ASEGS (mrestrict H M) (Z_to_bv 64 (s - 2200)) 2200 = true ->
    ret_ok raw ->
    getr R2 10 = Z_to_bv 64 n -> getr R2 2 = Z_to_bv 64 (s - 2144) -> getr R2 1 = (0x14f794%bv : word) ->
    getr R2 8 = Z_to_bv 64 s -> getr R2 9 = Z_to_bv 64 0x6820d0 -> getr R2 20 = Z_to_bv 64 1 ->
    exists R3 M3',
      msteps ASEGS (mkst R2 (0x149d44%bv : word) MV2 (seg_rom ASEGS)) (mkst R3 raw M3' (seg_rom ASEGS))
      /\ getr R3 10 = Z_to_bv 64 n /\ getr R3 2 = Z_to_bv 64 s /\ getr R3 1 = raw
      /\ getr R3 8 = getr R 8 /\ getr R3 9 = getr R 9 /\ getr R3 18 = getr R 18 /\ getr R3 19 = getr R 19 /\ getr R3 20 = getr R 20
      /\ keeps_but OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0ReadIcpt.RIPL R2 R3
      /\ (forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> M3' x = MV2 x)
      /\ mem_grows MV2 M3'.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0119 ()) ["FPX_1"; "DrvRead"] "p'0p'1h04__x1h14cstrh25heq_nh33Hinh42H0h54__x2h61xi001xh77__arithh88__varmaph95__with:4__ffh;7__sat22h<7__sat23h=7__sat24h>7__sat25h?4__p1h@7__sat21hA4__x3hB3M3'hC2R3hD4__x4hE4__p2hF7__sat66hG7__sat67hH7__sat68hI7__sat69hJ7__sat70hK7__sat71hL7__sat72hM6heq_fShN6heq_lShO7__sat65hP4__x5hQ4__p3hR7__sat26hS7__sat73hT1ahU4__p4hV1vhW1bhX2HxhY4__x6hZ2H1h[2H2h\2H3h]2H4h^2H5h_2H6h`2H7ha2Hahb4__p5hc1ohd1zi011zhe3H21hf4__p6hg1ei021ehh3z21hi3Hx0hj2_Hhk7__sat74hl1ni031nhm3Hj0hn2M'ho4__x7hp5cstr0hq5regs'hr1yhs2w1ht2Hjhu2KBhv2O1hw3O10hx3O18hy3O19hz2O2h{3O20h|2O8h}2O9h~3Q10i043RUNi054__p7i064__x8i071ji081mi092w0i0:1Ai0;2BZi0<3CV2i0=2D1i0>3DL0i0?2DMi0@2DVi0A2FAi0B2FFi0C2GRi0D1Hi0E2HHi0F3Hbsi0G4Hfari0H2Hni0I3Hn0i0J4Hn64i0K3Hnpi0L3Hnzi0M4Hreti0N2Hsi0O4Hsp'i0P3Hsri0Q2L0i0R2L1i0S2LAi0T2LBi0U2LKi0V1Mi0W2MBi0X3MV2i0Y2N1i0Z2N2i0[2Nxi0\2OAi0]1Qi0^2Q1i0_2Q2i0`3Q20i0a2Q8i0b2Q9i0c1Ri0d2R2i0e2RAi0f3SHZi0g3SL1i0h3SL2i0i3SL3i0j3SL4i0k3SL5i0l3SL6i0m3SL7i0n2T1i0o2T2i0p2T3i0q2T4i0r2T5i0s2T6i0t2T7i0u3VFRi0v3VSTi0w2VZi0x3WOKi0y2XOi0z7__sat27i0{7__sat28i0|2bsi0}2cri0~2fSi102lSi115lemmai125modeli133rawi141si152s0i161pp%0p%1p%2p%3p%4p%5p%6p%7p&0p&1p&2p;1p;2p;5p;3p;4p;6p;8p;Dp;;p;Ep;7p;<p;:p;9p;Qp;Bp-1R0p10000p4p710p9P0g01U?R1p4p710p9P0p1001?R2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g01V1R2p4p710p9P0g002UR3p4p710p8p1002lp4p70g003\R4p4p710R5p8p1004:p4p70P5p8p1004hp4p70P5p8p1005cp4p710P5p8p1006>p4p710P5p8p1007?p4p70P5p8g0085j15Tg008Zk10nTg00:@S00j1LTg009[j19Tg00:^j1;Tg00;=k12DTg00AKk21QTg00>^k122Tg00;fk11~Tg00<Qk21UTg00?Ak21mTg00=4k51rTg00@AS01k21jTg00QWj30k119Tg00D3R5j27Tg01Vlk115Tg01WJk21gTg00HiR6j2:Tg01Wck42ZTg00HIR7j1jTg00WfR8j2ITg01XFk12STg01Xdk22RTg01YEk30~Tg00LJj2qTg0098k11aTg00@aj2>Tg00?dk21JTg00=Xk31ITg01YnR9k12CTg01ZNk21[Tg01Zkk21ETg01;kk404Tg00C4j2GTg00CQk11YTg00Gik10_Tg00DOk20WTg00IFj2ATg00WKR:j21Tg00XBS02j24Tg00GIk11lTg00Jlk11zTg00KJk11yTg00Khk21wTg00Ldk21tTg00Mok41sTg00F=k21>Tg00Fek31=Tg00ELk21<Tg00^:k11RTg01[Hk21pTg00Uhj2lTg01[jk21:Tg01\[k31oTg01]:k11PTg01]fk41OTg01^Gj2DTg01_3j22Tg01_ek21kTg01`mk22`Tg013^k116Tg00Zlk22_k32ATg01aMk20kTg01bLk41iTg01cHk31hTg01dIk32^k42NTg01eDk62]Tg01fBk12\Tg01g7k514Tg00R1k11eTg00Rok82[Tg00Ilk42YTg01gik12XTg00Smk21MTg00YPmD1LTg01hbk210Tg018\j6~k71HTg01iTk52TTg00h>S03j28Tg01jVm;0MTP4j6sTg01kYk22QTg00^\k10OTg01l9S04k22PTg01lYmE2OTg01mek206Tg00ZQk40ATg00n]k40XTg01ncm;2MTg01odk52LTg020ck12KTP1k32JTg021Tk12ITg022Ck62GTP2k72FTg022nm<2ETg013Ak61_Tg023mm<0zTg024Rk40cTg0259k41FTg014Ck20LTg025dk61]Tg026Mk72BTg00d;k32?Tg027Bm:2>Tg028Fk31DTg029Ek50tTg00X\k31CTg029jk62=Tg02:nk72<Tg02<0j5FTP3k303Tg02<Mk12:Tg02=[k329Tg02>Bk328Tg02>ck21XTg02?@k21WTg02?lk227Tg02@Uk326Tg02A>k325Tg02AaR3k22;Tg02B9k424Tg02BUk41STg02C4k41TTg02CPm91ZTg02DVk421Tg02EUk31ATg02FWk412Tg02GXk50FTg02HSmQ20Tg01<Kk30|Tg01:9j4bTg01:dj7_Tg01AQk61}Tg01>Dk32HTg02I^k31VTg01;Hk30{Tg01=4k21`Tg01?Kk30}Tg00MPk31|Tg02JAm<1cTg01=`k70NTg01?kk80STg00]\k21{Tg01@Ok40gTg01@mk62UTg02Jfk41fTg01>gk72WTg02KWk311Tg02L_k31dTg02M[mB1vTg00Y6k31NTg02NAk31uTf0R2#5#5p>0a%52#5#5#5p=\%52#5#9#9p>0d%52#5#5#Lp=O%;2#;#;#;p>23%;2#;#;#;#;#;#;#;p>1x%;2#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;p=6%52#9p=x%52#9#5#5p=h%52#5#5#9p>0T%92#5#9#5p>0\%92#9#9#9p>0j%92#9#9#9#9#9#9#9p>0h%52#5#5#5#5#5#5#5p>0f%92#9p>0Cg01B5R1/I2p=c1712p=@g01BSR401Q2p=uf2R;f1R<>0|4260|4p>02%52#Lp>0w21m42p=pP;g01C1R=g01CPR>P>g01D0R?P4P<g01DPR@P2Cbg01E7RAF_p=E%52#9#9#5p>0p%92#9#5#5p>0JP;P=P>P>P?P4P<g02O>RBP2CbPAF_p>05P<P=P>P>P?P2J1}p=|P;P=P>P>P?P4P<g01EWRCP2CbPAF_p=e%92#9#9#5p>0H%92#5#9#9p>0;%92#5#5#9p>0]%92#9#5#9p>0E%92#5p>18%92#5#5#5p>0m1q42p=TA04<2p==B0|4<2p=o%52#5#9#5p>0eB2H4<2p=m%L2g02OeRD61V<p>0@B1V<2Dp=t21U42p=Nf3RDP4P4P4P;P<H04P2H04p=wP4P4P<P2H04p>0:P<P4P2P1H04p>0lB0{4<2p=VB0|4<2g01F>RE+1`p>1BA0421p=gg01FjRF21`<E<0}2p=^PDP=P>P>P?P4B0{4;<P@P2CbPAF_p>1Kf4RE/7D1:;</72'1p=M1I<2,1;p=]B1|412p>0rg01SCS05,42p>01f6RGf5RH;0EA0D;</42'4p>00B0};<2:0}EDp>0^A0D;</42p>1@1:;</72p>0=g01KYS06P4P4P4P7P7PHPEPDP;P<P2N<1cp>1?PEP=P>P>P?PDP=P>P>P?P4P;P@P<CbPAF_P2K0Np>0o17;</12p=KP4P<P@P2Cbp>0UPDP=P>P>P?P;P<P=P>P>P?P2PAF_K0Np>0IP;P=P>P>P?P<P2K0Np=HP4Q06P4P4P9PEP7PDg02PAP;P<P2N<1cp>1qPGP=P>P>P?PHPEPDP=P>P>P?P;P<P2L0SL0Sp=<21k<2,l;p=k21{42p>0GP4P;P<P2H0gp=aP4P4PEPDP;H0gP<P2H0gp=}P<P=P>P>P?P2J2Up=fPHP=P>P>P?PEP=P>P>P?PDP;K0NP<P2L0Sp=QPDP=P>P>P?P;P<P2L0Sp=rP4PEPDP4P;P<P2H0gH0gp>1n1G;</72p>171G<2,A;p>0B12;<=0D2p=Xg01L8S07P;P<P2H1fp=J17D;1I<2'1$0Op=B206<2,1;p>13Q07PDP;P<H1f=0E2p=ZA0D;</12p=n17<2,1;p=zPGP=P>P>P?PHP=P>P>P?P4PEP@PDCbPAF_P;P=P>P>P?P4P<P@P2CbPAF_K0Np=v17D;17<2'1p=U1GD;/7</12p>0717D;1I<2'1p>0Zg01GVS08g01HVS09702p>0RP;P=P>P>P?P<P2K2Wp>0814<2,4;p>2Vg02PnR9/72p>0Y11<2,1;p>0Q11<2,1;,1D,1Ep=[f7RI?0GHg02QkRJ@11ED206<2,1;'1'1p=`12D;=0E</12p=?A0IGH12D;=0E</12'1p=dA0GHEA0D;</12'1p=3Q07PHPEPDP;P<I1481dG/12p=CB11JED206<2,1;'1p=iB11J<2p={Q07PEPDP;P<P2I1481dHp>1bB11J;</12p>0PPGPHPEPDP;P<P2H0AH0Ap=WP4P<PBP2Cbp>0[PEP=P>P>P?PDP=P>P>P?P;PAF_P<P2L0Sp>0KPHP=P>P>P?PEP=P>P>P?P4PDP@P;CbPAF_P<P2L0Sp>0<1I<2,1;$0Op>0bg02Rh:03<2p=yPEP4PDP;P<P2J1_p=SP;P4P<P2H0490EDp>0yPDP4P4P4P;P<H04P2H0490HEp=PP4PHPEPDP;P<P2K1Hp=YPIP=P>P>P?PGP=P>P>P?P4PHP@PECbPAF_PDP=P>P>P?P4B0{4;<P@P2CbPAF_K0Np>09A0412p>0xP4P4P4P4P4P4P6P2P<P;P6PDPEPHPGPIf8R6f9RBNB1vp>0iP4P4P5PIP5PGPHPEPDP;P<P2N<0zp>1GP4PEPDP;P<P2Esp>0DP4P4P8PIP8PGPHPEPDP;P<P2N<0zp>1^P4P<PCP2Cbp>0qP4B0{4;<P@P2Cbp>1;PHP=P>P>P?PEP=P>P>P?PDPAF_P;P=P>P>P?P4P<P@P2CbPAF_K0Np>2@PEP=P>P>P?PDP;P<P=P>P>P?P2PAF_L0Sp>0s1q<2:1CD;p>0`B1N;<2:1NEDp=RB1C;<2:1NEDp>0u1><2,q4p>0?PIPGPHPEPDB1u;<2E~p>0>B0}F<2p>0v1l<290D;p>0VQ06P4P3P7P8g02ShPHPEPDP;P<P2N<0zp>1\g01I6R8#5R7#5R3#5S0:#5RA#5R@#5RC$0ng01I[R5Q0:$0nP5%5C$0aS0;#5$0aR5#\RJ#LP4&0aJ#\RJ#LP4%L5P4Q0:#9$0d#OP4g01J^R5#;RK#;RL#;RM#;RN#;RO#;RP#;RQ#;RR#;S0<#;RS#;RT#;$23$1x#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6#6Q06Q0:#LP4%98#x#\#h$0T$0\#OP4%98RU#9S0=$0j$0hRV#9RW#5$0a#\$0fRX#5#\$0f#OP4%97RY#9S0>$0Cg01J9S0?%L7RZ#cp-0R[%@ZP[%LCP4%LAP4%uL&2D4RL%uKRK%uMS0@21Q45S0A402PL%5JRJ$0wP4%uPPL%pY&224RP&1~4R521U41RM21m48RC3EP5P=P>P>P?I1rR=%LJP4%98#x$0p$0J$0f#OP4%5URJ#5R\#5R]#LP4%L@P4%5YR@#5R^#5Q0?&0w]P4%9ARA#5$0C#OP4B055CM,|5P=Ae5MCP=%58$0J#\$0H$0;#OP4%58$0;$0T#x$0C$0H#OP4%58$0]$0C$0;$0;$0p$0wP4%58$0\$0E$0;$0d#OP4%58$0;$0j#h$0j#OP4%LXP4%58$0\$0E$0;#h#OP4%58$0J#\$0H$0E#OP4%58$18$0;$0p$0E#x#OP4%58$0J#\$0H$0H#OP4%58$0\$0E$0;$0p#OP4%58$0J#\$0H$0J#OP4%9W$0C$0j$0h$0h$0h#LP4&18@#\$0f#OP4%58$0C#\$0]#x$0m#OP421j44RW01j4RXQ01PWP4P4P2Q01P4P4P4P<P<n2001116000120101101n2001116000120116101WgP4^gXR]Q0?Q0:708P[Q01PWP4P4P2P2n2001116000120116101XgXP]17<2R]$15Xr4X6421g]]^r4^64P4P4g02TJ1:<2H2ZR]#TZ084Xl41=]]`084^l4Q06%j2R]#TW6Q061=]]]6%uNS0BQ0A'oPL%p3PP1I<2RN$15Xr4X6421gNN^r4^64%uRPL%93R3#pPPQ0:#pPP&0\8#\$0m$0d#OP4%98#x$0e#h$0e$0T#LP4%98#x$0e#h$0T$0]#LP4&188$0m$0e#\$0E$0wP4%xV$0C$0j$0h#LP4%98#x#\#h$0e$0T#LP4&0f8$0T$0]#\$0m$0d#LP4%uSPL&2S8-2R4S0C%uOS0D60~4PL%9J#pPP%p@PP%p\PP%p7R7,mCPPQ06/qRQ06?0RR%jRP4%uTPL%pJPP&0nYRY$1aP0fzS0E$1aRJP0PJP0f|S0Fp,3sp0S0G'>P420@Y@PD1tYZPE%L8R@,tYPHfyS0H,tYPG20@Y3PI20@Y^P6Q0H#LP4fwS0I#@P[fxR^-1JZP4%@^P[Q0A,o^PLp+01@S0J#NRJPPp+01GS0K#NRTPPPTPPPTPP%NZS0Lp+01MS0M61I4PPp+01LS0N,:9P4PTPPp+01NS0O#NPPp+01IS0Pp+01OS0Q':P4f{S0R#N9e5CP=%53-0@YfHS0SQ0E#LP4%93-0@YfJS0TQ0Q#NR3PPQ0P#NPPp+01AS0U#NRTPPPTPPPJPPPJPPp+01US0V$2CQ06PWf~S0WP@P@CwPXPWQ0Wp+01WS0Xf}S0YCwPXPWQ0Yp+01XS0ZQ0FCwPXPWQ0Yp+01YS0[Q0FCwPXPWQ0Fp+01ZS0\Q0RCwPXQ0Fp+01[S0]+0:-0lWPXPWQ0Fp+01\S0^Q0RCwPXQ0Fp+01]S0_+0:-0lWPXPWQ0Fp+01^S0`Q0RCwPXPWQ0Fp+01_RJQ0RCwPXp+01`S0a,=@P[p+01aS0b#TS0cQ0bQ0b'=Q0Y#NPPp+01KS0d#NRTPPQ0W#NPPPTPPPTPPp+01JS0e#NR\PPP\PPP\PPP\PPP\PPP\PPp+01mR\-1[1P4p+01nS0f#cP[p+01oS0g/71P[Q0Dp+01DS0h'oPLp+01eS0i9e5MP=p+01fS0j>055M,|5P=p+01FS0k9e5MP=Q0K>055M,|5P=21[12X64ROp+025S0lO1P4p+01ES0mQ0k'VPPQ0]Q0m':P4Q0^Q0m':P4Q0_#NPPp+01HS0n#NRSPPPSPPp+02<S0o#@P[Q0op+02=S0p+1EP4Q0p#@P[PTPPPWP4Q0ip+02@S0q+0:g02TnS0rH04PXPWP4p+02ART-0:Jg02UoS0sH04PXQ0M#NPPp+01gS0tQ0O':P4p+02CS0up+02>RS':/G@P4p+02?RV#NPPP3PPp+01kS0vp+01PS0w':P4Q0KQ0C%uQS0x60~4Q0D'o+1BPFQ0d%pUS0y'VPPQ0m$1YP0Q0k$0_P0p+02SS0z%x8$0d$0E$0C$0]#h+0@Q0np+02KS0{Q0K'7P[Q0U-1JZP4p+01BS0|#@RUP[Q0U#cS0}P[PUP[Q0N#@P[Q0Mp+02LRU+0W#@P[Q0Bp+01CRQ'oPLAE5Q7P=1m7QQ0|'mPPQ0|,mCPPQ0|9e5CP=p+02MS0~Q0h'm=E5CP=Q0|=E5CP=Q0|,VQPPp+01VS10p+02NS11'GP4p+02dS12&188$0J#h$0H#h+0@Q0[p+02eR3%h8$0]$0E#h#h+0@Q0\p+02fS13/A9Q0]%NQPPp+02hS14/A1Q0_Q0HQ0H50XP[A0X^^R9P[P9P[P9P[P9P[P9P[%jQP4Q0\#TQ0\Q0\'=fkS15flR9p+02jS16'='1fjS17%g9'1'4P[Q17&1lFRN'^&0_FRFQ0M=E5MP=P5PCQ0OP^H1KP=Q0^Q0y5E5P=Q0~P2P2p+031S18PUDM%c;S19%gDQ05[S1:%@DS1;Q0i7]D[[[^04^54P[P2X64R_Q17O1P4p+01RS1<:055TP=Q159e5CP=P5p+02BR`p+01TS1=Q0WH1KP=p+02iS1>fsS1?'o/^NPFQ16p+01dS1@802KPLQ0yp+01cS1A'mp+01bS1B'mPPfmS1C/V9PPfnS1D/V9PPp+03?S1E/A1p+024S1FQ0a/G@P4PNPF&1z4RL&1y4RKQ0`9e5M21w5?RaP2P;Q08g01H6Rb'qQ0821t2;;0bd&0r<H1sRcb:b8b9Q0FP2b7Q0FQ1A9E5CP=Q0i/VCPPQ0rfpS1G':P4Q1B-1JZP4p+01hS1H9E5MP=fqS1I9E5CP=1V^CPPQ0f,m7PPp+03KS1JQ16'AQ0qp+03LS1KQ16'APTp+03MS1Lp+02kS1M'tP`p+03NS1NQ16'tQ0up+03OS1OQ16'Ap+02DS1Pp+03PS1QQ1M'tp+02ES1Rp+03QS1SQ1M'tp+02FS1Tp+03RS1UQ1M'Ap+02GS1Vp+03SS1Wp+02lS1X'tp+02HRdp+03TS1YQ1X'tp+02IS1Zp+03US1[Q1X'Ap+02JS1\p+03VS1]p+02mS1^'tQ0{p+03WS1_p+033S1`'APUp+03XS1ap+032S1b'AQ0~p+03YS1cQ18'AQ11Q0v90X\P[p+01lS1d90X\P[PXQ1dP\PXQ0vP\PXp+01jS1eP\PXp+01iS1fP\PXQ1HP\PXQ0tP\Q0j=0X\$01K00K00K00P[PXp+020S1gPXQ0gPXQ0fPXP\PXQ1dPXQ0vPXQ1ePXQ1fPXQ1HPXQ0t&1lXI0^I0^I0^I0^I0^&0_Xp+021ReQ0K50XP[Q0n90XeP[Q0P90XeP[Q0e90XeP[PXPeQ0dPXQ1gQ0dPXQ0gQ0dPXQ0fQ0dPXP\Q0dQ1dQ0d50X$01H1@K00K00P[p+026Rfp+022S1h50XP[p+023S1i90XfP[Q1F90XfP[Q0l90XfP[PXQ0lPfPXQ1FPfPXQ1iPfPXQ1hPfA0Xef$01K00K00P[p+02;Rg=0XfP[p+027S1j90XgP[p+028Rh90XgP[p+029Ri90XgP[p+02:S1k90XgP[PXQ1kPgPXPiPgPXPhPgQ1j=0Xg$01H1@K00P[A0XTgP[Q0o90XTP[Q0p90XTP[A0XTSP[A0XTVP[Q0q90XTP[PXQ0qPTPXPVPTA0XST$01K00P[A0XdTP[A0Xd`P[Q0u90XdP[Q1P90XdP[Q1R90XdP[Q1T90XdP[Q1V90XdP[PXQ1VPdQ1T=0Xd$01H1@P[p+02PS1l=0XdP[Q1lQ1Z50XP[Q1lQ1\50XP[Q1lQ0{50XP[Q1l=0XUP[Q1lQ0~50XP[Q1lQ1150XP[Q1lp+02OS1m50XP[Q1mQ1l50X$01P[p+02YRjQ0f50XP[Q0g90XjP[Q1g90XjP[A0XjeP[Q1h90XjP[Q1i90XjP[Q1F90XjP[Q0l90XjP[A0XjfP[Q1j90XjP[p+04PRkp+03oS1n'tp+03ES1o1VThPPAE5iCP=p+040S1p/:VP4Q0q#@P[Q1R/VhPPp+030S1q9E5MP=Q1VQ1['VPPQ1WQ1b'VPPQ1Wp+03DS1r60=2Xd4P[^d4S1sP_P_p+03hS1tPRp+04SS1up+02bS1vJ1?P_Q1WO1P_Q1uO1'=Q1aQ0{p+03dS1w'V6055P=Q0up+03eS1x5E5P=P5P5PMQ1aQ1ap+03@S1y5e5I0oP=p+04BS1z/:E,=H1G<;p+02XS1{'=p+03kS1|/7G%cGS1}%gIQ05[S1~p+04aS20f;Rl7KI1GGIS21#@Q21Q1[3][[[[[[^04^54^A4^D4^P4^Y4^?[P[p+02TS221G2<S23Q23p+04[S24Q0zDM%cDS25%gEQ05[S261GDES27#@Q27Q1O3][[[^04^54^A4P[Q1[Q0q[P0Q1YQ0o'7P[Q0p#cP[%@SP[p+04WS28-1>Zp+04YS29Q1QPV[[p+04ZS2:Q1SQ0q[[P[Q2:g01K=S2;Q24>1=Z<UWaQ2:Q2;Q0q[]aQ24Q2;PT[]aP[p+03[S2<Q2:+1<Q1UQ0q[\VQ0qQ1WPT[[P[P5PSP5Q0Lp+04`S2=$0n61I4-0U7H0IP=Q2:#NQ0p5E5P=Q299E5VP=Q29=H5SP=Q0o9e5CP=Q0~$1YP0Q1w$1RQ1mP_POp+04jS2>Q2>p+039S2?I1qQ1h/=3p+04kS2@-1p1PeQ0j=E5CP=Q1T=E57P=Q0t=E5CP=p+03jS2AQ0j'lp+02US2BQ0v/^NPFQ1@%N@S2C'mPPQ1@Q1@p+052S2D+0W'GP4Q0O,4TP[Q0eQ0P'4P[Q0m,4`P[Q0J,4`P[Q0H,4`P[frS2E,4`P[Q17,4`P[faS2F$01P[f`RO=E5CP=p+05;S2Gp+05<S2H+1:p+02nS2IQ18PO[[p+02oS2JQ1bQ2F[[P[P5Q0f&1R>R>P5f^S2KP>p+04CS2L9E5MF<P=P5Q2DP>P5f_S2MP>AE5M7F<P=Q1z9E5iP=Q2M=E5iP=p+04=S2N@1oiRp+02gS2Op+04ES2PQ0o6055P=P5p+03CS2QP>P5p+03BS2RP>fbS2Sp+03nS2T5E5F<P=1VSCPPp+049S2U-1>Zp+05BS2VQ14f\S2W[[p+05CS2XQ1>f]S2Y[[P[Q2XQ2;Q2N>1=Z<UWaQ2XQ2;Q2Y[]ap+05DS2ZQ2;Q2K[]aP[Q2Jp+02]S2[p+04FS2\e7kRfQS2]Q1qp+02^S2^7kRfRS2_fSRP$19fTS2`P[[^6PP5p+03JS2aP>P5p+03IS2bP>fVS2cF<P=P_P_p+04cS2dp+03iS2eQ2bPPJ1?P_p+02VS2fO1Q11'=P5fPS2gP5Q1V-0UCH0IP=p+035S2h?kRgfWS2ip+036S2jp+05XS2kQ0r'A7kRfXS2lp+037S2mQ1k7kRfYS2np+038S2oQ1v7kRfZS2pQ2??kRif[S2qp+03:S2rQ1j7kRQ2Wp+03;S2sp+05]S2tQ0s'A7kRQ2YQ1i/4PP[Q0g/4PP[Q1e/4PP[Q0i/4PP[14JPP[Q0Z/4PP[Q0w/4PP[Q0K/4PP[Q2_Q2]Q2BbOp+03aS2ufOR0fNRm5H5P=p+03FS2v/lmfhS2wp+04oS2xQ0A'o/^NPFPLP;&0GGS2y?aGLP<&0GHS2zPEPLPDPLD}D}PKP5Q0KP>P5Q2iP>P5Q0kP>P5Q2AP>P5Q2eP>P5Q1^1f56S2{5H5P>Q0mF<F<F<PaPcb:b8b9X04X54XA4XD4XP4XY4X?[P5PLP<Q2z?aHLS2|P2&0GES2}?aDLS2~?a;LS30D}$0r$1PP?P5Q0mP>P5fUS31P>P5Q0hP>P5Q1tP>P5p+03gS32P>P5Q1M1f5GS335H5P>PQF<F<F<H1O^04^54^A4^D4^P4^Y4^?[P5P5p+041S34=E5CQ13P>fERnEQP=f<Ro,4TP[Q0p/4oP[14hoP[Q1i/4oP[14\oP[Q0j/4oP[Q0`/4oP[Q0V/4oP[P5PlP>P5Q1|P>P5Q2AP>Q0kCrF<P=PNPF&0G;S35?a;LRp?a<LS36PKf=RqPaPcb:Rrb8b9X04X54P5&0G<S37P<PLP2PLD}$0r$1PP?PlH1O^04^54Q1V/46P[14`6P[Q0p/46P[Q1j/46P[Q1g/46P[Q1H/46P[14J6P[PNPFQ35P<&0GDPDPLI1nS38PKPrb8b9X04X54XA4P5Q37?a2p$0r$1PP?PlH1O^04^54^A4Q1\/4GP[Q1R/4GP[14VGP[14hGP[Q1g/4GP[Q0t/4GP[Q0{/4EP[Q1R/4EP[14SEP[14fEP[14\EP[Q1\/4DP[Q0u/4DP[14gDP[Q1h/4DP[Q1V/4;P[14V;P[14f;P[14`<P[14i<P[14g2P[&0_WS39g01MM$0_S3:Q3:g01NKQ39Q0tg01OHp+06US3;,G2P4p+05NS3<p+06XS3='Gp+06WS3><17<P[p+05OS3?,7;P[p+06]S3@/A;p+05RS3Ap+06^S3B/AEp+05SS3Cp+06NR?/7EP[p+05JS3D,IGP[Q2X/7GP[p+06bp+06[S3E80B6p+05WS3Fp+06cQ3;80BBQ2kp+06dS3Gf:Rpp+06MS3H40Bp+05YS3Ip+06eQ3H80Blp+05ZS3Jp+06fQ2V80Bop+05[S3Kp+06gQ3H80Bqp+05\S3Lp+06hf>RrQ3H40BQ2tp+05^S3Mp+04HS3N?kR2Q0vp+05`S3O,DYQ3K,22p+05aRsQ3K,2<p+05bS3Pp+05KS3Q,2;p+05cS3RQ3D,2Dp+05dS3SQ2t,2Ep+05eS3Tp+04OS3U21kRERt'lQ1h1lktQ1ip+04QS3V/ltQ1Fp+04RS3W/ltQ0lQ1u/ltPfp+05kS3X,DYp+05iS3Y,22p+05lS3Zp+05mS3[P<Q3Yp+078S3\%9A$0a#O80BmCXP[Q3Y,2;p+05nS3]p+05oS3^PDp+05hS3_p+07:p+072S3`'ACXP[p+060S3aPEQ3_p+07;/A@CXP[p+061S3bPHQ3XfMS3cCXP[p+062S3dQ2:70DP[11D;P[11;2RAP[PAP[p+04_S3ep+066S3f02`2Q06P]P4%@2S3gP[&16;P2Q2MQ2Y+2_p+06;S3hQ08[Q2M-0k2Q3cQ2YfKS3iH1ip+06<S3jp+04gS3k[Q31=J2RQ1ZQ31=J<RQ1\Q31=J;RQ0{Q31=JDRPUQ31=JERQ0~Q31=JHRQ11Q31=JGRQ1mfgS3l>1h6IQ29<2^q-0k6p+06DS3mQ2x[p+02QS3nQ3170IP[p+02RS3o?0I0P[Q0z?0I0P[Q22?0I0P[Q2B?0I0P[Q2f?0I0P[p+02WS3pQ1F70IP[11<2P[11D2S3qP[11H2P[11I2P[11B2P[PnftS3rQ2EQ2SPOQ0TJ2]Q1Xp,2fxR]Q2cp+04hS3sP2Q07$2\RAI14g02W5p+06SS3tQ3rp+07_S3u/>2RtPtfuS3vCBp+05?S3wPDP<O1Rt;0t[]6P[ffS3x=J;Rp+02`S3yB13<DDP[Q1vPEQ1DPRQ3xDZP[p+02cS3zPHQ1DPRPODZP[Q12PGQ1DPRPODZP[P3PIQ1DPRPODZP[Q13P6Q1DPRPODZP[Q2OPBQ1DPRPODZP[Q14Ppp+04AS3{PRQ1kDZP[Q1>Plp+04MS3|PRPTDZP[Q16PoQ3|PRPTDZP[Q1MPqQ2LPRPTDZP[Q1XPrp+04LS3}PRPTDZP[Q1^f?Rtp+04DRuPRPTDZP[Q2If@S3~p+04KS40PRQ0uDZP[Q2JfAS41Q2PPRP`DZP[Q1qfBS42p+04JS43PRP`DZP[Q18fCS44Q3};JRQ1PP6CnP[11;<P[11olP[p+034S45fFS46?JkRQ1ZP;CnP[11G;P[Q3~/1;S47P[Q2mfIRvp+04US48;JRQ0{P;CnP[11p;P[fDS49/1;P[Q2rfLS4:Q29;JRQ1mP;CnP[11r;P[p+03<S4;p+04]S4<=JmRQ3oP<CnP[Q41/1<S4=P[fiRwP4p+086S4>/:2P4p+08?Rx/A<p+074S4?1G<@P4p+08:S4@,:;P4p+077S4AQ0E;0;P[p+08<S4B-1E;P4Q1;P[Q3ag02X<7zDP[Q2E,=6P[Q1;P[Q0r/:EP4p+07fS4C/:HP4fvS4D#TPDePDp+08DS4E-1:pp+069S4FPH[\Gp+06:PG[\IP[p+08FS4G-0WE,GEP4Q3jP6[\BP[p+06=RyPB[\pP[p+06>S4HPp[\lP[p+06?S4IPl[\oP[p+06@RzPo[\qP[p+06AS4JPq[\rP[p,2HIS4KQ1hPeQ1gQ0gQ0fP\Q1d$1eL2[fGR{p+08SS4L'7Q0vQ1e'1Q08Q07Q0UQ1g+0kQ1ep+08QS4MH2Y;0b&2XJQ46Q1<p+07PS4NQ1<p+068Q4Ne30Q0wp+01SS4OQ4Op,3HspRbQ3hQ2T'1PnPvQ0NQ0MQ1oQ1rQ1rQ2QQ1pQ1nQ1nQ2TQ2Tp+03mS4PQ4Ip+08ZS4Q/^N'^PFQ35?a<LPKP5p+042S4RP>P5P5P5Q4IPCP5PCP7FvP>P5P5Pz1f5ES4SP>Q34=H5yEQF<PaPcb:b8b9X04X54X?[p+08aS4TP<P<p+06ES4UCUp+08hS4V,G;p+08gS4WP<17<;H07p+08cS4X?KDEp+08\S4YQ4V,GDPDp+07WS4ZH0Z[[[^04^54^?[P2p+047S4[p+07[S4\PVP6Q41PbO6b7b@b;b<b=b>b1b2Q1g,1ePlQ0Op+08_S4]'7Q4ZQ4X/>2RzP41I2gP[AKg<2Q4\p+08fS4^/A;Q4\p+01QS4_P2O1$0RW6R|p,4scfgS4`p,1LS4ap,2arS4bp,1CS4cp,2ILS4dQ4Kp,4HIokS4eQ0Gp,2DLS4fQ1PQ0uP`PTQ0qPVPSP;Q41Q3iP0Q1<Q4OQ1JQ2aQ2aQ2bp+046S4gp+045S4hQ4hp+044S4iQ4ip+043S4jQ0xQ4T'oQ4]p+06FS4k'o/^N'^PFQ38PKP5P5p+06CS4lp+08`S4m9e5CP>P5Q2UP>P5P5Q4[P5Q4m00U7H0IP>P5p+06GS4n1f5HS4o5H5R}P>Q4gCrF<EQPaPcb:b8b9X04X54XA4X?[P;p+08lS4pP21I2;H07p+08iS4qP;P;Q3HCUp+090R~,GDp+08oS4rPE17EDS4sH07p+08kS4t?KEG%@ES4uQ3u7]E[[[[^04^54^A4^?[P2Q2NQ1Rp+07aS4vPpP6PrP{PbO8b7b@b;b<b=b>b1b2Q3iP0Q1<Q4OQ1JQ2aQ2aQ2bQ4gQ4hQ4hQ4iQ4iQ4jQ0@p+07]S4w'o/^NPFQ38PKP5P}P>P5p+04;S4xQ335H5P>P5P5p+06K1f5IS4yP>Q2{p+08bS4z#N,m7=E5C1f5BS4{60856085EQF<PaPcb:b8b9X04X54XA4X?[XE[XQ[XU[Xb[P;P~P2PDH07p+093S4|,G;p+092S4}PDPHH07p+08nR}?KDIQ4X>17ED>2VBp[[[^04^54^A4^?[^E[^Q[^U[^b[P221MUpp+08XS4~,IpQ2NP`PBQ1RQ4vPpP6P{PbO;b7b@b;b<b=b>b1b2ND1LPDQ4^010DE~WXaaW6Q4ZPiPzPzQ1kH0ZQ0OP<O1$0R[]6p+07XS50p+08dS51/>2RzP4&0Y2S52p+07GS537]2Q4\Q4^/A<P|Q4`Q4aQ4bQ4cQ4dQ4KQ4eQ0GQ4fQ1PQ0uP`PTQ0qPVPSP<Q41Q3iP0Q1<Q4OQ1JQ2aQ2aQ2bQ4gQ4hQ4hQ4iQ4iQ4jPNPFQ37PKP5P5Q4IQ4RP>Q4jEQPaPcb:b8b9X04Q4^P2P2p+07MS54H0Z%@<S55p+07YS567]<[^04P2PBP6O2b7b@b;b<b=b>b1b2Q3iP0Q1<Q4OQ1JQ2aQ2aQ2bQ4gQ4hQ4hQ4iQ4iQ4jPNPFQ37PKP5P51f5DS57Q4iP>Q4NQ4S6085EQPaPcb:b8b9X04X?[XE[p+07OS589]<2p+08[S59,I</4D[^04^?[^E[P2Q3h/7B21MUB'4Q4^/7BPBP6O4b7b@b;b<b=b>b1b2ND1LP;Q4^010;E~WXaW6Q50&0Yzp+07FS5:7]zQ0QP<O1S5;$0R[]6PvQ3cQ0wQ4_Q2bp+03HS5<Q5<p+03GS5=Q4iQ4jQ4jQ4RQ4RQ34PNPFQ37PKP5P5Q4iQ57P>Q4J9E5yEQPaPcb:b8b9X04X?[Q4YQ4V,G2;K<Q54Q4q,G<'7[^04^?[P2Q0oQ0uPlO3b7b@b;b<b=b>b1b2Q1ieQ1iQ0Q00kSQ1dQ0oPEQ1eI2TQ0mQ0hPQQ0|Q0UQ0Jp+03fS5>Q0KQ1r3040QD[P:Q0kQ0Ep+07\S5?,DYRyp+048S5@Q5@Q0RP]P<Q1gP2PAp+07^S5AQ4\,2<S5BQ2nQ5Ap+07ZS5C,2<S5DPgQ5AP<Q56Q1gQ5AQ50,2<S5EP\Q5AP<Q4ZQ1dQ5AP<Q5:Q0vQ5AP<p+07DS5FQ1eQ5Ap+07VS5G,2<S5HQ1fQ1AP<Q5AQ0qp+08jS5I/>2RzPzPTCBp+06JP;P<O1RzQ0WP<O130[]6Q0FP2G`D?D?GdD?F3FCWB'8XCy'8P2Q0nQ0YP:Q0PQ0Jp+07`S5J,DYRyp+04<S5KQ5KQ0JP]P<Q1FP2PAp+07bR|Q3u,2<S5LQ2YP|Q5A,2<S5MPVP|P<Q4wQ1FP|P<Q5?PeP|Q5BQ1gP|P<p+07JS5BQ0gP|P<p+07HQ0fP|Q5DP\Q0tP<Q1P1>}2S5NQ5NQ1RCBPQP<O190?z[^6|Q0UP2G`D?GdD?D?F3FCWB'8XCy'8P2Q0dP:Q0NQ0mp+07dS5N,DYRyp+04@R?Q0hP]P<PhP2PAQ4Cp+07cS5O,2<S5PQ2FQ4C12<|S5QQ0uQ4CP<Q4vPhQ4CP<Q5JQ0lQ4CQ5LQ1FQ4CP<p+07NS5LQ1iQ4CP<p+07LS5RQ1hQ4CQ5MPeQ0vP<Q4CPdQ4}/>2S5MQ5MQ1ZCBp+06RS5MQ0KP<O170z[]6Q0mP2G`D?GdD?D?F3FCXB?'8XCy'8P2Q0OQ0nP:Q0QQ0ep+07hS5S,DYS5TQ5TQ0nP]P<Q0oP2PAp+07jRyp+07gS5U,2<S5VfeS5WPyQ4C,2<S5XQ1VPyP<p+07eS5YQ0oPyQ5N,2<S5ZPiPyQ5PPhPyP<p+07RS5PQ1jPyP<Q4NPfPyQ5QQ0lQ0gP<PUp+096S5Q/>2S5[Q5[Q0~CBp+06VQ0dP<O170z[^6yQ0PP2G`D?D?F3D?F3FCXBu,8uWC'8P2Q4_Q0MP:Q1<Q0Qp+07lS5T,DYS5[Q5[Q3NQ3NQ0NP]P<Q0qP2PAp+07nS5\p+07kS5],2<S5^PwQ5\12<yS5_Q0{Q5\P<p+07iQ0qQ5\Q5S,2<S5`Q0pQ5\Q5VQ0oQ5\Q5HPgQ5\P<p+07TS5HQ1kQ5\Q5XPiQ1iP<Q5\Q1lp+09:S5V/>2RyPyQ3nCBp+06ZS5aQ5;70z[]6Q0MP2G`GdF3D?F3FCWB'8WC'8P2Q1=Q1<P:Q0VQ1=p+080S5[,DYRyQ3}Q3}Q0wP]P<Q1PP2PAp+082S5;p+07oS5b,2<S5cQ1CQ5;Q5\,2<S5dQ1mQ5;p+07mS5e,2<S5fQ1PQ5;Q5T,2<S5gPTQ5;Q5^Q0qQ5;Q5DPVQ5;Q5EPSQ5;Q5_Q0pQ1jP<Q5;Q22p+09>S5E/>2S5DQ5DQ2BCBQ3BQ4OP<O170z[]6Q4_P2DiF3F3F3F3FCWB'8XCy'8P2Q0XQ0Xp+04?RyQ0jQ1R90?2XcyPnAJJURQ1HQ3pQ2BQ1RQ0uP\Q3cQ4:Q3ip+097S5DfcS5hQ3lQ1eQ0vp+03cS5ip+03bS5jQ5jQ2up+04NS5kQ3|Q3|Q3}Q3}Q40PNPFPLPKP5P5Q4vQ4vP5Q4vQ5]FvPaPcb:b8b9Q5EQ5EQ5Ep+09@S5]CUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MP?Q0jQ3{?02VXc?Q42Q0a?JURQ1fQ1{Q2fQ1TQ1PQ0fPmQ3cQ4:p+091S5lfdS5mQ2wQ0vQ1dQ1wQ5iQ5iQ5jQ3UQ5kQ5kQ3|Q3|Q3}PNPFPLPKP5P5P|Q4vP5Q4vQ5TFvPaPcb:b8b9p+09?S5np+098S5oQ5op+09AS5pCUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MQ3{Q0jQ3{Q1z?02VWcPtQ0b?JURQ1ePjQ3pQ1VQ1RQ0gP0PmQ3cQ4qQ5WPwQ1dP\Q1xQ1wQ1wQ5iPkQ3UQ3UQ5kQ5kQ3|PNPFPLPKP5P5Q5OQ4vP5Q4vQ5eFvPaPcb:b8b9Q5]P~P~p+09BS3{CUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MQ1zQ0jQ1zQ2L?02VWcPoQ1B?JURQ0vp+02ZS1zQ1{PdQ1TQ1gQ2gP0PmQ4qQ3xQ17P\Q0fQ5>Q1xQ1xQ1wQ3VPkPkQ3UQ3UQ5kPNPFPLPKP5P5Q5NQ4vP5Q4vQ5\FvPaPcb:b8b9Q5pP~P~p+09CS5qCUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MQ2LQ0jQ2LA0u2VWcPBQ1A?JURQ1dp+02[S5rPjQ1ZQ1VPeQ2]Q2gP0Q5AQ3lQ15Q0fQ0gQ32Q5>Q5>Q1xQ3WQ3VQ3VPkPkQ3UPNPFPLPKP5P5Q5Yp+06TR?P5P?Q5bFvPaPcb:b8b9Q3{Q5YQ5Yp+09DS5sCUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MPuQ0jQ2P?02VXcuPGQ1@?JURP\p+02\S5tQ1zQ1\PdQ1hQ2_Q2]Q2gQ4qQ2wP9Q0gQ1gQ1tQ32Q32Q5>Q1uQ3WQ3WQ3VQ3VPkPNPFPLPKP5P5Q4CP|P5P|Q5[FvPaPcb:b8b9Q5qP~P~p+09ES5uCUP2b7b@b;b<b=b>b1b2N;0MEsQ0MeQ0MQ2PQ0jQ2PQ2\Q5i702WcPGQ0i?JURQ0fQ2[Q5rQ0{Q1ZQ1iPPQ2_Q2]Q4qPwQ1CQ1gPeQ2eQ1tQ1tQ32p+04TS5vQ1uQ1uQ3WQ3WQ3VPNPFPLPKP5P5Q5UP|P5P|p+081S1uFvPaPcb:b8b9Q5sP~P~p+09FS5wCUP2b7b@b;b<b=b>b1b2N;0MEsQ2PQ0VQ5j30eQ2PQ0VQ5i30Q0I02Q1Q0I#gRu&0Ou+2PQ04%g^Ru&0OuQ4B,DYRup+04XS04Q04Q0^P]P<Q1lP2PAp+08>S5xp+08;S5y,2<S5zQ0HQ5xQ4@,2<S5{Q5rQ5xp+089S5|,2<S5}Q1lQ5xP<p+088S5~Q0~Q5xP<p+087S60PUQ5xQ5XQ0{Q5xQ5ZQ1\Q5xP<Q4>Q1ZQ0uP<Q5xQ3yp+09JS5Z/>2S5XQ5Xp+02aS61CBp+06jR?PJP<O170z[]6Q0_P2DiD?F3D?GdF3FCWB'8XCu'8P2Q0H#gS62P4Q0EQ5xp+09IS63/A270`Xl4Q2KP1P2E~p+08=Rup+06P70TP]PAQ1lQ3yQ2lPOQ11Q0uQ0_P2Q2KQ2YQ2WQ2pPEPpPBP6PIPGPHNE2OQ5x,DYRyP]Q1PQ3;PxeQ0`PAI14P]P2Q3nQ0`PAPxQ4B,22S64Q5MPxQ5y,22S65Q5tPxQ4@,22S66Q3nPxQ5|,22S67Q11PxQ5~,22S68Q0~PxP2Q5UPUPxP2Q5YQ0{PxP2Q60Q1\Q1P/{2D?D?GdF3F3FCXqy'8Q031DYxRyQ0`P]P2Q3oPJPAp+08@S0`P2PuQ3tQ0`Q64Q2[Q0`Q65Q3oQ0`Q66Q1mQ0`Q67Q11Q0`P2Q5SQ0~Q0`P2Q4CPUQ0`Q68Q0{Q1R/{2CnD?D?F3F3D?FCXqyQ0`,DYRyp+04\S68Q68Q0aP]P<Q22P2PAp+08BS6712<xS66Q0YQ67Q5x,2<S65p+02_S64Q6712<uS69Q22Q67P<Q4BQ3nQ67Q5zQ1lQ67Q5_Q1mQ67Q5`Q11Q67Q5{Q0~Q1VP<Q67Q12p+09NS5{/>2RJPJP3CBp+06nRJQ1AP<O170z[]6Q0bP2DiF3F3GdF3FCWB'8XCy'8P2p+08AS5`,DY122xQ67p+08CRyQ65Q2B30P[Q4EQ3>70<P[p+08ES3>PDQ5`Q1vCXP[Q4GPEQ0`Q2BCXP[p+08GS5_PHQ0`Q2BCXP[p+08HS6:PGQ5[Q2BCXP[p+08IS6;PIQ5bQ2BCXP[p+08JS6<P6Q67Q2BCXP[Q1fP]PBQ2[Q1ePAJ1bP[Q3n/{p,1<P[Q3qP[Q0zQ1f80PoP[11G<P[11H<P[11B<P[116<P[11o<P[11l<S3qP[Q4=P[11r<S6=P[Q4=P[Q4=P[Q49/1<S6>P[Q46/1<S6?P[11n2P[Q47P:Q41PDp+08^S6@,DYS6AQ6Ap+05:S6BQ6BPSP]P<Q1bP2PAQ4mp+08]S6C,2<S6DQ0^Q4mQ4Y,2<S6Ep+03=S6FQ4mP<Q59Q1bQ4mQ4Q,2<S6GQ2JQ4mP<p+08YS6HQ2IQ4mP<Q6:Q1^Q4mP<Q4GQ1XQ4mQ4~,2<S6IQ1MP3P<Q4mQ2Rp+09lS6J/>2S6KQ6KQ2QCBQ5RPTP<O170z[]6PVP2G`D?D?GdD?F3FCWB'8WC'8P2Q44P:Q4:PBQ4z,DYS6AQ6Ap+05>S5RQ5RP`P]P<Q2jP2PAQ51Q4T,2<S6KQ0aQ51Q4m,2<S6Lp+03AS6MQ51P<Q4]Q2jQ51Q6@,2<S6NQ1`Q51Q6DQ1bQ51p+08LS6D,2<S6OQ18Q51P<Q6<Q1qQ51Q6EQ2JQ1>P<Q51Q2vp+0:0S6P/>2S6QQ6QQ5=CBQ4NQ1RP<O170z[]6Q0uP2G`GdF3D?F3FCWB'8WC'8P2P:P0PtQ4^,DYS6AQ6AQ2VQ2VQ1TP]P<Q2rP2PAQ4Vp+08eS6Q,2<S6RQ1@Q4VQ51,2<S51Q1oQ4VP<Q4XQ2rQ4VQ4z,2<S6SQ2mQ4VQ6KQ2jQ4Vp+08PS6K,2<S6TQ2hQ4Vp+08NS6U,2<S6VQ45Q4VQ6LQ1`Q1^P<Q4VQ2ap+0:4S6W/>2S6XQ6XQ1JCBQ5HQ1ZP<O170z[]6Q1VP2G`F3F3D?F3FCWB'8WC'8P2Q2]Q42P:Q31PnQ5I,DYS6AQ6Ap+05FS6XQ6XQ1\P]P<p+03>S6YP2PAQ4pQ4q,2<S6ZQ1HQ4pQ4V,2<S6[Q2bQ4pP<Q4WQ6YQ4pQ4^,2<S6\Q2sQ4pQ6RQ2rQ4pP<p+08TS6RQ2?Q4pP<p+08RS6]Q2oQ4pQ51Q2mQ18P<Q4pQ1Np+0:8S6^/>2S6_Q6_Q1OCBQ50Q0~P<O170z[]6Q0{P2G`D?D?F3D?F3FCWB'8WC'8S6AP2Q2iQ0SP:Q2cQ3i1DY}S6_Q6_Q3DQ3DQ11P]P<Q2RP2PAP~p+08mS11,2<S6`Q1dP~Q4p,2<S6aQ1LP~Q4t,2<S6bQ2RP~Q5I,2<S6cQ1EP~Q6ZQ6YP~Q6IQ6FP~P<p+08VS6IQ4;P~Q6[Q2sQ2hP<Q1Up+0:<S6d/>2S6eQ6eQ1WCBQ5?Q3nP<O170z[^6~Q1mP2G`D?F3F3F3FCWB'8WC'8S6_P2Q2lP:Q2nQ2]Q4},DYS1mQ1mQ3<Q3<Q3oP]P<Q2vP2PAp+094S6eQ5l,2<S5lQ1gQ6e12<~S6fQ1SQ6eP<Q4rQ2vQ6e12<}S4rQ2QQ6eQ6`Q2RQ6eQ6EQ6MQ6eQ6GQ1yQ6eQ6aQ1EQ2?P<Q6eQ1]p+0:@S6G/>2S6EQ6EQ1_CBQ5JQ2BP<O170z[]6Q0zP2G`F3F3D?F3FCWB'8WC'8S1mP2Q2qQ2`P:Q2WQ2iQ5Q,DYS6EQ6EQ3AQ3AQ2fP]P<Q2aP2PAQ5op+095S6`,2<S6gQ1FQ5oQ6e,2<S6hQ1[Q5oP<Q4|Q2aQ5oQ4},2<S6iQ5=Q5oQ5lQ2vQ5oQ6LQ1oQ5oQ6NQ1rQ5oQ6fQ2QQ6FP<Q5op+03ZS6Np+0:DS6L/>2S5lQ5lQ2<CBQ5NPjP<O170z[]6Q3pP2G`F3F3D?F3FCWB'8WC'8S6EP2Q2KQ2pP:Q2MQ2WQ5V,DYS5lQ5lp+05VS6jQ6jQ1zP]P<Q1NP2PAp+09<S6kp+099S6l,2<S6mPhQ6kQ5o,2<S6nQ1cQ6kP<Q5DQ1NQ6kQ5Q,2<S6oQ1JQ6kQ6gQ2aQ6kQ51Q2bQ6kQ6SQ5<Q6kQ6hQ5=Q6MP<Q6kp+03^S6Sp+0:HS51/>2S2aQ2ap+03_S2aCBQ5SQ2[P<O170z[]6Q5rP2G`F3F3D?F3FCWB'8WC'8S5lP2Q2FQ2MP:Q2SQ2RQ15'{Q5E,DYS5SQ5SQ3JQ3JQ2^P]P<Q1UP2PAQ5]p+09=S2[,2<S6gQ0oQ5]Q6k,2<S6pp+03]S6qQ5]p+09;S6r,2<S6sQ1UQ5]Q5V,2<S6tQ1OQ5]Q6mQ1NQ5]Q6[Q1LQ5]Q6\Q1KQ5]Q6nQ1JQ1oP<Q5]Q5jp+0:LS6\/>2S6[Q6[Q5iCBQ5TQ61P<O170z[]6Q64P2DiF3F3F3F3FCWB'8WC'8S5SP2Q5mQ1oQ1D'{Q5p,DYS6[Q6[Q2tQ2tQ61P]P<Q1[P2PAQ5qQ5],2<S6mPVQ5qQ5n,2<S6up+03`S6vQ5qQ5E,2<S6wQ1[Q5qQ6gQ1UQ5qQ6pQ1SQ5qQ6bQ1QQ5qQ6ZQ1OQ5qQ6sQ1NQ5<P<Q5qQ1xp+0:OS6s/>2S6ZQ6ZQ5>CBQ5bQ12P<O170z[]6Q1vP2DiF3F3F3F3FCWB'8WCfoS6[Q3LQ3LQ3yP]Q1GQ1YP2PAQ3{Q6[PSP9Q1DQ15Q17PwQ2wQ3lQ5=Q1G'{S6ZQ3{Q1wp+0:NS6b/>2S6xQ6xQ1xCBS6xQ5\Q3zP<O1S6y70z[]6Q61<132D[D[CnFCWBQ3yP4P1Q3xQ3{Q6[p+0:MS6z/A230P9Q1DQ15Q17PwQ2wQ3lQ6ZQ3{Q6xQ5\Q6yQ6y30[]6Q61Q6141340QD[D[Xl4Q5WQ31,19Q2]P9Q31Q3cQ15Q2cPvQ1CQ2lPnQ17Q2pQ41PwQ2WPqQ2wQ2KPBQ3lPOPHQ3xQ2SP<Q2vQ6['{Q5tP2Q2^Q3yQ3y+06S5tQ5pQ6z/>2P4Q1wP2P2Q1xCBQ5\Q3zP;O1'qWjaW6Q5pQ5TQ61P2O1p+05MS6Z30$0OP2WXW6Q5teH0AFWFWFWFWFWPVQ3rEsH0XH0XWuW{P<P2O2n2001000000121000000W4WyP<P2O2n2001000000121000000W4WxP<P2O2n2001000000121000000W4W}P<P2O2n2001000000121000000X4mW|P<P2O2n2001000000121000000W4WvP<P2O2n2001000000121000000W4WzP<P2O2n2001000000121000000X4oXwmP<P2O2n2001000000121000000X4GY04P<P2O2n2001000000121000000W4aaaaaaaaaaaaaaaaaaaaaaaaaaWCP<P2O2n2001000000121100000bgb~Y0IP2O1Q62$0OQ1CQ1IQ1FQ0lQ4Pp+03lS62Q62Q1|Q04Q28Q28p+04VS28Q28Q48Q0BQ0CQ0@60~4Q5s402/^NPFQ38PKP5P5PMQ3{P>P5P5Q3{-0[CP>P5Q6lP>P5p+06iQ4o5H5P>Q5oF<I0KJ0<PaPcb:b8b9X04X54XA4X?[%@;1=<D%g;Q05[p+09MS0@?KEG%cES48[[[[^04^54^A4^?[P2Q3eQ0pPyPQPGPIP6PbO8b7b@b;b<b=b>b1b2Q0E#cQ5xQ5XP4Q0lP<O1$0RQ1vP<P<Q3zCB&0Y;Q5b80b;Q08Q09Q08Q08p+06oS09P2Q3UQ14Q4EQ08p+070S5XQ1kP2O1PkQ1>P2O1n0100000020000WTQ2fQ13Q22H1i61hip+06YS47PSPHH2Nn0100000020000Q14PHO150JWWPhQ2OP3Q2BQ0zQ0pQ2YQ2WPEP<P2N;2MPhPEO1P;Esp+06mS08Q1BPEO1Q2OPEO130eY0ZY0YWXaW6Q5xQ1FP2O1$0RQ61p+09KS5t/><S5TQ5TQ1vCBp+09LS5T/>;S6x$0YQ6xQ5\40bp+06lS6xQ0bPDO1Q13PDO130[[[]6Q4m/72P[1=}<P[1=};P[Q11/=DP[Q11/=EP[Q4p/=HP[Q4p/=GP[Q5t-0:I-0lWPXQ11/=6P[Q11/=BP[Q11/=pP[Q11/=lP[p+09WS6y/AoQ6Dp+09QS6{,:qQ4p5zoP[p+07US6|,:rP4Q3E,:tP4p+09[S6}/>DP4Q41Q3;':P4Q2jQ1u7JHp+04^S3;Q6:,7DP[p+06`,:DP4Q47,:EP4PWP{Q6}P2CwPXQ5q/=<P[Q3{/=;P[Q3{/=DP[Q5p/=EP[Q5]/=HP[Q5n/=GP[Q5n/=IP[A0XuIP[A0Xu6P[A0XuBP[A0XupP[A0XulP[A0XuoP[A0XuqP[A0XurP[A0XutP[Q3~90XuP[&012P[p+07Sp+0:5S6~Q44'A7kRp+056S7014D<P[14H2P[14I2P[14B2P[14l2P[14q2P[14t2P[Q41/42P[Q3i,yXQ07Q1aQ5mQ4LQ3cI2Lp+05AS71Q4<Q71Q4<Q71$2K42JQ22Q2l;JRPpQ2_Q71Q4<Q71$2IQ2_PpP2J2GK2FY11Q6qp+03\S72Q2<Q6NQ1cQ1aQ1_$1eQ5mQ6^Q3cQ0]P2N<2EQ02Q49P<Q2iP2PXp+09TS73Q6RPmP2DSQ5mPXQ0?Q01PWP4Q0?P2Q01P4P4Q0?P<P4Q0?P2P8P2P8n011010003001011610116n2001116000120101101n2001116000120116101XgXp+08US01P0P<J1_Q73PXQ73Q6IQ2gP;DSQ2],=@Q2_,=@Q6yP@Q59PWQ1Cp+0:AS74P2CwS7550XPO]3XV4PXQ4QPWQ6G-0:9S76P@I0yp+09jS77PXQ4YPWp+0:BS78-0:2S79P@I0yp+09_S7:P<P<p+0:CS7;p+09^S7<DMS7=]3XT4PXQ59PWQ77Q74P@EPQ0gQ1ip+09\S7>Q4LQ0?P4Q0?$19Q00&194g02YAP8P@%T@Q0:Q7;Q6]N<0zPEH0cQ4LQ2jQ2mQ2xp+04nS0:Q0:p+04mS00Q3JQ3IQ3IQ2kQ2kQ3FPNPFPLPKP5P5Q2C00[}P>1f5;I0KPaPcb:b8b9X?[Q59P<[^?[P2p+09gS0?Q6WQ6Wp+0:KS7?p+09fS7@DMPIO2b7b@b;b<b=b>b1b4b2W3Q1CP<P2EYW3Q31P;PGEYVwUUP2O1b4P2O1b4P2O1b4X3nP2O1Q02PnPEQ2nP2Q46PXp+09VS7AQ01Q2gP2DSQ5WPXp+09US7BQ6IQ2]P<DSQ2gQ2]Q2wQ0?Q4QQ7550XPO]3XV4PXQ6HPWQ76Q0?I0yp+09iS76PXQ59PWQ79Q76I0yQ7=]3XT4Q4QQ4Q50XQ0gQ1iQ2hQ2jQ0:Q00Q00p+04lS7=Q3IQ2kQ2kQ3FQ3FQ6jPNPFPLPKP5P5Q6HQ4~P5Q4~Q4pp+08WS79L09PaPcb:b8b9p+09eS75p+0:1S7CQ7Cp+0:IS7Dp+09dS7EDMP2b7b@b;b<b=b>b1b2W3Q1CP<P2EYW3Q31P<PEEYUUP2O1b4P2O1b4W3P2O1Q02Q46PIQ2qP2PXp+09XS7FQ6IQ2_P2DSQ3xPXQ6yQ79PPP<DSQ2]Q2_Q0?PXQ59PWQ6[Q7;P2EPQ2S]3XV4PXQ4QPWQ1DQ78Q0?EPQ76PXQ4YPWP2Q6LQ76EPp+09aS78P<P<p+0:ES7Gp+09`S7HDM]3XT4p+07QS7IPeQ0lQ2mQ2op+050S7JQ2xQ2xQ0:Q3KQ3JQ3JQ3IQ3IQ2kPNPFPLPKP5P5Q59Q4~P5Q4~P}Q6HL09PaPcb:b8b9Q0?Q7CQ7CQ7?Q7@DMP2b7b@b;b<b=b>b1b2W3Q6[P<P2EYW3Q2iP<PEEYVwUP2O1b4P2O1b4X3{P2O1Q02P{PpQ2YP2Q0SPXp+09ZS7KQ79Q2`P2DSQ3lPXp+09YS7LQ4~Q31P<DSQ2_Q17p+09hS7MPXQ4YPWQ1IQ7GP2EPQ5m]3XV4PXQ59PWQ1GQ6LQ7MEPQ77PXQ6CPWP2p+0:FS7NQ77EPp+09cS7OP<P<p+0:GS7Pp+09bS7QDM]3XT4Q4YQ4Y50XQ1iQ1jQ2?Q2rQ2Dp+051R}P}Q7JQ2tQ3LQ3LQ3KQ3KQ3JPNPFPLPKP5P5Q6CQ6HP5Q6HP~Q59L09PaPcb:b8b9Q76p+0:2S7RQ7RQ6zQ7MDMP2b7b@b;b<b=b>b1b2W3Q1IP<P2EYW3Q2nP<PEEYUVPP2O1b4P2O1b4W3P2O1Q02Q0SPqQ2MP2PXQ7>Q4~Q2cP2DSQ2wPXQ6}Q6HQ2iP<DSPPQ2`Q15Q7MPXQ6CPWQ1?Q7PP2EPQ3x]3XV4PXQ4YPWQ2EQ7NQ7MEPQ77PXQ6@PWP2Q51Q77EPQ75P<P<Q7DQ7EDM]3XT4Q5HQ0lPiQ2sQ4;p+054S51p+053S7SQ7SQ2Dp+05_S7TQ3MQ3MQ2tQ2tQ3LPNPFPLPKP5P5Q4]Q4QP5Q4QQ4}Q6CL09PaPcb:b8b9p+09kS4}Q7RQ7RQ6sQ77DMP2b7b@b;b<b=b>b1b2W3Q1?P<P2EYW3Q2qP<PEEYUUP2O1b4P2O1b4X3vP2O1Q02PvQ3~Q2FP2Q0TPXQ7<Q6HQ2lP2DSPwPXp+09]S6HQ4QQ2nP<DSQ2p$0xQ2q$0xP4P1PXQ6@PWQ3vQ7DP2EPQ2w]3XV4Q6C=0X9Q4}Q4]p+0:JS7U-0:2-0lW50XQ0?Q7?Q7@60=<S7V7K<]3XT4Q6|Q1jPgQ6FQ6YQ70p+055S6YQ6YQ51PsQ3OQ3OQ7TQ7TQ3MPNPFPLPKP5P5Q4TQ59P5Q59Q6eQ4]L09PaPcb:b8b9p+09mS0?p+0:3S7WQ7Wp+0:QS7XQ6JDMP2b7b@b;b<b=b>b1b2W3Q3vP<P2EYW3Q2YP<PEK1HV9UP2O1b4P2O1b4W3P2O1Q41Q02Q0TQ44Q5hP2Q3iPXQ7HQ4QQ2pP2DSPwPXQ7:Q59Q2qP<DSQ2cQ2iQ77PXQ4]PWQ0IQ7?P2EPQ17]3XV4PXQ6@PWQ4DQ7UQ77EPQ6JPXQ4mPWP2Q6\Q6JEPQ76P<P<Q6zQ7MDM]3XT4Q5GPiQ0pQ1EQ1yp+058S7?p+057S7HQ7HQ70Q3RQ3PQ3PPsPsQ3OPNPFPLPKP5P5Q4XQ4YP5Q4YQ5QQ4TL09PaPcb:b8b9p+09oS7YQ6WQ6Wp+0:SS7Zp+09nR}DMP2b7b@b;b<b=b>b1b2W3Q0IP<P2EYW3Q2MP<PEEYV9UP2O1b4P2O1b4W3P2O1Q49Q02Q3iQ46Q5WP2Q4:PXQ7QQ59Q2WP2DSQ17PXQ78Q4YQ2YP<DSQ2K$0xQ2M$0xQ1CP4P1PXQ4mPWQ0HQ6zP2EPP9]3XV4Q4]Q1G50XQ0?Q4TQ6b-0:2-0lW50XQ4}P<P<Q6sQ77DM]3XT4Q4ZPgPVQ6MQ2RQ6Bp+059S6zQ6zQ7?Q3TQ3SQ3SQ3RQ3RQ3PPNPFPLPKP5P5Q6QQ6CP5Q6CQ5oQ4XL09PaPcb:b8b9Q7CQ6~Q6~p+0:UQ6PDMP2b7b@b;b<b=b>b1b2W3Q0HP<P2EYW3Q2FP<PEK1HUUP2O1b4P2O1b4W3P2O1Q02Q4:Q0TQ3lP2Q3cPXQ7EQ4YQ2KP2DSQ15PXQ7OQ6CQ2MP<DSQ2nQ2pQ1DQ6JPXQ4TPWQ0RQ6sP2EPQ1D]3XV4PXQ4mPWQ0EQ6bQ6JEPP}PXQ4zPWP2p+0:PS6sP}EPQ0?P<P<Q7XQ6JDM]3XT4Q50Q0pPTQ2QQ1rQ2HQ2GQ2GQ6Bp+05gS7Op+05fS7CQ7CQ3TQ3TQ3SPNPFPLPKP5P5Q4WQ6@P5Q6@Q5VQ6QL09PaPcb:b8b9Q7Wp+0:6S7WQ7Wp+0:WS7[Q7RDMP2b7b@b;b<b=b>b1b2W3Q0RP<P2EYW3Q5hP<PEEYUUP2O1b4P2O1b4W3P2O1Q3iQ02Q3cQ05PwP2PXQ7@Q6CPOP2DSP9PXQ75Q6@Q2FP<DSQ2pQ2qQ6[Q0?PXQ4zPWQ0YQ7XP2EPQ1G]3XV4PXQ4TPWQ0FQ6sQ0?EPQ7YPXQ4XPWP2p+0:RQ7YEPQ7YP<P<Q7ZP}DM]3XT4Q4zQ4z50XPVQ0uQ1oQ2vQ5Rp+05=S4zQ4zQ2HQ3YQ3_Q3_Q7OQ7OQ7CPNPFPLPKP5P5Q4qQ4]P5Q4]Q6kQ4WL09PaPcb:b8b9Q6~p+0:7S4XQ4Xp+0:YS6@Q6WDMP2b7b@b;b<b=b>b1b2W3Q0YP<P2EYW3Q5WP<PEEYUUP2O1b4P2O1b4X3mP2O1Q05Q05Q15P2n010000000W3P2O1n200100000021000010000W3P2O1n200100000021000011000X3{P2O1n200100000021000011000W3P2O1n200100000021000011000W3P2O1n200100000021000011000X3rP2O1n200100000021000011000X3lP2O1n200100000021000011000X36P2O1n200100000021000011000X3HP2O1n200100000021000011000X3;P2O1n200100000021100011000Q2cQ07Q6RQ22Q1cQ2lQ5Wp+07BS6WQ4t60=2Xd4Q0jQ1eQ2_Q2iQ4t'7P_Q6{Q2cQ2iP_P_P_p+09PR}Q3xQ3xQ3x#TQ6WPuP_P_p+09OS7@Q01Pup+05@S02J1?N:0iQ4tQ4tp+07AS7\L1GQ1XQ1^Q02Q7\PxP4Q3kp+04fS7]Q7]p+04eS7^Q3Ap+05QS7_Q7_p+05PS7`Q7`Q3?Q58PFQ35Q2~7a<S35PKP5P5Q33P5Q11-0[7H0IQ4NQ4y5H56085P>P5Q2{Q585H5P>P5p+08KS2~P>P5Q6<P>P5P5Q5LQ4{P>P5PCP7Q5QH1KEQF<F<PaPcb:b8b9X04X54XA4XD4X?[XE[XQ[XU[Q7U,=<,1EQ2~/1H'4Q7V,1I%cHS7V%gGS5QQ05[S7aQ6\?KGl1:HGS7bQ5]'7[[[[[^04^54^A4^D4^?[^E[^Q[^U[P2Q3IQ1DQ5QQ3>Q0pQ2[PGQ6[PIPpQ1IQ2EPbO=b7b;b<b=b>bRbhbeb1H1Fb2Q2]eQ2`Q5WQ0jQ1eQ1XQ1^Q7^p+04dS5]Q5]Q2dQ7`Q3?Q3?Q3<Q3<Q6ZQ2LQ7\P2PgQ1CP6Q6[Q1GO5b7b@b;b<b=b>b1b2+0LI0DQ6`Q74/>2P4%T21=22Q2w/7<P[Q2p9]2;P[Q2n/7DP[Q2q,IEP[Q2i,IHP[Q2WQ4E':9];GP[11H;P[11E;P[P4POP2PlPlQ5L,:2H0ZXd4P2Q1IQ1IQ1hPfP;PEPIPHPIQ2W,Il&15IP_Q7FPlPlPpQ2YQ2WP_P_P_Q7>Q2FQ2FQ2F#TQ5LQ5:Q3sN:0iL1^J1]P<H0cPEQ2?Q2rQ6ZQ5LQ6DP4Q51Q7SQ7SQ2DQ7TQ3MQ3MQ2tQ2tQ3LQ3WQ4NP2Q1\Q0FP{Q0WQ0JO5b7b;b<b=b>bRbhbeb1bib2+0LE~P;PDP6PBPGPB1IlO&15BP_Q7FPlPlPpQ2SPOP_P_P_Q7>Q2EQ2EQ2E#TQ5LQ5:Q3sN:0iL1^J1]P2H0cP6Q3rPqQ5qQ6b/AoQ5qQ2?P2O1$0RW6Q4`Q4aQ4bQ4cQ4dQ4KQ4eQ0GQ4fQ62Q1|Q2AQ2eQ1tQ32Q5>PoQ1eQ1FPhP<PpQ2sQ4;Q3?Q4NQ6UP4Q70Q6YQ6YQ51PsQ3OQ3OQ7TQ7TQ3MQ77Q6bQ0?402Q0xQ0DQ0A402/^N'^PFQ30P<Q2|PHPLI1nS2|PKP5Q4yQ5C5H5Q3uQ2{5H56085P>P5P5P5Q77PCQ56I0oP>P5P5Q4qQ775E5Q50P>P5Q4~P>P5Q79P>P5P5Q4>Q4{P>Q3TEQF<EQF<PaPcb:b8b9X04X54XA4XD4XP4X?[XE[XQ[Q6@,=E,1HQ4Q/1G'41:EH,I<S6@9KE<Q4XPHPHp+0:[S4>Q7WDMQ7VQ7ap+0:\S79?KGo%@GS4~?]G}[[[[[[^04^54^A4^D4^P4^?[^E[^Q[P2Q3_Q5QQ6RPGQ0WPUQ5TP{PIPBPvQ0UQ0|PbO>b7b;b<b=b>bRbhbeb1bib2Q1FPhP<PpQ2sQ4;Q3?Q4NQ6UP4Q70Q6YQ6YQ51PsQ3OQ3OQ7TQ7TQ3MQ50PFQ2|PKP5Q4yQ4w5H5Q2{9H5|6085S4yP>P5Q4{Q5?5H5S0DP>P51f5pS0?Q4\5H5S4fP>P5Q59P>P5Q4QP>P5Q5|1f5lS4e5H5S4KP>Q5q1f5oS4d6085F<F<F<PaPcb:b8b9X04X54XA4XD4XP4X?[XE[XQ[XU[Xb[Xf[Q79,=E,1HQ6C/1G'4S4cQ6@,16S6@p+0:^S4b,:Hp+0:9S4a5zpS4`Q7VQ7ap+0:_?KGrS2DQ7Z,IGQ3~'4[[[[[[^04^54^A4^D4^P4^?[^E[^Q[^U[^b[^f[P2Q4C/7{Q4[01M{'4Q3_Q0YPnQ5QQ6RPGQ0WPUQ5TP{PIPBPvQ0UQ0|PbOAb7b;b<b=b>bRbhbeb1bib2ND1LPqQ6b010qE~Q1FPhP<PpQ2sQ4;Q3?Q4NQ6UP4Q70Q6YQ6YQ51PsQ3OQ3OQ7TQ7TQ3MQ5G1f52S6b5H5P=Q6PQ0xQ5C402/^NPFQ2z?aGLP;PLP<Q2yPEPLPDPLD}D}PKP5Q2{Q5J5H5Q5YQ4{5H56085P>P5P5Q0?P5Q59-0q7H0IP>P5P5Q4eQ5AP>P5Q4mP>P5Q4]P>P5PoP>P5Q3T1f5r5H5P>P5PoP>Q3S1f5t5H5,|5CrF<F<EQF<PaPcb:b8b9X04X54XA4XD4XP4XY4X?[XE[XQ[XU[aXb[Xf[Z05[Q4b,=H,1GQ4]/1I'4Q7b9]B;p+0:`S7b,:Gp+0:;5zlQ1}Q1~p+0:aS4b?KItp+0:h,G6S4mp+0:gS5APGQ41H07p+0:cQ417KBQ4mQ497KBQ05[[[[[[[[[^04^54^A4^D4^P4^Y4^?[^E[^Q[^U[^b[^f[`05[P2Q1p,I{Q4PQ3_Q0YPnQ5QQ6RPGQ0WPUQ5TP{Q1pPIPBPvQ0UQ0|Q1eQ1iPbOEb7b;b<b=b>bRbhbeb1bib2Q1FPhP<PpQ2sQ4;Q3?Q4NQ6UP4Q70Q6YQ6YQ51PsQ3OQ3OQ7TQ7TQ3MQ50PFQ2|PKP5Q4yP>P5Q0DP>P5Q4fP>P5Q59P>P5Q4QP>P5Q4KP>p+084S4KQ4d5H5,|5F<F<F<PaPcb:b8b9X04X54XA4XD4XP4X?[XE[XQ[XU[Xb[Xf[Q4cQ6@Q4`Q7VQ7aQ2DQ4bQ3~7KGQ05[[[[[[[^04^54^A4^D4^P4^?[^E[^Q[^U[^b[^f[P2Q5o,I{Q3_Q0YPnQ5QQ6RPGQ0WPUQ5TP{PIPBPvQ0UQ0|PbOAb7b;b<b=b>bRbhbeb1bib2&0Yo@0bo~eO4abXXX2aaaaaaaaaaW6K2Bc0eO2W3aaaaaaaaaaaaaaaaaaaaaaaaaaaaXV4aaaaaaaaaaaaaaaaaaaaaaXT4PWP<Q5uP2Cw,yXQ5kQ0bQ0@/A;PRp+06kQ0@/A<S5Q7kRDZ[^V4^T4p+07>S4c/72S6@P[Q4c,7<P[Q5{/A;PyQ1>Q2O<2A2$0RP[Q1@P<O1Q09Q6{/>;P411HEP^Q0FPVQ0qQ5@Q4[Q4[Q4gQ2dp+04bRWPWQ20Q20Q2=PNPFQ36PKP5Q5@P>p+04:S4`CrPaPcb:b8b9X04X54Q5LP2P2Q54CUQ19Q1:Q1;Q6;7]D[[[^04^54P2Q0OPtP6Q42Q44O5b7b@b;b<b=b>b1b2-0LI1=<IQ1bQ18Q1qQ2JQ2IQ1^Q1XQ6[P6Q0HQ0YQ0qPTQ2UQ5@Q5@Q4[Q5]Q2dQ2dPWPWQ20PNPFQ36PKP5Q2UP>P5Q6|P>P5Q5HP>P5P5Q5LQ58<1;CP5PCQ54Q58'VJ2@CrF<PaPcb:b8b9X04X54Q58P2P2Q5LCUQ19Q1:Q4WQ2[':PDPDQ4^Q2[':CU[[[^04^54P2Q0QQ3~PBQ44Q49O5b7b@b;b<b=b>b1b2%98#x#\#h$0T$0m#OQ0;$0\#O<2?6eN:2>Q1^@1D61/1EP:Q2I@1DB1PHp+075S0;?0HkP2Q1q@1Dl1Q3\Q1bPpO1Q3\p+079S2[Q5v702WcP<P6PtPpP2PqQ1qP2P2Q18CBXd4Q0WPQQ1RQ1Tp+04>S5vQ2NQ2NQ5Kp+04iR8Q3sQ3sQ3kQ3kQ7]Q3BQ6b5H5P=PWPFQ35PKP5P5Q33p+06\S3B9E57P>P5Q5OP>P5P|P>P5PIP>P5Q3sQ4{5H5P>P5PIP>Q3kQ0?5H5,|5CrF<F<EQPaPcb:b8b9X04X54XA4XD4X?[aXE[XQ[XU[Q569zE<Q48%gHQ05[S54Q7Q?KH6Q76,GGR~Q7MPEPpH07Q7E?KIpAK~IqQ05[[[[[[[^04^54^A4^D4^?[^E[^Q[^U[P2Q2o,InQ2hQ7JQ49Q1=Q6RPnQ2oPrQ0SPvQ1IQ0EPbO>b7b@b;b<b=b>b1b2PIPHI0DPqQ52Q4B80b2Xd4Q0WPQQ1RQ1TQ5vQ2NQ2NQ5KP8Q3sQ3sQ3kQ3kQ7]PNPFQ36PKP5P5Q20Q4SP>P5Q5?P>P5Q4\P>Q4oQ3s5H5,|5F<EQPaPcb:b8b9X04X54X?[XE[Q5G?K2;Q19Q1:Q4G9]GDQ05[[[[^04^54^?[^E[P2Q7L/7nQ44Q1=PnPrQ0SPvO7b7b@b;b<b=b>b1b2&0YqQ5y80bqePIPHI0DO4EsZ0w6Y0;P<P2O2n2001000000121000000bTaWXaaaaaaX64Q6@p+07=7z2Q6xQ0bQ5QO1p+04GS5Q30[^64Q0RQ3hQ5uQ1IQ3vPhPiQ34Q1pQ1pQ1nQ68Q24Q24Q2:Q2:Q29Q4Jb@b;b<b=b>b1b2Q1IQ3vPhPiQ34Q1pQ1pQ1nQ68Q24Q24Q2:Q2:Q29PNPFQ37PKP5Q4lP>P5Q5kQ3GQ2C'm+0UI0sPaPcb:b8b9X04p+09RS5k,72S3GQ0@/:<Q3m817@[^04P2Q0KQ1DO2b7b@b;b<b=b>b1b2I0tQ4M,7^Q5uQ0FQ5wQ2EQ4DPiQ1kQ4RQ34Q34Q1pQ4<Q68Q68Q24Q24Q2:P^Q0IQ4lb@b;b<b=b>bRb1b2Q2EQ4DPiQ1kQ4RQ34Q34Q1pQ4<Q68Q68Q24Q24Q2:P^Q0IPNPFQ37PKP5Q6rP>P5Q6kP>Q5|=E5kF<PaPcb:b8b9X04%c2S2:%g<Q05[S1p1:};/G@,7}[[^04P2Q0PPqPrO3b7b@b;b<b=b>bRb1b2I0tQ4MQ0H'7P]Q1BPAQ2BQ5wQ0UP3P1Q4FQ3vQ2PQ1GQ4F#TQ3v#TQ2P#TQ1G#TQ1?Q0IQ1kPgQ4jQ4RQ4RQ34Q5\-1>Zp+09GR~Q5b#@Q4H#c[[Q2;Q1u>1=Z<UXa~Q2;Q4I#@[^a~Q2=Q3eQ3eQ3;Q3;Q4<Q0Rp+07ES2;Q0|[\QPNPFQ37PKP5Q5EP>P5Q5nP>P5p+06HP>P5Q5EP5Q0LQ3{$0n61I4-0qCH0ICrF<PaPcb:b8b9X04Q2:Q1pQ7L,7;Q25Q4k7]D[[[^04P2Q0NQ3~Q41Q1?O4b7b@b;b<b=b>bRc0zc0{b1b2g02YhQ5wQ0FQ0sCUQ1?Q0IQ1kPgQ4jQ4RQ4RQ34Q3;Q4<Q4<Q68Q68Q24Q0HQ4DPNPFQ37PKP5Q4kP>P5p+06BS2:P5Q4Up+083S0LQ4Y#N41;H0ICrPaPcb:b8b9X04Q7B,72p+07CS4I1:}<Q6{':Q593z[^04P2Q0eQ1IO2b7b@b;b<b=b>bRb1b2P^e61C^Q2YQ1?Q0IQ1kPgQ4jQ4RQ4RQ34Q3;Q4<Q4<Q68Q68Q24Q0HQ4DQ3tQ6b5H5P=Q28PFQ35PKP5Q4nP>P5Q4ZP>P5Q5GP>P5PGP>P5P5Q5M=E57Q2{P>P5PGP>P5Q4kQ5|Q4U41;I0sEQF<F<PaPcb:b8b9X04X54XA4XD4aX?[XE[Q4T,72Q48Q54Q7A?KHIQ6H,GGQ7>PHPBH07Q7F?KIBQ5n/:GQ6}Q6H,GI40=[[[[[[^04^54^A4^D4^?[^E[P2Q1MQ7]Q0eQ6<Q2IQ0hPpPrPtQ3lQ1GPbO<b7b@b;b<b=b>bRb1b2Q3vQ1280=~eQ07p+09HR=Q2O-0khQ1BQ61PhQ2OP3Q2BQ0zQ0pJ2=Q3xK2<Q5WPyp+063S0pPkQ1A?J2RRZQ1tPkQ1AQ3d;JRQ32Q0hF3XWyPyQ3dQ0XQ3290kZQ0h40QXWyPyQ7OQ0XQ10PkPZQ5>Q0kCn40QXWyPyQ3^Q0XQ10Q0VQ1x90kZS07Q0PD[XWyPyQ7CQ0XQ10Q0VQ1=PkPZQ1wQ0NCnD[XWyPyQ3ZQ0XQ10Q0VQ1=Q4OQ07Q0Q40QD[XWyPyQ3TQ0XQ10Q0VQ1=Q4OQ1<PkPZQ5iQ0ZCn40QD[XWyPyQ3YQ0XQ10Q0VQ1=Q4OQ1<Q4_Q5j90kZ'140QD[XWyQ10Q0VQ0|'1PDQ11Q4pP?Q4<Q1WQ3;P3Q12Q1[PJQ20Q1_P3Q12Q1cQ3ZQ1tQ3XQ3}Q3@p+05jRZPXQ5UH0`DRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ3u>03XseQ3u,yXeO3Q0VQ0|PDQ4pQ0rP?Q4<Q2bQ3;P3Q12Q1JPJQ20Q1LP3Q12Q1OQ3_Q6NQ7OQ32Q7CQ40Q3TQ3Sp+07?S3T,qXI0uDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ4A>03XseQ4A,yXeO3Q1=Q0hPDQ5IQ4qP?Q4<Q6MQ3;P3Q12Q2QPJQ20Q1oP3Q12Q5=Q3RQ1QQ3PQ1cPsQ5>Q3OQ43Q3BQ7TPXQ5YH0`DRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ4w>03XseQ4w,yXeO3Q4OQ0KPDQ4qP1P?Q4<Q2sQ3;P3Q12Q6FPJQ20Q1EP3Q12Q6MQ3MQ5<Q2tQ1OQ3LQ1aQ3KQ1xQ3Jp+04IQ3EQ3IQ5N,qXI0uDRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ5?>03XseQ5?,yXeO3Q1<Q0ePDQ4VQ4WP?Q4<Q2jQ3;P3Q12Q2oPJQ20Q2rP3Q12Q4;Q2kQ2RQ3FQ5=Q6jQ1Np+05US1NQ1_p+05TRkQ1wQ3CQ3NQ5aQ3APXQ5OH0`DRDRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ4\>03XseQ4\,yXeO3Q4_Q0MPDQ4WP1P?Q4<Q1bQ3;P3Q12Q45PJQ20Q2jP3Q12Q2oQ7_Q6FQ7`Q6MQ3?Q2vQ3<Q1LQ6ZQ1]p+05LS2vQ5iQ3QQ5QQ47Q3D1qX|I0uDRDRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ5C>03XseQ5C,yXeO3Q0wQ0QPDQ4^Q6QP?Q4<Q2JQ3;P3Q12Q18PJQ20Q1`P3Q12Q2hp+05IS47Q2?p+05HS6MQ4;p+05GQ1yQ6XQ1op+05ES1oQ1KQ2ZQ1[Q2XQ5jQ2VQ2\Q3=Q71PXQ4vH0`DRDRDRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFQ56>03XseQ56,yXeO3PDQ6QQ0sP?Q4<Q1^Q3;P3Q12Q2JPJQ20Q18P3Q12Q1`Q02Q2jQ3wQ2oQ5RQ2sQ4zQ1EQ2HQ1rQ2GQ1JQ6BQ1YQ6zQ2uQ7?Q2PQ7HQ05Q4c,qXI0uDRDRDRDRX`3X_3Q5hDFX^WX]JQ2SDFX\3X[3PwDFWZX4?PbDFp+076R?>03Xse1yX?eO3H0AFWFWFWQ3_Q6QQ3_Q5{Q3_+0?L0>PZQ4^PZQ5{00?ZL0>Q3XQ4WQ3XQ5{Q3X+0?L0>Q3[Q4VQ3[Q5{Q3[+0?L0>Q3]Q4qQ3]Q5{Q3]+0?L0>Q3aQ5IQ3aQ5{Q3a+0?L0>Q3bQ4pQ3bQ5{Q3b+0?L0>Q0:Q11Q0:Q5{Q0:+0?L0>Q1B$2:eQ0}Q4E1>}2P4Q3jP2P2P^H0ZQ5_Q5k/A<Q5_Q3`Q0tP2O1Q3|30W6PGP<Q0IQ0RPSPVQ4[Q4gQ4gQ4hPWQ20Q20Q2=Q2=Q3eQ0YQ0mQ53Q0h[[Q3@PFQ30?a<LPKP5P5Q3UQ7IQ4q'V9e5CP>P5P5Q4qp+07KRXP>P5Q4ZP>P5Q5GP>P5P5Q0;Q33P>Q4xEQF<J0<EQPaPcb:b8b9X04X54XA4XD4X?[Q2;P2P2Q6k/:DH0ZQ6Q,7EQ48Q54Q7K?KH6Q5GPHPHQ6|CU[[[[[^04^54^A4^D4^?[P2Q2>Q0nQ0OQ6UPpPBPrQ42Q44PbO:b7b@b;b<b=b>bRb1b2O2P;Q5k010;E~WXaW6WjQ0}PDQ4DQ3rP^PgQ0oQ4iQ4jQ4jQ4RQ3eQ3;Q3;Q4<Q4<Q68Q0EQ0|Q5FQ0U[[PNPFQ36PKP5Q6zP>P5Q4lP>P5Q7IP>P5Q4NP>P5P5Q3HQ2:P5Q2:p+06LFvF<F<PaPcb:b8b9X04X54Q6C/72Q4],7<Q25Q26Q58Q5V/:ERsPsQ5LCU[[[[^04^54P2Q0dQ0mPpPlPtQ3~O6b7b@b;b<b=b>bRb1b2Q7\Q4DQ4Dp+07@S0mCUeO2WjA0411Q0Y00W~/I1Q0=#L#@'1P4P1H0`Q0}Q0UQ5p3zQ7=P4Q63-0W2P41G<2P4Q55P[Q7J,=DP[Q0@-1<EQ4uQ6WPD[[%@HQ4IPE[[P[Q4~Q5FPH[[P[%@IS4~Q2;PG[[P[%@6R1Q5:PI[[P[%@BRsQ53P6[[P[Q7K/A6p+08OS53Q6R,:BP4Q7B,:pP4%@qPo\X[P[Q2G#TPpePpQ1i?JERQ2=Q6<,7EP[Q78/>GP4Q2dQ2A70;P[Q0eP4Q6H-0W2P4Q7<-1E<P4Q55P[Q55P[Q5L/7EP[17HXP[1GGHP4Q7E-1<IQ4~Q56PG[[Q75-1:6Q5CPG[\1Q4\P6[\sP[%@pQ5?P6[[P[%@lQ4wPp[[P[17|HP[Q77,:GP4Q7R/AIQ4W%@tQ4vPr[[P[Q11,:BP4Q4C,7DP[Q1\?JDRQ7HQ4T,7;P[Q6^/>HP4Q0a,=nP[Q0cP2eP2Q5e#TQ2nQ5e'=Q1dQ4vQ6~P<P;PmQ2nQ1@Q1HQ16Q1MQ2dPWPWQ20Q3<Q6ZQ6ZQ2vQ2vQ3QQ1eQ0jQ2FPOQ3VbFbGbHbIbJbKbLb1b2bMbNP<P;PmQ2nQ1@Q1HQ16Q1MQ2dPWPWQ20Q3<Q6ZQ6ZQ2vQ2vQ3QQ1eQ0jQ2FPOQ51Q7SPNPFQ37PKP5P5Q57Q5[9E5CP>P5Q6PP>P5Q2ZQ11Q5['VQ2C'm+0UI0sEQPaPcb:b8b9X04X?[p+0:=S2C9z<2Q1pQ6L/:;Q1u817@[[^04^?[P2Q0o#cQ0oQ17Q1IO4b7bObFbGbHbIbJbKbLb1b2bMbNI0tQ1fQ5E'7Q7WP;PDP0Q2pQ0iQ1fQ1MQ1XQ5]Q2dQ2dPWQ3?Q3<Q3<Q6ZQ6ZQ2vQ0vQ1hQ4KPe[[Q2SPOQ3WbFbGbHbIbJbKbLb1b2bMbN629vQ46Q0SQ7W3]Q0TQ4XPDPEQ2gQ2qQ0jQ1eQ1XQ1^Q46%@mQ5[Q3c[[Q7]Q7^Q7^Q5]Q7_Q7`Q7`Q3?Q3?Q3<P\Q1HQ5m%@wQ60Q2w[[Q7HQ70PNPFPLPKQ4W>055M,|5PaPcb:b8b9Q6L#gQ05[P2b7bObFbGbHbIbJbKbLbSb1b2bMbN428Q0TQ4XQ0S+1X/:v'=PEPHQ2]Q2WQ0tQ0vQ1^Q2IP{%@0Q1uPm[[P{Q2g#@RWQ5;Pm[[Q3sQ3kQ3kQ7]Q3CQ3AQ3AQ7_Q7_Q7`Q0gQ5~Q0l[\fQ3xQ5hQ6zQ7?PNPFQ36PKP5Q3^P>P5Q5_P>P5Q4GP>P5Q3aQ3\+0UI0sF<PaPcb:b8b9X04X54p+09SR@/72Q19Q1:Q5~Q7Y/:D'7[[[^04^54P2PTPgQ1GQ3vQ4DO5b7bObFbGbHbIbJbKbLbSbkb1b2bMbNQ46eQ46PHPGQ2_Q2YQ1HQ1dQ2IQ2JQ0SQ5;P0[\WQ0SQ2]#@Q0LP0[[P8Q3sQ3sQ3kPkQ3CQ3CQ3AQ3AQ7_Q1gQ1eQ3lQ5hQ6BQ6zPNPFQ36PKP5P5PCp+085RWP>P5Q6:P>P5Q5_P>Q2[Q3[5E5F<J0<PaPcb:b8b9X04X54Q3GQ19Q1:Q6P@0=DW[[[^04^54P2P`Q0oQ42Q4DQ0IO5b7bObFbGbHbIbJbKbLbSbkb1b2bMbNQ46eQ46Q5UQ3cp+0::PGPIPPQ2KQ1fP\Q2JQ1qPvP{PvP{Q2>P8P8Q3sQ1NPkPkQ3CQ3CQ3APeQ1eQ2wQ5hQ04bFbGbHbIbJbKbLbSbkb1b2bMbNPGPIPPQ2KQ1fP\Q2JQ1qPvP{PvP{Q2>P8P8Q3sQ1NPkPkQ3CQ3CQ3APeQ1eQ2wQ5hQ2GQ6BPNPFQ36PKP5Q71P>P5Q6;P>P5Q6:P>Q71CrF<PaPcb:b8b9X04X54Q60/72Q19Q1:Q4@/7D[[[^04^54P2Q0uQ2WQ3~Q0IP^O5b7bObFbGbHbIbJbKbLbSbkb1b2bMbNI0tQ3{Q3i'7PIP6Q2`Q2MQ1eQ0fQ1qQ18Q0TQ46Q0T%@PQ2]\W[Q2@Q2>Q2>P8Q6jQ1NQ1NPkPkQ3CQ1hQ5yPh[\iPwQ1D#@Q4BQ1C[[Q2HQ2GQ0CQ0B60~4Q0A'oQ0AQ7Q+1B+1WQ75Q7X-274Q0A6264Q7FQ0xQ6y402+1B+1W00vN+0vPFQ2y9aLIP;Q2z?aILP<PLPE&0GIRiPDPLD}D}PKP5Q1oP>P5Q2ZP>P5P5Q6yQ0p+0[P>P5P5Q6}#NQ7AP>P5P5PCp+065R8P>P5Q6MP>P5Q6eQ7A6254/V7:055CP>P5Q6]P>P5Q4MP>P5P5Q6|Q4{P>Q2dEQF<F<J0<J0<I0KF<PaPcb:b8b9X04X54XA4XD4XP4XY4Xo4X?[Q4GP1[\yQ55Q5_Q4u[[Q4X/:6,=GQ7>/76Q5x,7E17yHQ7[01Xl/:I,=G%cp%glQ05[p+0:XR1Q3~7KlQ6R1GplRWPWQ4>Q4LDM[[[[[[[[[[^04^54^A4^D4^P4^Y4^o4^?[P2Q3OPuQ2qQ1IQ1PQ5sQ2WQ2YP<PpPqPtQ3~Q41Q42P^Q0HPbOBb7bObFbGbHbIbJbKbLbSbkb1b2bMbNc0]c0Rc0Qc0?c0Wc0=11lGQ4\Q4\Q5?Q5?Q02P0Q4w/l<Q02P6Q4wP2H0VCnWs'8Y09Q5]Q4\Q4\Q3iQ3wPIQ5?P2H0V'1WsQ5]Q0TQ5RQ2P70GQ0GPbQ3nPRQ2_Q5]Q5DQ2qPkP;PDP0Q2pQ0iQ1fP0Q5I,7PP_P}Q2`PPP_P_P_Q7@Q2KQ2KQ2K#TQ6lQ4aQ6jN:0iQ5IQ5IQ0mL1GQ1MQ1XPnPqQ7^Q5]Q5]Q2dQ7`Q3?Q3?Q3<Q3<Q6ZQ2SPOP\Q1HQ70Q6YPNPFQ38PKP5Q6YP>Q51CrPaPcb:b8b9X04X54XA4Q23/=xQ25Q26Q27Q7DQ5V40=[[[^04^54^A4P2PSQ17Q15PtQ2EQ1?O6b7bObFbGbHbIbJbKbLbSb1H1Fb2bMbNQ4:eQ3iQ2qP;PDP0Q2pQ0iQ1fQ1MQ1XPnPqQ7^Q5]Q5]Q2dQ7`Q3?Q3?Q3<Q3<Q6ZQ2SPOP\Q1HQ70Q6YQ3VQ3LP2Q3JQ2iPhPSQ5EQ17Q15PqPtQ1CQ2EQ1?PbO=b7bObFbGbHbIbJbKbLbSb1b2bMbN+0LI0DQ0622;2RS2qP[%j<Q6^'IRhP[Q5;%j;Ru':P4Q6`PDQ3sp+071H24RWQ6`P|Q3pQ7;%jHR|,:2'AO1Q5DP<H0VXd4Q1sPHPEPG%jGRg%TgPRQ2CQ6DJ1\P2H0cPEQ5hP;Q60P;Q6lPDQ0;Q6lQ0;PRPIH1SH1TQ6lQ0;;0DQ5VP?Q5VQ4CQ5rQ7P/AGO1Q6rP2H0VWWQ17PHPlPoQ2lQ5hQ0fQ1hPEPB&16o%jo#@Q2jQ2mQ2gQ4:Q7JQ2xQ2xQ0:Q3KQ3JQ3JQ3IQ3IQ2kQ1jQ1gQ1DPwQ71Q02PNPFQ36PKP5Q7GP>P5Q4|9e5CP>P5Q53P>P5Q6UP>P5P5PXQ4zP5Q4zQ5BFvF<F<PaPcb:b8b9X04X54Q3gQ7X,I<Q25Q26p+08MRX1:XER?P?Q6DCU[[[[^04^54P2Q1ZQ0S#jPlPoQ0YQ0WO6b7bObFbGbHbIbJbKbLbSbpb1bmb2bMbNO2PEP2E~b4Q5hPBI0DPPQ5hPpPlQ2iQ2SP\PePDP6&16lRP%jl#@R?Q2hQ2jP0Q3cQ2xQ0:Q0:Q00Q3JQ3IQ3IQ2kQ2kQ3FP9PwQ1jQ1gQ02Q3wQ24Q7CP2Q3SQ2FP`PdP=Q3rQ3vPtPvQ0IQ0FQ0YPbO=b7bObFbGbHbIbJbKbLbSbpb1bmb2bMbN+0LI0DaXtEaaaaaY07N91ZQ0GPbQ3nPRPpQ5]Q5DQ42PkP;PDP0Q2pQ0iQ1fP6Q5I,7rP_P}PlPrP_P_P_Q7@PnPn%TnQ6lQ4aQ6jN:0iQ5IQ5IQ0mL1GQ1MQ1XPnPqQ7^Q5]Q5]Q2dQ7`Q3?Q3?Q3<Q3<Q6ZQ1dQ1@Q5hQ2pQ70Q6YPNPFQ38PKP5P5Q4oQ7?P>Q6YEQPaPcb:b8b9X04X54XA4X?[Q23Q7P':=zDxQ25Q26Q27Q7UQ6r40=[[[^04^54^A4^?[P2Q0TPSQ2cQ2iPrQ2EQ1?O7b7bObFbGbHbIbJbKbLbSb1H1Fb2bMbNPHePEQ42P;PDP0Q2pQ0iQ1fQ1MQ1XPnPqQ7^Q5]Q5]Q2dQ7`Q3?Q3?Q3<Q3<Q6ZQ1dQ1@Q5hQ2pQ70Q6YQ5vQ3KP2PSQ2cQ2iPrQ2EQ1?O6b7bObFbGbHbIbJbKbLbSb1b2bMbN+0LI0DQ06Q2qP[PhP[1:nuP4PWQ6`PEPDPHP|%T|PRQ6dQ2~J1\P2H0cPDPvQ5NPjQ7G%jI,:2'AO1Q6lPDH0VXd4Q5oP;Q4?Q5oQ4?PRPGH1SH1TQ5oQ4?;0;Q6lQ0;Q6lQ5YQ1zQ7N/AHO1Q5VP2H0VWWPwPEPpPlQ2iQ2SP\PePEP6PPP?Q2hQ2jP0Q3iQ2xQ0:Q0:Q00Q3JQ3IQ3IQ2kQ2kQ3FPfQ0gQ1CQ2wQ02Q3wQ7<Q6\Q0A402Q7AQ0<#uQ0xQ4}'o402/^N'^-0vx-0vxPFQ2}P;Q2y?aHLP<PLP6&0G6PDAai6LD}D}PKP5Q3QP>P5Q3DP>P5P5PMQ0yP>P5P5Q0yQ5V+0qP>P5P5Q0>#pQ4F+0[P>P5P5Q6KQ6H'V-0[CP>P5P5Q47Q0?P>P5P5Q5_Q6HP>P5P5Q6HQ6<P>P5P5Q6y-0qMP>P5Q6y>055M,|5P>P5P5P5P~Q6JQ4eI0oP>P5P5Q5PQ0`P5Q0`Q7IFvF<I0KJ0<J0<EQI0KI0KI0KJ0<F<PaPcb:b8b9X04X54XA4XD4XP4XY4Xo4Z064X?[XE[Q6;Q6DPs[[Q55Q4u\X[Q4up+0:Z,IHp+0:?/:l,=pQ6G/:p,=HQ6IQ21;KrQ76/7oQ4},7q%cq%grQ05[Q7bQ497KrQ4Y1Goq/:rRsPsQ59CU[[[[[[[[[[[[^04^54^A4^D4^P4^Y4^o4`064^?[^E[P2Q3SP0Q5`Q3vP`PdP=%j{POQ2FP<PBPlPoPrPtQ0SQ0IP^Q0FQ0YPbOFb7bObFbGbHbIbJbKbLbSbpb1bmb2bMbNO2PDP2E~b4PlPBPpQ2cQ2FQ1dQ1gPDPI&16p%jp#@Q45Q2hPmQ4:Q0:Q00Q00Q7=Q3IQ2kQ2kQ3FQ3FQ6jQ0lQ0gP9Q2wQ3wQ5RQ5QQ3SP2Q1VQ2MPOP{Q0RQ0FO6b7bObFbGbHbIbJbKbLbSbpb1bmb2bMbN-0LvI0DaXtDaaaaY07N91ZH0AH0XH0Xc0Sc0Aaaaaaaaaaaaaaaaaaaaaaaac10aaaaaaaaaaaaaaaaaaac0~Q08Q08Q3WQ0iQ6{Q3N'A;JRQ09/l<Q3WQ0iQ6{Q1?'APRQ09/l2DZCnXsJ,8JY09'8eY0JQ0zPdQ1BQ0RQ1T/1SQ5mQ1TPSQ5hPTPVQ2SP`Q0qQ2FQ1PQ0uPOQ2MH0AFWFWQ5wQ0UP3PdH21eQ1BQ1B81A3R`Q1BQ1B+06RVQ2BP3Q0zQ1BH12RT'1Q7@/>2P4Q13,I2Q2O/72'4Q5XQ0iP;O1'qWjaX6yP`ePVPTQ1AP2O1Q3U50J$0OP2WXX6yPVeQ0_Q0^Q0k'1PtQ0^Q0kPrQ0]Q0PPqQ0\Q0NPoQ0[Q0ZPlPpH0AFWFWPTeFWQ1BQ2BP3Q0zQ1BI0FePBNQ201DYyRTQ3eQ3eQ1AP]P<Q3pP2PAQ3>Q67,2<RlQ0UQ3>Q5`,2<RrQ1vQ3>Q0`,2<RVQ3pQ3>Q66Q22Q3>Q65Q0zQ3>Q5fQ3oQ3>Q5^Q3nQ3>Q69Q1lQ1\Q1@Q3pQ2OQ2BP2I0F80P<F3F3F3F3FCWn'8XqT'8Q03Q4E,DYRTQ2=Q2=Q1@P]P<Q1{P2PAQ4G12<yRyQ0|Q4GPlQ3zQ4GPrQ1{Q4GPVQ2BQ4GQ66Q22Q4GQ5dQ0zQ4GQ5gQ3oQ4GQ65Q3nQ0{Q0iQ1{Q14Q2fP2I0F80P<F3F3F3F3FCWn'8XqTQ3>,DYRTQ20Q20Q0iP]P<PjP2PAQ5_P<Q4EPQQ5_PyQ12Q5_PlPjQ5_PrQ2fQ5_PVQ2BQ5_Q5cQ22Q5_Q5fQ0zQ5_Q66Q3oPUP<Q5_Q1>1>@2RVPVQ16CBp+073Q1HP<O170z[]6Q0jP2G`F3F3F3D?FCWB'8XCT'8P2Q4G,DYQ5_P2Q67PjCXP[Q6:P<Q3>Q0hCXP[Q6;P;Q3>Q13CXP[Q6<PDQ4EPjCXP[Q2~PEQ4EPjCXP[Q6DPHQ4KPjCXP[PXPGQ0LPjCXP[Q6UPIQ4GPjCXP[Q2>Q2>Q0fP]PBQ1vP2PAPIPGP6PHPEPDP;P<Q2BQ0gQ1vQ1bQ3yP2I0F80PBD[D[FCWn'8Q03Q2@Q2@Q0gP]PpQ3zP2PAP6PIPBPGPHPEPDP;Q2fQ1gQ3zQ1`Q61P2I0F80PpD[D[FCWnQ4M,DYRIQ00Q00PeP]P<P3P2PAQ4LQ6TQ0QQ4LP<Q53Q1qQ4LQ6VP3Q4LP<PXQ1vQ4LQ6OQ61Q4LQ5zQ3yQ4LQ5}Q64Q4LP<Q2~Q2^Q1{P<Q4LQ2hQ7:/>2RXPXQ2jCBQ3TQ1FP<O170z[]6Q1hP2DiGdF3GdGdFCWB'8XCI'8P2Q00Q1{Q1hP3Q2hQ3zP2I0F80PoP[Q1i006<Q13Q2jQ12P<H12'1P[Q01Q2mQ78/>2RIPIQ2oCBQ7\PEP<O1PfP<O130[]6P[Q1FP]PtQ14PDPAJ1bP[116DP[Q1j>13;HP[Q3qP[Q64Q44<0P<P[Q6=P[11q<P[Q4=P[Q3~/1<P[Q6>P[Q44/1<P[11v<RHP[Q6?P[PHP[PHP[Q4:/1<P[11m<P[Q3c/12P[Q41/1;P:Q42PDQ6AP2Q49P:Q2`PBQ6_P2Q2cP:Q2iPtQ1mP2Q2nQ42P:Q2YPnQ6EP2Q2MQ0SP:Q2KQ3iQ5lP2P:Q2FQ2]Q5SP2Q5hQ2`P:Q5mQ2iQ3{,DYRtQ3MQ3MQ1vP]P<Q1]P2PAQ5sQ5p,2<R[Q0qQ5sQ6mQ2uQ5sQ6uQ1]Q5sQ6wQ1WQ5sQ6gQ1UQ5sQ6aQ1SQ5sQ6cQ1QQ5sQ6pQ1OQ2bP<Q5sQ5>Q6s/>2RHPHQ32CBQ5[P3P<O170z[]6Q3zP2DiF3F3F3F3FCWB'8XCt'8P2Q3xQ2pP:Q3lQ2YQ5w,DYRtQ3PQ3PQ13P]P<Q6NP2PAP=Q5u,2<R3Q1PP=Q5s,2<RHQ1xP=Q5q,2<RfQ6NP=P<Q3{Q1_P=P[Q1]P=Q6fQ1[P=Q4rQ1YP=Q6mQ1WQ1LP<Q2Ap+0:T/>2RIPIQ1|CBQ4KQ1>P<O170z[^6=Q2OP2DiF3F3GdF3FCWB'8XCt'8P2P:Q17Q5WQ5Z,DYRtQ7CQ7CQ16P]P<Q6SP2PAQ5TQ63,2<RIPdQ5T12<=R=Q2eQ5TP<P~Q6SQ5TP<Q5wQ2<Q5TP3Q6NQ5TQ6hQ1cQ5TQ6iQ1aQ5TPHQ1_Q1SP<Q5TQ2T1>12R1P1Q1nCBQ5~Q1^P<O170z[]6Q1MP2DiF3F3D?D?F3FCWB'8XCt'8P2Q2wP:Q1UQ4D'{Q1XQ2aQ1nQ6qQ17I0FQ5{,DYRtQ2IP]P<Q5jP2PAP}Q0@,2<R1PUP}Q5T,2<RUQ4PP}P<Q5tQ5jP}P<Q5ZQ2aP}PIQ6SP}Q6nQ6qP}Q6oQ72P}P=Q2<Q1[P<Q4RQ79/>2R=P=Q4jCBQ4BQ18P<O170z[^6}Q2JP2DiF3F3D?D?F3FCXBZ,8ZXCt'8P2Q1Y/{^Q2JQ5jQ4RQ6vQ1CI0FP:Q1qQ4jQ1D41AP9Q5k,DYR^Q3]Q3]Q1bP]P<Q5>P2PAQ73Q6{,2<RtQ1lQ7312<}R}Q34Q73P<Q7@Q5>Q73P<Q5{Q5iQ73P1Q5jQ73Q6pQ2uQ73Q6tQ6vQ73PUQ2aQ1cP<Q73Q4gQ7b/>2RUPUQ4[CBQ0`Q2hP<O170z[]6Q1`P2DiF3F3D?D?F3FCWB'8XC^'8P2Q1bQ4hQ1G41AQ6[P:Q45Q2E+06Q32Q4[Q1xQ2EH12Q7A,DYR:Q3dQ3dQ2jP]P<Q2AP2PAQ7FQ7B,2<R^Q22Q7FQ73,2<RUQ4hQ7F12<@R@Q2AQ7FP<Q5kQ32Q7FPtQ5>Q7FQ6mQ1xQ7FQ6wQ1wQ7FP}Q5iQ6qP<Q7FQ4`p+0:d/>2R}P}Q4xCBQ4EQ2?P<O170z[]6Q2mP2DiF3F3GdF3FCWB'8XC:'8P2Q2jQ3r+06Q2AQ4`Q1tQ3vH12Q7L,DYRYQ2?P]P<Q4PP2PAQ6}P<Q7FQ3pQ6}P<Q6yQ5@Q6}P<Q7AQ4PQ6}P^Q2AQ6}PUQ2eQ6}PfQ1tQ6}P[Q32Q6}P@Q5>Q6vP<Q6}Q2NQ5A/>2R@P@Q5vCBQ5_Q4;P<O170z[]6Q2rP2G`F3F3D?D?D?FCXB8,88XCYPQp+064RYQ2oP]Q0hQ62P2PAQ0|Q0UPQQ0JQ0WQ0YQ0FQ0RQ2aQ0hQ7KQ5Kp+0:f/>2RAPAQ2NCBQ4GQ2sP<O170z[]6Q2?P2DiD[D[FCXBYQ4DQ2EQ0UQ2F'1Q2YQ0UQ2FQ2nQ0JQ2SQ31Q0|Q5mQ2]Q0WQ3xQ3cQ0YQ2wPvQ0FQ17PnQ0RP9Q41Q0EQ1DPqQ6S/{QQ1GPBQ1?Q2oQ4D+06Q7Lp+0:e/>2P4Q5KP2P2Q2NCBP6P;Q0~Q3nQ1WQ1YQ2vQ3QQ3QQ3Dp+067Q3fQ3fP8P8PYQ0zQ1zQ4YPj[[PNPFQ38PKP5P5P5Q5CPCAe5C7I0o,|5P>P5Q4pP>P5Q4tP>Q5C9e5CAE57C6085CrF<PaPcb:b8b9X04X54XA4P<p+0:mP21I2<H07Q05[Q25Q26p+0;0,GE,IDQ4s'4[[[^04^54^A4P2Q3zQ5QPpPBQ0ZQ0[O6b7b@b;b<b=b>bRb1b2O2Y0[aW6P<H0AFWFWFWFWFWH0XH0XWjY0CP<P2O2n2001000000121000000W4Y0\P<P2O2n2001000000121000000W4WuP<P2O2n2001000000121000000W4X{9P<P2O2n2001000000121000000X4OXywP<P2O2n2001000000121000000W4WxP<P2O2n2001000000121000000W4W}P<P2O2n2001000000121000000X4mX|OP<P2O2n2001000000121000000W4WvP<P2O2n2001000000121000000W4WzP<P2O2n2001000000121000000X4oWwP<P2O2n2001000000121000000X4GY04P<P2O2n2001000000121000000W4aaaaaaaaaaaaaaaaaaaaaWBP<P2O2n2001000000121100000W4aaaaaaaaWCP<P2O2n2001000000121100000bgc0>c0@c0fc0<c0yc0KY0LP2O1n200111400021110211103c15c0tc0sc0rc0qc0pc0oc0nY0mY0lP<P2O2n2001000000121000000W4Y0kP<P2O2n2001000000121000000W4Y0jP<P2O2n2001000000121000000W4Y0iP<P2O2n2001000000121000000X4QY0hP<P2O2n2001000000121000000W4Y0gP<P2O2n2001000000121000000b4c0Gc0vc0uc0Fc0Nc0OY0`Y0bY0aY0^Y0_W~Y0MY0xY0PY0HY0Eaaaaaaaaaaaaaaaaaaaaaablaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac0Xaaaaaaaaaaaaaaaaaaaaac0DaaaaY0|aaaaaaaaaaY0daaaaaaaaaaY0caY13aaaaaaaaaaaaaaaZ144Y12Y0VY0:Y0}Y0UY0BY0Taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

  Lemma aread_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (cnt : Z) pth off data so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 3 -> getr R 11 = Z_to_bv 64 STAGE -> getr R 12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    fd_lookup (m_fds model) (Z_to_bv 64 3) = Some (FdFile pth off) -> fs_lookup (m_fs model) pth = Some data ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    (forall R' M' (model' : Model),
       let bs := file_read data off (Z_to_bv 64 cnt) in
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = len_word bs ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_readA so bls vbnd kn) ->
       dinvA LB LK cr A M' model' ->
       m_fds model' = fd_insert (m_fds model) (Z_to_bv 64 3) (FdFile pth (off + len_word bs)) -> m_fs model' = m_fs model ->
       rdn ASEGS M' (Z_to_bv 64 STAGE) (length bs) = Some bs ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 + so - 2200 <= a < bv_unsigned sp0 + so) -> ~ (STAGE <= a < STAGE + 65536) ->
                  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6a2b8) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A cnt pth off data so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hfsl Hbl Hvb CONT.
    pose proof Hsp as Hsp'. unfold STAGE in *.
    set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
    assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
    assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
    { replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
      apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
    assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); unfold s in Hx; lia. }
    assert (VST : forall x : word, 0x6820d0 <= bv_unsigned x < 0x6820d0 + 65536 -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
    assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
                 rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
    { intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell _ _ _ _ _ _ _ a n v HH Hin)|].
      apply (avoid_img _ _ _ _ _ _ _ a (Z.to_nat n) HH);
        unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
    (* [comment removed for export] *)
    destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x6820d0 cnt
                ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
      as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
    1: { rewrite <- (w_lit 0x160758 (0x160758%bv : word) eq_refl). exact (CV 0x160758 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: { rewrite <- (w_lit 0x158bf0 (0x158bf0%bv : word) eq_refl). exact (CV 0x158bf0 8 0x14f76c ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
    rewrite (w_lit 0x6a2b8 (0x6a2b8%bv : word) eq_refl).
    apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
    intros model1 MI1 SBM1 EQV1.
    destruct (sbm_fds _ _ SBM1) as (F1 & F2).
    (* [comment removed for export] *)
    eapply (rz_read_file_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) pth off data cnt K); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - rewrite F1. exact Hfd.
    - rewrite F2. exact Hfsl.
    - exact A12.
    - lia.
    - lia.
    - lia.
    - rewrite A11.
      apply (store_ok_window ASEGS _ (Z_to_bv 64 0x6820d0) (Z_to_bv 64 0x6820d0) 65536%nat (Z.to_nat cnt) 0x6820d0 0x6920d0);
        first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
    - rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
    - rewrite A11, (sbm_lazy_eq _ _ SBM1).
      apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ model _ _ HH); [rewrite u_small by lia; lia|].
      intros k Hk. left. rewrite u_small by lia. lia.
    - cbv zeta. rewrite A11, A12.
      set (bs := file_read data off (Z_to_bv 64 cnt)).
      set (n := Z.of_nat (length bs)).
      assert (Hn : 0 <= n <= 65536).
      { unfold n, bs. rewrite length_file_read. unfold word_to_nat. rewrite (u_small cnt) by lia. lia. }
      replace (v_addi (0x149d40%bv : word) 4) with (0x149d44%bv : word) by (apply bv_eq; reflexivity).
      set (raw := Z_to_bv 64 ra) in *.
      set (M2 := wbytes (munrestrict H M (RDA MV raw s R)) (Z_to_bv 64 0x6820d0) bs).
      set (R2' := regupd Ra 10 (len_word bs)).
      set (model2 := with_fds (fd_insert (m_fds model1) (Z_to_bv 64 3) (FdFile pth (off + len_word bs))) model1).
      assert (EL2 : m_vm_lazy model2 = m_vm_lazy model) by (unfold model2; rewrite with_fds_vm_lazy; exact (sbm_lazy_eq _ _ SBM1)).
      assert (EH2 : ahid A model2 = H) by (unfold H; apply ahid_same_lazy; exact EL2).
      assert (Hh2 : m_halted model2 = None) by (unfold model2; rewrite with_fds_halted'; rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
      assert (MI2 : MInv A model2) by (apply (minv_same_vm A model1 model2); [unfold model2; apply with_fds_vm | exact MI1]).
      assert (Hbs : Z.of_nat (length bs) <= 65536) by (fold n; lia).
      (* [comment removed for export] *)
      destruct (rd_post LB [] LK cr A M model s raw R R2' bs HH Hbs ltac:(unfold s; lia) WOK ltac:(apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2))
        as (R3 & M3' & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3 & OUT3 & GR3).
      1: { unfold R2'. rewrite getr_same by discriminate. reflexivity. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A9. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
      unfold rd_MV2 in RUN3, OUT3, GR3. fold H in RUN3, OUT3, GR3. fold MV in RUN3, OUT3, GR3. unfold STAGE in RUN3, OUT3, GR3. fold M2 in RUN3, OUT3, GR3.
      apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model2 K HOFF asegs_wx ltac:(rewrite EL2; exact HLC) HAWF MI2 Hh2 RUN3).
      intros model3 MI3 SBM3 EQV3.
      set (M3 := munrestrict H M2 M3') in *.
      (* [comment removed for export] *)
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x6820d0 <= a < 0x6820d0 + 65536) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N1 N2. unfold M3, munrestrict.
        assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { unfold M2, MV. apply (rd_M2_out H M s raw R bs Hs Hbs); rewrite u_small by lia; unfold STAGE; lia. }
        destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
        rewrite OUT3 by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. exact E2. }
      assert (GRW : forall x : word, M x <> None -> M3 x <> None).
      { intros x Hd. unfold M3, munrestrict.
        assert (E2 : M2 x <> None) by (unfold M2, MV; apply (rd_M2_grows H M s raw R bs); exact Hd).
        destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold mrestrict. rewrite Hx. exact E2. }
      assert (EV3 : vml_of model3 = vml_of model).
      { rewrite (sbm_vml _ _ SBM3). unfold model2. rewrite (vml_same_vm model1 _ (with_fds_vm _ model1)). exact (sbm_vml _ _ SBM1). }
      assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh2).
      assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model2 model3 SBM3); exact EH2).
      assert (DI3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3 | rewrite (sbm_rdrA _ _ SBM3); unfold model2; rewrite with_fds_rdr; exact (sbm_rdrA _ _ SBM1)].
        intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
        - right. left. unfold s in Hr. lia.
        - right. right. exists 0x6820d0, 0x693aa8. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
      assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
      { assert (KK : forall r : reg, In r callee_saved -> ~ In r OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0ReadIcpt.RIPL -> getr R3 r = getr R r).
        { intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
          intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
        - rewrite O2, R2. reflexivity.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - exact O8.
        - exact O9.
        - exact O18.
        - exact O19.
        - exact O20.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate. }
      apply (CONT R3 M3 model3 HL').
      + rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
      + exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
      + (* [comment removed for export] *) rewrite EH3. unfold keep_readA.
        pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R3)) ebs)
                  (fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x6820d0 <= a < 0x6820d0 + 65536))
                  (fun a => s - 2200 <= a < s)
                  _ MV (mrestrict H M3) _ _ kn HK1).
        * assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x6b6000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
            by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
          constructor; cbn [ev]; rewrite ?P0'.
          -- lia.
          -- lia.
          -- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
          -- intros z Hz. right. unfold s. lia.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
             pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
             destruct SBk as (cap & Hnb & Hin & HB).
             split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
             apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i [].
          -- intros lo hi Hin. unfold IMG_NOSTAGE in Hin. cbn [In] in Hin.
             repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
             destruct Hin.
          -- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
             intros Mx d m Hd Hm.
             apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x6820d0) (Z_to_bv 64 d) 65536%nat m 0x6820d0 0x6920d0);
               first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
        * intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
        * intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
          apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
      + exact DI3.
      + rewrite (proj1 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fds, F1. reflexivity.
      + rewrite (proj2 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fs. exact F2.
      + fold bs. rewrite <- (rd_stage_bytes H M s raw R bs Hbs). unfold STAGE. fold MV. fold M2.
        apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
        unfold M3, munrestrict. rewrite (VST x) by lia. rewrite OUT3 by lia. unfold mrestrict. rewrite (VST x) by lia. reflexivity.
      + exact FRM.
  Qed.
End DrvRead.
End FPX_1.

End Na0DrvRead.
Module Na0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition STOPS_LA : list Z := 0xaeab4 :: STOPSA.
Definition runLA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_LA scr ss [].

(* [comment removed for export] *)
Definition kn_blk2A (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16].

(* [comment removed for export] *)
Definition keepalloc_G (kn : list kentry) : list kentry := keep_allocA MSO 4096 [(48%nat, 65536)] [] kn.

(* [comment removed for export] *)
Definition below_frameA (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) off) _ _ => (off <? -128) | _ => false end.
Definition knLP6A : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frameA K)) keepB.
Definition knLPA : list kentry := kn_blkA 48 65536 ++ knLP6A.

(* [comment removed for export] *)
Definition srLPA : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 6896384; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 6824144; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37].

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runLA scr0 (SS 0xaea80 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPpA : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLPA.
Definition rPa := Eval vm_compute in runLA (SCR [false; false] [] []) (SS 0xaeab4 srLPA [] knLPpA 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition rPb := Eval vm_compute in runLA (SCR [false; true] [] []) (SS 0xaeab4 srLPA [] knLPpA 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
Definition want_xA : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRDA : list expr := sr_upd (sr_upd srPa (ridx 12) (EVar 71)) (ridx 23) (EVar 29).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srRA0 : list expr := Eval vm_compute in sr_after_call_j srRDA (map ridx c_kept) 72.
Definition knRA : list kentry := Eval vm_compute in keep_readA MSO [(48%nat, 65536)] [] knLPA.
(* [comment removed for export] *)
Definition knRe0A : list kentry := KRange (EVar 82) 1 65536 :: knRA.
Definition rRe_tk := Eval vm_compute in runLA scr0 (SS 0xaeb14 srRA0 [] knRe0A 104).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx c_kept) 104.
Definition knRm0 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knRe0A.
Definition rRm := Eval vm_compute in runLA scr0 (SS 0xaeaac srRm0 [] knRm0 136).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
Definition len_xA : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition knRf0A : list kentry := KRange (EVar 82) 0 0 :: knRA.
Definition rRe_ft := Eval vm_compute in runLA scr0 (SS 0xaeb14 srRA0 [] knRf0A 104).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition cellCA : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0xaeb28).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint expr_canon (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => (Nat.ltb v 6 || Nat.eqb v 38 || Nat.eqb v 48 || Nat.eqb v 70)%bool
  | EAlu _ a b => (expr_canon a && expr_canon b)%bool
  | EMd _ a b => (expr_canon a && expr_canon b)%bool
  | _ => false
  end.
Fixpoint relay_sr_from (i : nat) (sr : list expr) : list expr :=
  match sr with [] => [] | e :: r => (if expr_canon e then e else EVar (6 + i)) :: relay_sr_from (Datatypes.S i) r end.
Definition srGLA : list expr := Eval vm_compute in relay_sr_from 0 (sr_upd srRe_ft (ridx 10) (ELit 0)).
Definition knGbaseA : list kentry := cellCA :: knLPA.
Definition knGA (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbaseA.

(* [comment removed for export] *)
Definition knLPgA : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLPA.
Definition rGa := Eval vm_compute in runLA (SCR [true] [] []) (SS 0xaeab4 srLPA [] knLPgA 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition cap2_xA : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2A 81 ++ keepalloc_G knLPgA.
Definition rGb := Eval vm_compute in runLA scr0 (SS 0xaead4 srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx c_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keepalloc_G knGb0.
Definition rGc := Eval vm_compute in runLA scr0 (SS 0xaeaf0 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knGc0.
Definition rGd := Eval vm_compute in runLA scr0 (SS 0xaeaf8 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).

(* [comment removed for export] *)
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.

End FPX_1.

End Na0DrvG_defs.
Module Na0DrvStdio.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition PR_CELLS : list (Z * Z * Z) :=
  [(0x160758, 1, 1); (0x160759, 1, 1); (0x1f15fc, 1, 1); (0x15fa78, 8, 0x7fff8000);
   (0x158c20, 8, 0x146850); (0x158c28, 8, 0x14056c); (0x158da0, 8, 0x148d68); (0x158da8, 8, 0x14916c)].

(* [comment removed for export] *)
Definition EX_CELLS : list (Z * Z * Z) :=
  [(1412008, 8, 1412008); (1412520, 8, 1347948); (1426368, 8, 1); (1426448, 1, 0); (1430160, 4, 1); (1430320, 8, 0); (1438428, 1, 1); (1440376, 8, 2147450880); (1443672, 1, 1); (2037280, 8, 18446744073709551615); (2038048, 1, 0); (1430164, 1, 0)].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DG_CELLS : list (Z * Z * Z) := [(1443672, 1, 1); (1443673, 1, 1); (2037244, 1, 1); (1440376, 8, 2147450880); (1412136, 8, 1312108); (1412512, 8, 1346920)].
(* [comment removed for export] *)
Definition DGS_CELLS : list (Z * Z * Z) :=
  [(1412432, 8, 1349772); (1412064, 8, 1346668); (0x15fa78, 8, 0x7fff8000); (0x160768, 8, 0); (0x160770, 8, 0); (0x160760, 8, 2 ^ 47 - 1); (0x1f16a3, 1, 1); (0x160759, 1, 1); (0x158da0, 8, 0x148d68)].

(* [comment removed for export] *)
Lemma rdn_tr : forall (M M' : word -> option byte) a (n : nat) bs,
  rdn ASEGS M (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn ASEGS M' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M M' a n bs H Ha Hn HF. rewrite <- H. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HF. lia.
Qed.

(* [comment removed for export] *)
Lemma img_cell : forall (MV : word -> option byte) a (n : nat) bs,
  rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> MV (Z_to_bv 64 i) = None) ->
  rdn ASEGS MV (Z_to_bv 64 a) n = Some bs.
Proof. intros MV a n bs H Ha Hn HN. exact (rdn_tr (fun _ => None) MV a n bs H Ha Hn HN). Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Stdio.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Lemma vis_low : forall LB LK cr A M (model : Model) a, dinvA LB LK cr A M model -> 0 <= a < 0x6b6000 -> ahid A model (Z_to_bv 64 a) = false.
  Proof. intros LB LK cr A M model a D Ha. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
  Lemma vis_stk : forall LB LK cr A M (model : Model) a, dinvA LB LK cr A M model -> usp - 8388608 <= a < 2 ^ 64 -> ahid A model (Z_to_bv 64 a) = false.
  Proof. intros LB LK cr A M model a D Ha. pose proof Hsp. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.

  (* [comment removed for export] *)
  Lemma pr_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) PR_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hpr _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6b6000).
    { unfold PR_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u_small a) by lia. apply (vis_low _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stk_wr : forall vals ebs MV kn a n,
    know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    usp - 6144513 <= a -> a + n <= usp ->
    forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true.
  Proof.
    intros vals ebs MV kn a n HK Hw P0 Ha Hn d k Hd Hk.
    pose proof (window_store_ok sp0 vals ebs MV kn (a + d - usp) k HK Hw P0 ltac:(lia) ltac:(lia)) as W.
    replace (usp + (a + d - usp)) with (a + d) in W by ring. exact W.
  Qed.
  Lemma stk_def : forall vals ebs MV kn a n,
    know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    usp - 6144513 <= a -> a + n <= usp ->
    forall i, 0 <= i < n -> MV (Z_to_bv 64 (a + i)) <> None.
  Proof.
    intros vals ebs MV kn a n HK Hw P0 Ha Hn i Hi. pose proof Hsp.
    pose proof (stk_wr vals ebs MV kn a n HK Hw P0 Ha Hn i 1%nat ltac:(lia) ltac:(lia)) as W.
    apply (store_ok_defined sp0); [lia | exact W].
  Qed.

  (* [comment removed for export] *)
  Lemma stk_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
    (usp - 8388608) / 8 + 0x7fff8000 <= x <= (usp - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model x D Hx. pose proof Hsp as Hsp'. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & STSH & _).
    assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
    assert (IS : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) x).
    { unfold in_shadow_of, S, SB. rewrite CE, (dla_sptop _ _ _ _ DL). replace (usp - 8388608 + (usp - (usp - 8388608)) - 1) with (usp - 1) by ring. exact Hx. }
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ STSH IS).
    apply (di_stksh _ _ _ _ _ _ _ _ _ _ D). unfold in_shadow_of, S, SB, STKTOP. rewrite CE, (dla_sptop _ _ _ _ DL).
    assert (MX : usp <= Z.max usp (ar_stack_top ar)) by lia.
    split; [lia|]. assert ((usp - 1) / 8 <= (usp - 8388608 + (Z.max usp (ar_stack_top ar) - (usp - 8388608)) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hi_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
    shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->            (* [comment removed for export] *)
    (usp - 8388608) / 8 + 0x7fff8000 <= x <= (2 ^ 47 - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model x D SAH Hx. pose proof Hsp as Hsp'.
    assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
    assert (IS : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x).
    { unfold in_shadow_of, S, SB. rewrite CE. replace (usp - 8388608 + (2 ^ 47 - (usp - 8388608)) - 1) with (2 ^ 47 - 1) by ring. lia. }
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SAH IS). exact (di_hish _ _ _ _ _ _ _ _ _ _ D x IS).
  Qed.

  (* [comment removed for export] *)
  Lemma img_sh0 : forall LB LK cr A M (model : Model) a n x, dinvA LB LK cr A M model ->
    0x10000 <= a -> a + n <= 0x6b6000 -> 0 < n -> Forall (fun r => a + n <= fst r \/ snd r <= a) (icl_poison IL) ->
    a / 8 + 0x7fff8000 <= x <= (a + n - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model a n x D Ha Hn Hp HP Hx. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH a n) as (Z0 & SA);
      [rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | exact Hp | exact HP |].
    assert (IS : in_shadow_of a n x) by (unfold in_shadow_of, S, SB; exact Hx).
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SA IS). exact (Z0 x IS).
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_clear : forall E MV kn lo hi, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KImg lo hi)) kn = true ->
    forall i, lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Proof.
    intros E MV kn lo hi HK Hb. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. exact (proj2 (proj2 X)).
  Qed.
  Lemma kword_lit : forall E MV kn a (w : nat) v, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KWord (SA (ELit 0) a) w v)) kn = true ->
    0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
    rdn ASEGS MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
  Proof.
    intros E MV kn a w v HK Hb Ha Hw. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. destruct X as (_ & _ & X).
    unfold adenot, v_addi in X. cbn [a_base a_off edenot] in X. rewrite (u_small 0) in X by lia. rewrite Z.add_0_l in X. exact X.
  Qed.
End Stdio.
End FPX_1.
End Na0DrvStdio.
Module Na0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_HA : list Z := 0xaeb54 :: 0xaecfc :: STOPSA.
Definition runHA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_HA scr ss [].

(* [comment removed for export] *)
Definition kn_hdrA : list kentry :=
  [KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGLA : list kentry := kn_hdrA ++ knGA 6 67108863.

(* [comment removed for export] *)
Definition scr_fallA : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runHA scr_fallA (SS 0x149d44 srGLA [] knGLA 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
Definition cfglen_xA : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_xA : expr := Eval vm_compute in nth 21 srHa (ELit 0).
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_xA (EVar 74)) (map (esub cfglen_xA (EVar 73)) srHa).
Definition PXA : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bmA : list kentry :=
  [KRange (EVar 73) 0 32767;
   KWord (SA PXA 2) 1 (EVar 75); KWord (SA PXA 3) 1 (EVar 76); KWord (SA PXA 4) 1 (EVar 77); KWord (SA PXA 5) 1 (EVar 78);
   KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bmA ++ kn_after rHa knGLA.
Definition rHb := Eval vm_compute in runHA scr0 (SS 0xaeb54 srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
Definition plen_xA : expr := Eval vm_compute in nth 13 srHb (ELit 0).

(* [comment removed for export] *)
Definition srT0A : list expr := Eval vm_compute in map (esub plen_xA (EVar 79)) srHb.
Definition kn_tgtA : list kentry :=
  [KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0A : list kentry := kn_tgtA ++ knGLA.

Definition summH (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Lemma hdr_itinerary_okA :
  (s_pc (fst (fst rHa)), snd (fst rHa), s_log (fst (fst rHa))) = (0xaeb54, [SCBr false BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_xA (ELit 6))], [])
  /\ kn_after rHa knGLA = knGLA
  /\ (s_pc (fst (fst rHb)), snd (fst rHb), s_log (fst (fst rHb))) = (0xaecfc, [], [])
  /\ kn_after rHb knHb0 = knHb0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma knT0A_sub : ksubl_b (kn_tgtA ++ knHb0) knT0A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma knHb0_eq : knHb0 = kn_bmA ++ knGLA.
Proof. vm_compute. reflexivity. Qed.
End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_2. Context {fx : PropExec.FPState}.

Definition cfgFA (v71 v72 : word) : word :=
  edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_xA.
Lemma cfglen_x_cfgFA : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_xA = cfgFA (vals_ev vals 71) (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Definition zseqA (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseqA : forall n z, In z (zseqA n) <-> 0 <= z < Z.of_nat n.
Proof.
  intros n z. unfold zseqA. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Definition cfgGA (v72 : word) : word :=
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgHA (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_splitA v71 v72 : cfgFA v71 v72 = bv_or (cfgGA v72) (cfgHA v71).
Proof. reflexivity. Qed.
Lemma cfgG_tabA : forallb (fun b1 => Z.eqb (bv_unsigned (cfgGA (Z_to_bv 64 b1))) (256 * (b1 mod 128))) (zseqA 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tabA : forallb (fun b0 => Z.eqb (bv_unsigned (cfgHA (Z_to_bv 64 b0))) b0) (zseqA 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tabA : forallb (fun a => forallb (fun b => Z.eqb (Z.lor (256 * a) b) (256 * a + b)) (zseqA 256)) (zseqA 128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cfgF_valA : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  cfgFA (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgG_tabA as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseqA 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
  pose proof cfgH_tabA as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
  pose proof lor_tabA as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128) (proj2 (in_zseqA 128 (b1 mod 128)) ltac:(cbn; lia))).
  rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
  apply bv_eq. rewrite cfgF_splitA, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
  assert (E : (b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0).
  { pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
    symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
  rewrite E. apply u_small. lia.
Qed.

Definition sx8FA (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8FA : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) sx8_xA = sx8FA (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Lemma plen_x_eqA : plen_xA = EAlu ALU_ADD (EAlu ALU_ADD (EVar 70) (EMd M_MUL (ELit (-1)) (EVar 73))) (ELit (-6)).
Proof. reflexivity. Qed.
Lemma mod_of_decompC : forall a b q r, 0 < b -> 0 <= r < b -> a = b * q + r -> a mod b = r.
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmulA : forall a c : Z, 0 <= c <= a -> a < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c)) = Z_to_bv 64 (a - c).
Proof.
  intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  destruct (Z.eq_dec c 0) as [->|Hnz].
  - rewrite Z.mul_0_r. change ((0) mod 2 ^ 64) with 0. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decompC ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
    rewrite (mod_of_decompC (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglitA : forall a k : Z, k <= 0 -> 0 <= a + k -> a < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eq_dec k 0) as [->|Hnz].
  - change ((0) mod 2 ^ 64) with 0. rewrite !Z.add_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decompC k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
    rewrite (mod_of_decompC (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_valA : forall (Lz Cc : Z) vals bl,
  0 <= Cc -> 6 + Cc <= Lz < 2 ^ 32 ->
  vals_ev vals 70 = Z_to_bv 64 Lz -> vals_ev vals 73 = Z_to_bv 64 Cc ->
  edenot (Env (vals_ev vals) (blobs_ev bl)) plen_xA = Z_to_bv 64 (Lz - 6 - Cc).
Proof.
  intros Lz Cc vals bl HC HL P70 P73. rewrite plen_x_eqA. cbn [edenot ev]. rewrite P70, P73.
  rewrite add_negmulA by lia. rewrite add_neglitA by lia. f_equal. lia.
Qed.

End FPX_2.

End Na0DrvC_defs.
Module Na0DrvPiece.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Piece.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_okB L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable M0 : word -> option byte.

#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation rom := (seg_rom ASEGS).

Theorem drv_piece : forall LB LK cr A M (model : Model) (fx fx' : PropExec.FPState) R (pc : word) R' (pc' : word) (MV' : word -> option byte) (W : Z -> Prop) K,
  dinvA LB LK cr A M model ->
  msteps ASEGS (@mkst fx R pc (mrestrict (ahid A model) M) rom) (@mkst fx' R' pc' MV' rom) ->
  (forall a : word, mrestrict (ahid A model) M a <> None -> MV' a <> None) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MV' (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, W a -> CWA sp0 LB a) ->
  (forall M1 (model1 : Model),
      dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
      mrestrict (ahid A model1) M1 = MV' ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M1 rom) model1) K) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
  intros LB LK cr A M model fx fx' R pc R' pc' MV' W K DI MS GR FZ WC KONT.
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HH & HL & HA & HM & Hh).
  set (H := ahid A model) in *.
  apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M rom) (@mkst fx' R' pc' MV' rom) model K HL HA HM Hh MS).
  intros model1 MI1 SBM HC.
  change (unrestrict H (ms_mem (@mkst fx R pc M rom)) (@mkst fx' R' pc' MV' rom)) with (@mkst fx' R' pc' (munrestrict H M MV') rom).
  set (M1 := munrestrict H M MV').
  assert (VIS : mrestrict H M1 = MV') by (apply As0DrvKitA.mrestrict_munrestrict; intros a Ha; exact (HC a Ha)).
  assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E; [reflexivity|]. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (AH : ahid A model1 = H) by (unfold H; apply (ahid_sbm A model model1 SBM)).
  apply (KONT M1 model1).
  - apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M1 model model1 DI).
    + intros a Ha Hn. apply FR1; [exact Ha|]. intros Hw. exact (Hn (WC a Hw)).
    + intros a Ha. unfold M1, munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
    + exact (sbm_vml _ _ SBM).
    + exact MI1.
    + rewrite (sbm_halted_eq _ _ SBM). exact Hh.
    + exact (sbm_rdrA _ _ SBM).
  - exact SBM.
  - rewrite AH. exact VIS.
  - exact FR1.
Qed.
End Piece.
End Na0DrvPiece.
