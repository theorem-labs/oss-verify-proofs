(* diginet_frame_build_seg_h2b: the piece 0x82914 .. 0x82a78 of diginet_frame_build (fuzz_frame.asan-ubsan, image B),
   as a footprint run (lib/Lib/ExecF.v evtF) stepped by lib/Lib/StepF.v. The piece reads ack (4 bytes at hp + 8),
   retry (2 bytes at hp + 12), cmd (hp + 14) and num_commands (hp + 15) and stores them big endian at out + 22 ..
   out + 29; each load and each store comes after its shadow check.

   The run is cut at each address where the slow path of a check joins its fast path again: fbh2b_v1 .. fbh2b_v13
   below, one piece per check (and the last store). fbh2b_run chains them; fb_h2b_F states the result as the
   interface statement fb_h2b_stmt.

   Every store takes its address from a0 or a1 (offset 0), so the 30 + nt bytes at out are carried as nine cell
   lists: out .. out + 21, then one cell each at out + 22 .. out + 28, and the cell at out + 29 followed by the tail.
   The 12 header bytes at hp + 4 and the addressability of both ranges are carried in fbh2b_inv; the four loads and
   every shadow byte are read from it.

   The six branches to the `unimp` word at 0x82af0 (`beq a0,a3` with a3 = -1 at 0x8294c and 0x829f0, `bltu a4,a0`
   with a4 = -3 / -4 at 0x82970 / 0x82994, `bltu a1,s4` / `bltu a2,s4` with -13 / -15 / -16 at 0x829b4, 0x82a10,
   0x82a48) compare out + 22 or s4 = out + 14 with a constant near 2 ^ 64; out + 30 <= 2 ^ 63 makes each comparison
   false, so no branch is taken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Word and byte facts *)

Lemma fbh2b_lts : forall (x : Z) (k : byte), 0 <= x < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma fbh2b_zx32 : forall z, 0 <= z < 2 ^ 32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma fbh2b_zx16 : forall z, 0 <= z < 2 ^ 16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma fbh2b_zxb : forall z, 0 <= z < 2 ^ 8 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8). apply Z.mod_small. lia.
Qed.

(** * Cell lists *)

Lemma fbh2b_recast : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] Wr] W' EB ES.
  split; [split; [exact W' | rewrite EB; exact B] | rewrite ES; exact Wr].
Qed.

Lemma fbh2b_app_inv : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (Ha & Hn & Hw)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma fbh2b_app : forall m A cs1 cs2, rw_cells rsegs m A cs1 ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split.
  - split.
    + apply cells_wf_app. split; assumption.
    + rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
      rewrite cells_bytes_length by exact W1. exact B2.
  - unfold wr_at. rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt | Hge].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(** * The state, the invariants and the memory at out *)

Definition fbh2b_st (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (out hp pc : Z) (a0 a1 a2 a3 a4 : word) (m : word -> option byte)
    : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0 a1 a2 a3 a4 a5 a6 a7
          s2 (Z_to_bv 64 hp) (Z_to_bv 64 (out + 14)) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition fbh2b_ok (RNG : ExecF.footprint) (out hp ack retry cmd ncmds : Z) (l : list byte) (nt : nat) : Prop :=
  0 < out /\ out + Z.of_nat (length l) <= 2 ^ 63 /\ length l = (30 + nt)%nat /\
  0 < hp /\ hp + 16 <= 2 ^ 63 /\
  0 <= ack < 2 ^ 32 /\ 0 <= retry < 2 ^ 16 /\ 0 <= cmd < 2 ^ 8 /\ 0 <= ncmds < 2 ^ 8 /\
  (out + Z.of_nat (length l) <= hp + 4 \/ hp + 16 <= out) /\
  ExecF.rng RNG (out + 12) 18 /\ ExecF.rng RNG (hp + 4) 12 /\
  ExecF.rng RNG (shadow_addr (out + 12)) (shadow_addr (out + 29) - shadow_addr (out + 12) + 1) /\
  ExecF.rng RNG (shadow_addr (hp + 4)) (shadow_addr (hp + 15) - shadow_addr (hp + 4) + 1).

Definition fbh2b_inv (out hp send ack retry cmd ncmds : Z) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (hp + 4) (fb_hdr_in send ack retry cmd ncmds) /\
  addressable m (out + 12) 18 /\ addressable m (hp + 4) 12.

Definition fbh2b_mem (out : Z) (l : list byte) (nt : nat) (m : word -> option byte)
    (b22 b23 b24 b25 b26 b27 b28 b29 : byte) : Prop :=
  rw_cells rsegs m out [CB 22 (firstn 22 l)] /\
  rw_cells rsegs m (out + 22) [C1 b22] /\ rw_cells rsegs m (out + 23) [C1 b23] /\
  rw_cells rsegs m (out + 24) [C1 b24] /\ rw_cells rsegs m (out + 25) [C1 b25] /\
  rw_cells rsegs m (out + 26) [C1 b26] /\ rw_cells rsegs m (out + 27) [C1 b27] /\
  rw_cells rsegs m (out + 28) [C1 b28] /\ rw_cells rsegs m (out + 29) [C1 b29; CB nt (skipn 30 l)].

Definition fbh2b_fp (out : Z) (m m1 : word -> option byte) : Prop :=
  munch [(out + 22, out + 30)] m m1 /\ wmono rsegs m m1.

(* The nine cell lists of fbh2b_mem as one list at out. *)
Definition fbh2b_cs (l : list byte) (nt : nat) (b22 b23 b24 b25 b26 b27 b28 b29 : byte) : list cell :=
  [CB 22 (firstn 22 l)] ++ [C1 b22] ++ [C1 b23] ++ [C1 b24] ++ [C1 b25] ++ [C1 b26] ++ [C1 b27] ++ [C1 b28] ++
  [C1 b29; CB nt (skipn 30 l)].

Lemma fbh2b_mem_of : forall m out (l : list byte) nt b22 b23 b24 b25 b26 b27 b28 b29,
  rw_cells rsegs m out (fbh2b_cs l nt b22 b23 b24 b25 b26 b27 b28 b29) ->
  fbh2b_mem out l nt m b22 b23 b24 b25 b26 b27 b28 b29.
Proof.
  intros m out l nt b22 b23 b24 b25 b26 b27 b28 b29 CS. unfold fbh2b_cs in CS.
  apply fbh2b_app_inv in CS. destruct CS as [M0 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 22) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M22 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 23) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M23 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 24) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M24 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 25) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M25 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 26) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M26 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 27) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M27 CS].
  match type of CS with rw_cells _ _ ?A _ => replace A with (out + 28) in CS by (cbn; lia) end.
  apply fbh2b_app_inv in CS. destruct CS as [M28 M29].
  match type of M29 with rw_cells _ _ ?A _ => replace A with (out + 29) in M29 by (cbn; lia) end.
  exact (conj M0 (conj M22 (conj M23 (conj M24 (conj M25 (conj M26 (conj M27 (conj M28 M29)))))))).
Qed.

Lemma fbh2b_mem_to : forall m out (l : list byte) nt b22 b23 b24 b25 b26 b27 b28 b29,
  fbh2b_mem out l nt m b22 b23 b24 b25 b26 b27 b28 b29 ->
  rw_cells rsegs m out (fbh2b_cs l nt b22 b23 b24 b25 b26 b27 b28 b29).
Proof.
  intros m out l nt b22 b23 b24 b25 b26 b27 b28 b29 (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  unfold fbh2b_cs.
  apply fbh2b_app; [exact M0|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 22) by (cbn; lia) end.
  apply fbh2b_app; [exact M22|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 23) by (cbn; lia) end.
  apply fbh2b_app; [exact M23|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 24) by (cbn; lia) end.
  apply fbh2b_app; [exact M24|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 25) by (cbn; lia) end.
  apply fbh2b_app; [exact M25|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 26) by (cbn; lia) end.
  apply fbh2b_app; [exact M26|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 27) by (cbn; lia) end.
  apply fbh2b_app; [exact M27|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 28) by (cbn; lia) end.
  apply fbh2b_app; [exact M28|].
  match goal with |- rw_cells _ _ ?A _ => replace A with (out + 29) by (cbn; lia) end.
  exact M29.
Qed.

Lemma fbh2b_split : forall m out (l : list byte) nt, length l = (30 + nt)%nat ->
  rw_cells rsegs m out [CB (length l) l] ->
  exists b22 b23 b24 b25 b26 b27 b28 b29, fbh2b_mem out l nt m b22 b23 b24 b25 b26 b27 b28 b29.
Proof.
  intros m out l nt HNT CL.
  assert (L8 : length (firstn 8 (skipn 22 l)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (E : l = firstn 22 l ++ firstn 8 (skipn 22 l) ++ skipn 30 l).
  { rewrite <- (firstn_skipn 22 l) at 1. f_equal.
    rewrite <- (firstn_skipn 8 (skipn 22 l)) at 1. f_equal. rewrite skipn_skipn. reflexivity. }
  set (w := firstn 8 (skipn 22 l)) in *. clearbody w.
  destruct w as [|b22 [|b23 [|b24 [|b25 [|b26 [|b27 [|b28 [|b29 [|b w]]]]]]]]]; cbn in L8; try lia.
  exists b22, b23, b24, b25, b26, b27, b28, b29.
  apply fbh2b_mem_of.
  apply (fbh2b_recast m out [CB (length l) l]); [exact CL | | |].
  - unfold fbh2b_cs. cbn. rewrite length_firstn, length_skipn. repeat split; lia.
  - unfold fbh2b_cs. cbn [cells_bytes cbytes app]. rewrite !app_nil_r. symmetry. exact E.
  - unfold fbh2b_cs. cbn. lia.
Qed.

Lemma fbh2b_join : forall m out (l : list byte) nt b22 b23 b24 b25 b26 b27 b28 b29,
  length l = (30 + nt)%nat -> fbh2b_mem out l nt m b22 b23 b24 b25 b26 b27 b28 b29 ->
  rw_cells rsegs m out [CB (length l) (fb_put l 22 [b22; b23; b24; b25; b26; b27; b28; b29])].
Proof.
  intros m out l nt b22 b23 b24 b25 b26 b27 b28 b29 HNT MEM.
  pose proof (fbh2b_mem_to m out l nt b22 b23 b24 b25 b26 b27 b28 b29 MEM) as CS.
  apply (fbh2b_recast m out _ _ CS).
  - cbn [cells_wf cell_wf]. split; [|exact I]. apply fb_put_length. cbn [length]. lia.
  - unfold fb_put, fbh2b_cs. cbn [cells_bytes cbytes app length Nat.add]. rewrite !app_nil_r. reflexivity.
  - unfold fbh2b_cs. cbn. lia.
Qed.

(** * Tactics *)

Ltac fbh2b_unpack OK :=
  pose proof OK as (HO & HOL & HNT & HH & HHL & HAk & HRt & HCm & HNc & HD & RO & RH & RSO & RSH).

(* After `srli rd, rs, 3` with rs = Z_to_bv 64 e: name the shifted word. *)
Ltac fbh2b_shr g G :=
  match goal with
  | |- context [Some (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 ?e)) 3))] =>
      let Ew := fresh "Ew" in
      assert (G : bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 e)) 3)) = e / 8)
        by (rewrite (unsigned_lit e) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
            apply unsigned_lit; Z.div_mod_to_equations; lia);
      remember (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 e)) 3)) as g eqn:Ew; clear Ew
  end.

(* The shadow word h = (e >> 3) + ASAN_K is named; MK reads its byte. Gives the load fact R and the footprint RS. *)
Ltac fbh2b_sh h G H MK RS0 R RS :=
  let EH := fresh "EH" in
  lazymatch type of MK with
  | mrd _ _ (wa (shadow_addr ?X)) = Some _ =>
      assert (EH : bv_unsigned h = shadow_addr X) by (rewrite H, G; reflexivity);
      pose proof (rdw0 _ h _ _ MK EH) as R;
      pose proof RS0 as RS; rewrite <- EH in RS
  end.

(* The `blt` that closes a slow path: its condition holds, so it goes back to the join. *)
Ltac fbh2b_blt :=
  rewrite ?land7;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
             rewrite (unsigned_lit e) by (first [lia | Z.div_mod_to_equations; lia])
         end;
  lazymatch goal with
  | |- context [bv_lts (Z_to_bv 64 ?x) (sxb ?k)] =>
      rewrite (fbh2b_lts x k) by (first [lia | Z.div_mod_to_equations; lia]);
      replace (x <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; first [lia | Z.div_mod_to_equations; lia])
  end;
  cbn [negb].

(* The `bnez` on the shadow byte k: 0 goes on; otherwise the slow path runs and its `blt` goes back. *)
Ltac fbh2b_bnez SK k slow fin :=
  let C := fresh "C" in let Cp := fresh "Cp" in
  destruct SK as [C | [Cp C]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; fin
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; slow; fbh2b_blt; fin ].

(* A branch to the `unimp` word: `beq x, -1` or `bltu c, x` with x = out + K below 2 ^ 63 and c a constant near
   2 ^ 64 is not taken. *)
Ltac fbh2b_ncond :=
  unfold bv_eqb, bv_ltu; fold_lit_ux;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
         end;
  first [ apply Z.eqb_neq; lia | apply Z.ltb_ge; lia ].

Ltac fbh2b_guard :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; fbh2b_ncond]
  end.

(* The byte Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) is Z_to_bv 8 z. *)
Lemma fbh2b_c1_lit : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
  rewrite (Z.mod_eq z (2 ^ 64)) by lia.
  replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + - (2 ^ 56 * (z / 2 ^ 64)) * 2 ^ 8) by lia.
  apply Z_mod_plus_full.
Qed.

(* A one-byte store of a word Z_to_bv 64 z: transport's StepF updates the cell in the step, as the byte
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)); the cell lists are rewritten to the byte Z_to_bv 8 z. *)
Ltac fbh2b_st1 :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => rewrite ?le1_lit_byte; mem_after_store
  | _ => idtac
  end;
  repeat match goal with
  | H : rw_cells _ _ _ ?cs |- _ =>
      match cs with context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] => rewrite (fbh2b_c1_lit z) in H end
  end.

(* The end of a piece with a store: n witnesses, the state, the footprint, the nine cell lists. *)
Tactic Notation "fbh2b_fin_st" int_or_var(n) :=
  apply evtF_done; do n eexists; split; [reflexivity|];
  split; [split; assumption|];
  lazymatch goal with
  | M22 : rw_cells _ _ (_ + 22) _, M23 : rw_cells _ _ (_ + 23) _, M24 : rw_cells _ _ (_ + 24) _,
    M26 : rw_cells _ _ (_ + 26) _ |- _ =>
      rewrite ?Z.shiftr_div_pow2 in M22 by lia; rewrite ?Z.shiftr_div_pow2 in M23 by lia;
      rewrite ?Z.shiftr_div_pow2 in M24 by lia; rewrite ?Z.shiftr_div_pow2 in M26 by lia
  end;
  unfold fbh2b_mem; repeat (split; [assumption|]); assumption.

Tactic Notation "fbh2b_fin" int_or_var(n) := apply evtF_done; do n eexists; reflexivity.

(** * The pieces *)

Section H2B.
Variables (RNG : ExecF.footprint)
  (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (out hp send ack retry cmd ncmds : Z) (l : list byte) (nt : nat).

Local Abbreviation STh :=
  (fbh2b_st ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc out hp).
Local Abbreviation OKh := (fbh2b_ok RNG out hp ack retry cmd ncmds l nt).
Local Abbreviation INVh := (fbh2b_inv out hp send ack retry cmd ncmds).
Local Abbreviation MEMh := (fbh2b_mem out l nt).
Local Abbreviation FPh := (fbh2b_fp out).

Lemma fbh2b_fp_trans : forall m1 m2 m3, FPh m1 m2 -> FPh m2 m3 -> FPh m1 m3.
Proof.
  intros m1 m2 m3 (U1 & W1) (U2 & W2).
  split; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption].
Qed.

Lemma fbh2b_inv_tp : forall m m1, OKh -> INVh m -> munch [(out + 22, out + 30)] m m1 -> INVh m1.
Proof.
  intros m m1 OK (BA & AO & AH) MU.
  pose proof OK as (HO & HOL & HNT & HH & HHL & _ & _ & _ & _ & HD & _).
  assert (APP : forall a, out + 22 <= a < out + 30 -> app_mem a).
  { intros a Ha. destruct AO as (_ & _ & _ & AB).
    destruct (AB (a - (out + 12)) ltac:(lia)) as (Happ & _).
    replace (out + 12 + (a - (out + 12))) with a in Happ by lia. exact Happ. }
  split; [|split].
  - eapply bytes_tp; [exact MU| |exact BA]. rewrite fb_hdr_in_length. lia.
  - exact (fb_addressable_tp m m1 _ _ _ _ MU APP AO).
  - exact (fb_addressable_tp m m1 _ _ _ _ MU APP AH).
Qed.

Lemma fbh2b_ck_out : forall m m1 k, OKh -> INVh m -> munch [(out + 22, out + 30)] m m1 -> 12 <= k <= 29 ->
  exists b : byte, mrd rsegs m1 (wa (shadow_addr (out + k))) = Some b /\
    (bv_signed b = 0 \/ (0 < bv_signed b /\ (out + k) mod 8 < bv_signed b)).
Proof.
  intros m m1 k OK INV MU Hk. pose proof OK as (HO & HOL & HNT & _).
  destruct (fbh2b_inv_tp m m1 OK INV MU) as (_ & AO & _).
  destruct (fb_ck_of_addressable m1 (out + 12) 18 (out + k) 1 AO ltac:(lia) ltac:(lia) ltac:(lia))
    as (b & Hb & Hs).
  exists b. split; [exact Hb|]. pose proof (Z.mod_pos_bound (out + k) 8 ltac:(lia)). lia.
Qed.

Lemma fbh2b_ck_hp : forall m m1 k w, OKh -> INVh m -> munch [(out + 22, out + 30)] m m1 ->
  4 <= k -> k + w <= 16 -> 1 <= w <= 8 ->
  exists b : byte, mrd rsegs m1 (wa (shadow_addr (hp + k))) = Some b /\
    (bv_signed b = 0 \/ (0 < bv_signed b /\ (hp + k) mod 8 + w - 1 < bv_signed b)).
Proof.
  intros m m1 k w OK INV MU Hk Hkw Hw. pose proof OK as (_ & _ & _ & HH & _).
  destruct (fbh2b_inv_tp m m1 OK INV MU) as (_ & _ & AH).
  destruct (fb_ck_of_addressable m1 (hp + 4) 12 (hp + k) w AH ltac:(lia) ltac:(lia) Hw) as (b & Hb & Hs).
  exists b. split; [exact Hb|]. pose proof (Z.mod_pos_bound (hp + k) 8 ltac:(lia)). lia.
Qed.

Lemma fbh2b_rng_so : forall k, OKh -> 12 <= k <= 29 -> ExecF.rng RNG (shadow_addr (out + k)) 1.
Proof.
  intros k OK Hk. pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RSO & _).
  eapply rng_sub'; [exact RSO|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma fbh2b_rng_sh : forall k, OKh -> 4 <= k <= 15 -> ExecF.rng RNG (shadow_addr (hp + k)) 1.
Proof.
  intros k OK Hk. pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RSH).
  eapply rng_sub'; [exact RSH|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma fbh2b_rd_ack : forall m, INVh m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (hp + 8)) 4 = Some (le4 (Z_to_bv 64 ack)).
Proof.
  intros m (BA & _ & _).
  replace (Z_to_bv 64 (hp + 8)) with (wa (hp + 4 + 4)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (hp + 4) _ 4 4 BA) by (first [lia | rewrite fb_hdr_in_length; cbn; lia]).
  reflexivity.
Qed.

Lemma fbh2b_rd_retry : forall m, INVh m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (hp + 12)) 2 = Some (le2 (Z_to_bv 64 retry)).
Proof.
  intros m (BA & _ & _).
  replace (Z_to_bv 64 (hp + 12)) with (wa (hp + 4 + 8)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (hp + 4) _ 8 2 BA) by (first [lia | rewrite fb_hdr_in_length; cbn; lia]).
  reflexivity.
Qed.

Lemma fbh2b_rd_cmd : forall m, INVh m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (hp + 14)) 1 = Some [b8 cmd].
Proof.
  intros m (BA & _ & _).
  replace (Z_to_bv 64 (hp + 14)) with (wa (hp + 4 + 10)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (hp + 4) _ 10 1 BA) by (first [lia | rewrite fb_hdr_in_length; cbn; lia]).
  reflexivity.
Qed.

Lemma fbh2b_rd_ncmds : forall m, INVh m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (hp + 15)) 1 = Some [b8 ncmds].
Proof.
  intros m (BA & _ & _).
  replace (Z_to_bv 64 (hp + 15)) with (wa (hp + 4 + 11)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (hp + 4) _ 11 1 BA) by (first [lia | rewrite fb_hdr_in_length; cbn; lia]).
  reflexivity.
Qed.

(* 0x82914 addi a1,s3,8; srli a0,a1,3; add a0,a0,s10; lb a0,0(a0); bnez a0 -> 0x82b94:
   andi a2,a1,7; addi a2,a2,3; blt a2,a0 -> 0x82928 (the 4-byte check of hp + 8). *)
Lemma fbh2b_v1 : forall a0 a1 a2 a3 a4 m, OKh -> INVh m ->
  evtF rsegs RNG (fun ms' => exists a0' a2', ms' = STh 0x8bad0 a0' (Z_to_bv 64 (hp + 8)) a2' a3 a4 m)
    (STh 0x8babc a0 a1 a2 a3 a4 m).
Proof.
  intros a0 a1 a2 a3 a4 m OK INV. fbh2b_unpack OK.
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU.
  destruct (fbh2b_ck_hp m m 8 4 OK INV MU ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK).
  pose proof (fbh2b_rng_sh 8 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 3 step) ltac:(fbh2b_fin 2).
Qed.

(* 0x82928 addi a0,s0,22; srli a2,a0,3; add a2,a2,s10; lb a3,0(a2); lwu a2,0(a1); bnez a3 -> 0x82ba8:
   andi a1,a0,7; blt a1,a3 -> 0x82940 (the check of out + 22; the load of ack). *)
Lemma fbh2b_v2 : forall a0 a2 a3 a4 m, OKh -> INVh m ->
  evtF rsegs RNG (fun ms' => exists a1' a3',
      ms' = STh 0x8bae8 (Z_to_bv 64 (out + 22)) a1' (Z_to_bv 64 ack) a3' a4 m)
    (STh 0x8bad0 a0 (Z_to_bv 64 (hp + 8)) a2 a3 a4 m).
Proof.
  intros a0 a2 a3 a4 m OK INV. fbh2b_unpack OK.
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU.
  destruct (fbh2b_ck_out m m 22 OK INV MU ltac:(lia)) as (k & MK & SK).
  pose proof (fbh2b_rng_so 22 OK ltac:(lia)) as RS0.
  pose proof (fbh2b_rd_ack m INV) as RA.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step. clear RA. rewrite (fbh2b_zx32 ack) by lia. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin 2).
Qed.

(* 0x82940 srli a1,a2,24; li a3,-1; sb a1,0(a0) (out + 22); beq a0,a3 (not taken); addi a1,s0,23; srli a3,a1,3;
   add a3,a3,s10; lb a3,0(a3); bnez a3 -> 0x82bb4: andi a4,a1,7; blt a4,a3 -> 0x82964. *)
Lemma fbh2b_v3 : forall a1 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a3' a4' m1,
      ms' = STh 0x8bb0c (Z_to_bv 64 (out + 22)) (Z_to_bv 64 (out + 23)) (Z_to_bv 64 ack) a3' a4' m1 /\
      FPh m m1 /\ MEMh m1 (b8 (ack / 2 ^ 24)) b23 b24 b25 b26 b27 b28 b29)
    (STh 0x8bae8 (Z_to_bv 64 (out + 22)) a1 (Z_to_bv 64 ack) a3 a4 m).
Proof.
  intros a1 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_so 23 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. rewrite (unsigned_lit ack) by lia. step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_out m _ 23 OK INV MU ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x82964 srli a3,a2,16; li a4,-3; sb a3,0(a1) (out + 23); bltu a4,a0 (not taken); addi a1,s0,24; srli a3,a1,3;
   add a3,a3,s10; lb a3,0(a3); bnez a3 -> 0x82bc4: andi a4,a1,7; blt a4,a3 -> 0x82988. *)
Lemma fbh2b_v4 : forall a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a3' a4' m1,
      ms' = STh 0x8bb30 (Z_to_bv 64 (out + 22)) (Z_to_bv 64 (out + 24)) (Z_to_bv 64 ack) a3' a4' m1 /\
      FPh m m1 /\ MEMh m1 b22 (b8 (ack / 2 ^ 16)) b24 b25 b26 b27 b28 b29)
    (STh 0x8bb0c (Z_to_bv 64 (out + 22)) (Z_to_bv 64 (out + 23)) (Z_to_bv 64 ack) a3 a4 m).
Proof.
  intros a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_so 24 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. rewrite (unsigned_lit ack) by lia. step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_out m _ 24 OK INV MU ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x82988 srli a3,a2,8; li a4,-4; sb a3,0(a1) (out + 24); bltu a4,a0 (not taken); addi a0,s0,25; srli a1,a0,3;
   add a1,a1,s10; lb a1,0(a1); bnez a1 -> 0x82bd4: andi a3,a0,7; blt a3,a1 -> 0x829ac. *)
Lemma fbh2b_v5 : forall a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a1' a3' a4' m1,
      ms' = STh 0x8bb54 (Z_to_bv 64 (out + 25)) a1' (Z_to_bv 64 ack) a3' a4' m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 (b8 (ack / 2 ^ 8)) b25 b26 b27 b28 b29)
    (STh 0x8bb30 (Z_to_bv 64 (out + 22)) (Z_to_bv 64 (out + 24)) (Z_to_bv 64 ack) a3 a4 m).
Proof.
  intros a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_so 25 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. rewrite (unsigned_lit ack) by lia. step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_out m _ 25 OK INV MU ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 4).
Qed.

(* 0x829ac li a1,-13; sb a2,0(a0) (out + 25); bltu a1,s4 (not taken); addi a1,s3,12; srli a0,a1,3;
   add a0,a0,s10; lb a0,0(a0); bnez a0 -> 0x82be0: andi a2,a1,7; addi a2,a2,1; blt a2,a0 -> 0x829cc
   (the 2-byte check of hp + 12). *)
Lemma fbh2b_v6 : forall a1 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a0' a2' m1,
      ms' = STh 0x8bb74 a0' (Z_to_bv 64 (hp + 12)) a2' a3 a4 m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 b24 (b8 ack) b26 b27 b28 b29)
    (STh 0x8bb54 (Z_to_bv 64 (out + 25)) a1 (Z_to_bv 64 ack) a3 a4 m).
Proof.
  intros a1 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_sh 12 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_hp m _ 12 2 OK INV MU ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 3 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x829cc addi a0,s0,26; srli a2,a0,3; add a2,a2,s10; lb a2,0(a2); lhu a1,0(a1); bnez a2 -> 0x82bf4:
   andi a3,a0,7; blt a3,a2 -> 0x829e4 (the check of out + 26; the load of retry). *)
Lemma fbh2b_v7 : forall a0 a2 a3 a4 m, OKh -> INVh m ->
  evtF rsegs RNG (fun ms' => exists a2' a3',
      ms' = STh 0x8bb8c (Z_to_bv 64 (out + 26)) (Z_to_bv 64 retry) a2' a3' a4 m)
    (STh 0x8bb74 a0 (Z_to_bv 64 (hp + 12)) a2 a3 a4 m).
Proof.
  intros a0 a2 a3 a4 m OK INV. fbh2b_unpack OK.
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU.
  destruct (fbh2b_ck_out m m 26 OK INV MU ltac:(lia)) as (k & MK & SK).
  pose proof (fbh2b_rng_so 26 OK ltac:(lia)) as RS0.
  pose proof (fbh2b_rd_retry m INV) as RA.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step. clear RA. rewrite (fbh2b_zx16 retry) by lia. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin 2).
Qed.

(* 0x829e4 srli a2,a1,8; li a3,-1; sb a2,0(a0) (out + 26); beq a0,a3 (not taken); addi a0,s0,27; srli a2,a0,3;
   add a2,a2,s10; lb a2,0(a2); bnez a2 -> 0x82c00: andi a3,a0,7; blt a3,a2 -> 0x82a08. *)
Lemma fbh2b_v8 : forall a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a2' a3' m1,
      ms' = STh 0x8bbb0 (Z_to_bv 64 (out + 27)) (Z_to_bv 64 retry) a2' a3' a4 m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 b24 b25 (b8 (retry / 2 ^ 8)) b27 b28 b29)
    (STh 0x8bb8c (Z_to_bv 64 (out + 26)) (Z_to_bv 64 retry) a2 a3 a4 m).
Proof.
  intros a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_so 27 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. rewrite (unsigned_lit retry) by lia. step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_out m _ 27 OK INV MU ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x82a08 li a2,-15; sb a1,0(a0) (out + 27); bltu a2,s4 (not taken); addi a0,s3,14; srli a1,a0,3;
   add a1,a1,s10; lb a1,0(a1); bnez a1 -> 0x82c0c: andi a2,a0,7; blt a2,a1 -> 0x82a28 (the 1-byte check of
   hp + 14). *)
Lemma fbh2b_v9 : forall a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a1' a2' m1,
      ms' = STh 0x8bbd0 (Z_to_bv 64 (hp + 14)) a1' a2' a3 a4 m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 b24 b25 b26 (b8 retry) b28 b29)
    (STh 0x8bbb0 (Z_to_bv 64 (out + 27)) (Z_to_bv 64 retry) a2 a3 a4 m).
Proof.
  intros a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_sh 14 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_hp m _ 14 1 OK INV MU ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x82a28 addi a1,s0,28; srli a2,a1,3; add a2,a2,s10; lb a2,0(a2); lbu a0,0(a0); bnez a2 -> 0x82c18:
   andi a3,a1,7; blt a3,a2 -> 0x82a40 (the check of out + 28; the load of cmd). *)
Lemma fbh2b_v10 : forall a1 a2 a3 a4 m, OKh -> INVh m ->
  evtF rsegs RNG (fun ms' => exists a2' a3',
      ms' = STh 0x8bbe8 (Z_to_bv 64 cmd) (Z_to_bv 64 (out + 28)) a2' a3' a4 m)
    (STh 0x8bbd0 (Z_to_bv 64 (hp + 14)) a1 a2 a3 a4 m).
Proof.
  intros a1 a2 a3 a4 m OK INV. fbh2b_unpack OK.
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU.
  destruct (fbh2b_ck_out m m 28 OK INV MU ltac:(lia)) as (k & MK & SK).
  pose proof (fbh2b_rng_so 28 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R.
  pose proof (fbh2b_rd_cmd m INV) as RA. step. clear RA. rewrite (fbh2b_zxb cmd) by lia. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin 2).
Qed.

(* 0x82a40 li a2,-16; sb a0,0(a1) (out + 28); bltu a2,s4 (not taken); addi a0,s3,15; srli a1,a0,3;
   add a1,a1,s10; lb a1,0(a1); bnez a1 -> 0x82c28: andi a2,a0,7; blt a2,a1 -> 0x82a60 (the 1-byte check of
   hp + 15). *)
Lemma fbh2b_v11 : forall a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a1' a2' m1,
      ms' = STh 0x8bc08 (Z_to_bv 64 (hp + 15)) a1' a2' a3 a4 m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 b24 b25 b26 b27 (b8 cmd) b29)
    (STh 0x8bbe8 (Z_to_bv 64 cmd) (Z_to_bv 64 (out + 28)) a2 a3 a4 m).
Proof.
  intros a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK INV MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (fbh2b_rng_sh 15 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_st1.
  step. fbh2b_guard.
  destruct (fbh2b_ck_hp m _ 15 1 OK INV MU ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK).
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin_st 3).
Qed.

(* 0x82a60 addi a1,s0,29; srli a2,a1,3; add a2,a2,s10; lb a2,0(a2); lbu a0,0(a0); bnez a2 -> 0x82c34:
   andi a3,a1,7; blt a3,a2 -> 0x82a78 (the check of out + 29; the load of num_commands). *)
Lemma fbh2b_v12 : forall a1 a2 a3 a4 m, OKh -> INVh m ->
  evtF rsegs RNG (fun ms' => exists a2' a3',
      ms' = STh 0x8bc20 (Z_to_bv 64 ncmds) (Z_to_bv 64 (out + 29)) a2' a3' a4 m)
    (STh 0x8bc08 (Z_to_bv 64 (hp + 15)) a1 a2 a3 a4 m).
Proof.
  intros a1 a2 a3 a4 m OK INV. fbh2b_unpack OK.
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU.
  destruct (fbh2b_ck_out m m 29 OK INV MU ltac:(lia)) as (k & MK & SK).
  pose proof (fbh2b_rng_so 29 OK ltac:(lia)) as RS0.
  unfold fbh2b_st, ASAN_K.
  step. step. fbh2b_shr g G. step. gen_addi g h H.
  fbh2b_sh h G H MK RS0 R RS.
  step. clear R.
  pose proof (fbh2b_rd_ncmds m INV) as RA. step. clear RA. rewrite (fbh2b_zxb ncmds) by lia. step.
  fbh2b_bnez SK k ltac:(do 2 step) ltac:(fbh2b_fin 2).
Qed.

(* 0x82a78 sb a0,0(a1) (out + 29) -> 0x82a7c. *)
Lemma fbh2b_v13 : forall a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29,
  OKh -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists m1,
      ms' = STh 0x8bc24 (Z_to_bv 64 ncmds) (Z_to_bv 64 (out + 29)) a2 a3 a4 m1 /\
      FPh m m1 /\ MEMh m1 b22 b23 b24 b25 b26 b27 b28 (b8 ncmds))
    (STh 0x8bc20 (Z_to_bv 64 ncmds) (Z_to_bv 64 (out + 29)) a2 a3 a4 m).
Proof.
  intros a2 a3 a4 m b22 b23 b24 b25 b26 b27 b28 b29 OK MEM. fbh2b_unpack OK.
  destruct MEM as (M0 & M22 & M23 & M24 & M25 & M26 & M27 & M28 & M29).
  pose proof (munch_refl [(out + 22, out + 30)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold fbh2b_st, ASAN_K.
  step. fbh2b_st1.
  fbh2b_fin_st 1.
Qed.

Lemma fbh2b_run : forall m b22 b23 b24 b25 b26 b27 b28 b29 a0 a1 a2 a3 a4,
  OKh -> INVh m -> MEMh m b22 b23 b24 b25 b26 b27 b28 b29 ->
  evtF rsegs RNG (fun ms' => exists a0' a1' a2' a3' a4' m1,
      ms' = STh 0x8bc24 a0' a1' a2' a3' a4' m1 /\ FPh m m1 /\
      MEMh m1 (b8 (ack / 2 ^ 24)) (b8 (ack / 2 ^ 16)) (b8 (ack / 2 ^ 8)) (b8 ack)
              (b8 (retry / 2 ^ 8)) (b8 retry) (b8 cmd) (b8 ncmds))
    (STh 0x8babc a0 a1 a2 a3 a4 m).
Proof.
  intros m b22 b23 b24 b25 b26 b27 b28 b29 a0 a1 a2 a3 a4 OK INV MEM.
  eapply evtF_cut; [eapply fbh2b_v1; eassumption|]. intros ? (x0 & x2 & ->).
  eapply evtF_cut; [eapply fbh2b_v2; eassumption|]. intros ? (y1 & y3 & ->).
  eapply evtF_cut; [eapply fbh2b_v3; eassumption|]. intros ? (c3 & c4 & m3 & -> & FP3 & MEM3).
  pose proof (fbh2b_inv_tp m m3 OK INV (proj1 FP3)) as INV3.
  eapply evtF_cut; [eapply fbh2b_v4; eassumption|]. intros ? (d3 & d4 & m4 & -> & FP4 & MEM4).
  pose proof (fbh2b_inv_tp m3 m4 OK INV3 (proj1 FP4)) as INV4.
  eapply evtF_cut; [eapply fbh2b_v5; eassumption|]. intros ? (e1 & e3 & e4 & m5 & -> & FP5 & MEM5).
  pose proof (fbh2b_inv_tp m4 m5 OK INV4 (proj1 FP5)) as INV5.
  eapply evtF_cut; [eapply fbh2b_v6; eassumption|]. intros ? (f0 & f2 & m6 & -> & FP6 & MEM6).
  pose proof (fbh2b_inv_tp m5 m6 OK INV5 (proj1 FP6)) as INV6.
  eapply evtF_cut; [eapply fbh2b_v7; eassumption|]. intros ? (g2 & g3 & ->).
  eapply evtF_cut; [eapply fbh2b_v8; eassumption|]. intros ? (h2 & h3 & m8 & -> & FP8 & MEM8).
  pose proof (fbh2b_inv_tp m6 m8 OK INV6 (proj1 FP8)) as INV8.
  eapply evtF_cut; [eapply fbh2b_v9; eassumption|]. intros ? (i1 & i2 & m9 & -> & FP9 & MEM9).
  pose proof (fbh2b_inv_tp m8 m9 OK INV8 (proj1 FP9)) as INV9.
  eapply evtF_cut; [eapply fbh2b_v10; eassumption|]. intros ? (j2 & j3 & ->).
  eapply evtF_cut; [eapply fbh2b_v11; eassumption|]. intros ? (k1 & k2 & m11 & -> & FP11 & MEM11).
  pose proof (fbh2b_inv_tp m9 m11 OK INV9 (proj1 FP11)) as INV11.
  eapply evtF_cut; [eapply fbh2b_v12; eassumption|]. intros ? (n2 & n3 & ->).
  eapply evtF_cut; [eapply fbh2b_v13; eassumption|]. intros ? (m13 & -> & FP13 & MEM13).
  apply evtF_done. do 6 eexists. split; [reflexivity|]. split; [|exact MEM13].
  exact (fbh2b_fp_trans _ _ _ FP3 (fbh2b_fp_trans _ _ _ FP4 (fbh2b_fp_trans _ _ _ FP5 (fbh2b_fp_trans _ _ _ FP6
    (fbh2b_fp_trans _ _ _ FP8 (fbh2b_fp_trans _ _ _ FP9 (fbh2b_fp_trans _ _ _ FP11 FP13))))))).
Qed.

End H2B.

(** * The interface statement *)

Lemma fb_h2b_F : fb_h2b_stmt.
Proof.
  unfold fb_h2b_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m
    out hp send ack retry cmd ncmds l HO HOL HL HH HHL HM4 HS HA HR HC HN HD CL BA AO AH RO RH RSO RSH.
  set (nt := (length l - 30)%nat).
  assert (HNT : length l = (30 + nt)%nat) by (unfold nt; lia).
  clearbody nt.
  assert (OK : fbh2b_ok RNG out hp ack retry cmd ncmds l nt)
    by exact (conj HO (conj HOL (conj HNT (conj HH (conj HHL (conj HA (conj HR (conj HC (conj HN
               (conj HD (conj RO (conj RH (conj RSO RSH))))))))))))).
  assert (INV : fbh2b_inv out hp send ack retry cmd ncmds m) by exact (conj BA (conj AO AH)).
  destruct (fbh2b_split m out l nt HNT CL) as (b22 & b23 & b24 & b25 & b26 & b27 & b28 & b29 & MEM).
  let v := eval vm_compute in FB_H2B in change FB_H2B with v.
  let v := eval vm_compute in FB_TAIL in change FB_TAIL with v.
  eapply evtF_mono; [eapply fbh2b_run; eassumption|].
  intros ms' (x0 & x1 & x2 & x3 & x4 & m1 & -> & (MU & WM) & MEM1).
  exists x0, x1, x2, x3, x4, m1. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  change (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds])
    with [b8 (ack / 2 ^ 24); b8 (ack / 2 ^ 16); b8 (ack / 2 ^ 8); b8 ack; b8 (retry / 2 ^ 8); b8 retry;
          b8 cmd; b8 ncmds].
  exact (fbh2b_join m1 out l nt _ _ _ _ _ _ _ _ HNT MEM1).
Qed.
