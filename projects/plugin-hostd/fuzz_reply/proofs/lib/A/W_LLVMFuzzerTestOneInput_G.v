(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the global set G_fr of fuzz_reply.asan's LLVMFuzzerTestOneInput, concretely, and
   every G_fr / errno fact that the W8 segment files (W_LLVMFuzzerTestOneInput_*.v, W_x*.v) take as a Section
   hypothesis, proved for it.  One witness that satisfies all of them at once is the check that those hypotheses do
   not contradict each other (at 45b95aa1834 SEG_EXIT's HG_SL and HG_err did); at integration these lemmas discharge
   the hypotheses.

   G_fr_c = the program's 20 objects [addr, addr + plain size) (maps/EvBound/GLOBALS.md: exactly the complement of
   AF0m's 20 redzone entries in Tfib_owned_static inside the two hulls) ++ errno's 4 bytes (send_line stores errno, and
   its G_SL names it, W_contract.v G_SL).

   Premises, each a start-up / instance fact discharged at the milestone:
     HEV  : as_errno B = 0x5d93cc      - AF0m's ts_errno (TFIB_ERRNO = TFIB_TP - 164; maps/EvBound/GLOBALS.md);
     HOWN : the bytes of G_fr_c are not in as_owned_static B - AF0m's ts_owned (as_owned_static B = Tfib_owned_static),
            by vm_compute at the milestone (AF0m is not in this tree).  Measured on cold/port-reply-startup
            56fc92fe6b0's AF0m.v: 0 of G_fr_c's 513 bytes lie in its 61 Tfib_owned_static ranges, and Tfib_zero_shadow
            has the range (0x5d88e0, 0x180) that makes `azs B (rg_s fr_RG) (4 * ASRC)` (HZS / AZS_s) true under ts_zsh
            (script and output: port-reply's w8/vac/own-zsh-check.txt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_G.v, with its module paths changed; 347 of its 535 lines of code are new or changed and 16 lines of the source are left out. *)
(* The global set G_fr of fuzz_reply.asan's LLVMFuzzerTestOneInput, concretely, and
   every G_fr / errno / image fact that the W8 segment files (W_LLVMFuzzerTestOneInput_*.v, W_x*.v) take as a Section
   hypothesis, proved for it.  At integration these lemmas discharge the hypotheses.

   THE METHOD (copy it for any walk whose segments share Section hypotheses over one object): (1) extract every
   Section Hypothesis of every segment file mechanically and tag the objects it constrains
   (the script hyps.py (sha256 88e1e8be1088; internal record) DIR, output hyps.txt (sha256 017859357386; internal record) beside it); (2) write ONE concrete witness
   for the shared objects and prove every
   hypothesis TEXT about them for it, in one file.  A single model that satisfies all of them rules out a
   contradiction among them, across files too, which reading pairs never can.  This found, at 45b95aa1834, HG_SL
   (send_line's G_SL, which names errno, inside G_fr) against HG_err / HGRT (errno outside G_fr) in
   W_LLVMFuzzerTestOneInput_exit.v, W_xends.v, W_xrf.v, and HGRT false at such a G_fr in _write.v and W_xreset.v:
   every one of those Sections was provable by `exfalso`.  Removed at cc0dc82f9f6 and f32b851cd82.
   What the witness does NOT check: the RINV / LS rule families (predicate Variables: RINV := False satisfies every
   rule, so the entry composition must exhibit RINV and LS at the entry state) and single-object instance facts.

   G_fr_c = the program's 20 objects [addr, addr + plain size) (GLOBALS.md (sha256 d3788bf0c2b6; internal record): exactly the complement of
   AF0m's 20 redzone entries in Tfib_owned_static inside the two hulls) ++ errno's 4 bytes (send_line stores errno, and
   its G_SL names it, W_contract.v G_SL).

   Premises, each a start-up / instance fact discharged at the milestone, and the MEASUREMENT this witness rests on
   (a change of either AF0m row invalidates it; re-run the script own-zsh-check.py (sha256 5876c8bf7a46; internal record)
   [REF] against the new AF0m - exit 0 means the witness still holds):
     HEV  : as_errno B = 0x5d93cc - AF0m's `ts_errno : as_errno B = TFIB_ERRNO` with `TFIB_ERRNO : Z := 0x5d93cc`
            (56fc92fe6b0, lib/A/AF0m.v:22 and :861; = TFIB_TP - 164, GLOBALS.md (sha256 d3788bf0c2b6; internal record) errno section);
     HOWN : the bytes of G_fr_c are not in as_owned_static B - AF0m's `ts_owned : as_owned_static B =
            Tfib_owned_static` (same ref, AF0m.v:870), by vm_compute at the milestone (AF0m is not in this tree).
            Measured on a working branch 56fc92fe6b0's AF0m.v: 0 of G_fr_c's 513 bytes lie in its 61
            Tfib_owned_static ranges; and Tfib_zero_shadow (AF0m.v:815, `ts_zsh` :875) has the range
            (0x5d88e0, 0x180) that makes `azs B (rg_s fr_RG) (4 * ASRC)` (HZS / AZS_s) true
            (the script own-zsh-check.py (sha256 5876c8bf7a46; internal record), output own-zsh-check.txt (sha256 0cb6efd3ef2a; internal record) beside it);
     HPIN : (c_ROM_OUT's premise) every owned read-only byte is rom_pinned - AF0m's Tfib_const_abs pins all 408
            owned read-only bytes of image A (same ref; rom_owned_check.py (sha256 13958cb8b3c1; internal record)). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
(* the generated start-up table (home: a working branch; carried by path), for the rom_pinned obligation *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ range checks, as booleans *)
Definition rng_inb (lo n : Z) (G : list (Z * Z)) : bool :=
  existsb (fun r => (fst r <=? lo) && (lo + n <=? fst r + snd r)) G.
Lemma rng_cover : forall lo n G, rng_inb lo n G = true -> forall a, lo <= a < lo + n -> inG G a.
Proof.
  intros lo n G H a Ha. unfold rng_inb in H. apply existsb_exists in H as (r & Hr & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold inG. apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.
Lemma rng_cover_zr : forall lo n G, rng_inb lo n G = true -> forall a, in_zr a (lo, n) -> inG G a.
Proof. intros lo n G H a Ha. unfold in_zr in Ha. cbn [fst snd] in Ha. exact (rng_cover lo n G H a Ha). Qed.
Lemma inG_sub : forall G G', Forall (fun r => forall a, in_zr a r -> inG G' a) G -> forall a, inG G a -> inG G' a.
Proof.
  intros G G' HF a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite Forall_forall in HF. exact (HF r Hr a Hz).
Qed.
(* every byte of every range of G satisfies f *)
Definition rng_all (f : Z -> bool) (r : Z * Z) : bool :=
  forallb (fun i => f (fst r + Z.of_nat i)) (seq 0 (Z.to_nat (snd r))).
Lemma rng_all_in : forall f G a, forallb (rng_all f) G = true -> inG G a -> f a = true.
Proof.
  intros f G a H Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in H. specialize (H r Hr). unfold rng_all in H. rewrite forallb_forall in H.
  unfold in_zr in Hz.
  assert (Hi : In (Z.to_nat (a - fst r)) (seq 0 (Z.to_nat (snd r)))) by (apply in_seq; lia).
  specialize (H _ Hi). cbv beta in H. rewrite Z2Nat.id in H by lia. replace (fst r + (a - fst r)) with a in H by lia.
  exact H.
Qed.

(* ------------------------------------------------------------------ the image's bytes *)
Section img.
Variable segs : list Segment.
(* a byte the loaded image holds writable is writable in every memory, hidden or not (mrestrict H m gives None on a
   hidden byte, and wview then reads the segment): the shape W8ArmRemove measured (W_LLVMFuzzerTestOneInput_remove.v
   probe_wr) and W6's writable_of_seg (W_relay_instance_gone.v:73), for any H *)
Lemma wr_of_seg : forall (H : word -> bool) (m : word -> option byte) a,
  wview segs (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a Hw. unfold writable_at, mrestrict, wview in *.
  destruct (H (Z_to_bv 64 a)); [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|]; [cbv iota; discriminate | exact Hw].
Qed.
Definition segwb (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Lemma segwb_ok : forall a, segwb a = true -> wview segs (fun _ => None) (Z_to_bv 64 a) <> None.
Proof. intros a H. unfold segwb in H. destruct (wview segs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate H]. Qed.
Definition segin (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma segin_ok : forall a, segin a = true -> in_img segs a.
Proof.
  intros a H. unfold segin in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs|]. lia.
Qed.
(* no read-only segment meets a range of G *)
Definition rom_apart (G : list (Z * Z)) : bool :=
  forallb (fun sg => seg_writable sg || forallb (fun r =>
    (fst r + snd r <=? Z.of_N (seg_base sg)) || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) G) segs.
Lemma rom_apart_ok : forall G a, rom_apart G = true -> in_rom segs a -> ~ inG G a.
Proof.
  intros G a H (sg & Hs & Hw & Hr) Ha. unfold rom_apart in H. rewrite forallb_forall in H.
  specialize (H sg Hs). rewrite Hw in H. cbn [orb] in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr' & Hz). specialize (H r Hr').
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.
End img.

(* ------------------------------------------------------------------ G_fr *)
(* fuzz_reply.asan's 20 program objects, [addr, addr + plain size), in the table order of GLOBALS.md (sha256 d3788bf0c2b6; internal record): g_s, g_nfd, g_out,
   g_nout, g_capout, g_send_max, g_send_eintr, g_send_dead, g_gone, g_lock, g_thread, g_thread_up, g_stop, g_listen,
   g_client, g_client_broken, g_wake, g_src, g_nsrc, g_capsrc (509 bytes). *)
Definition G_fr_obj : list (Z * Z) :=
  [ (0x5d88e0, 384); (0x5d8820, 4); (0x5d8b40, 8); (0x5d88c0, 8); (0x5d8b20, 8); (0x5d8840, 8);
    (0x5d88a0, 1); (0x5d8880, 1); (0x5d8860, 1); (0x5d8ac0, 40); (0x5d8740, 8); (0x5d8760, 1);
    (0x5d8780, 4); (0xa1fc0, 4); (0xa1fe0, 4); (0x5d87e0, 1); (0xa1fa0, 8); (0x5d87c0, 8);
    (0x5d87a0, 4); (0x5d8800, 4) ].
Definition TFIB_ERRNO_A : Z := 0x5d93cc.

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Definition G_fr_c : list (Z * Z) := G_fr_obj ++ [(as_errno B, 4)].
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.

Lemma obj_c : forall a, inG G_fr_obj a -> inG G_fr_c a.
Proof. intros a Ha. unfold G_fr_c. apply inG_app. left. exact Ha. Qed.
Lemma err_c : forall a, as_errno B <= a < as_errno B + 4 -> inG G_fr_c a.
Proof. intros a Ha. unfold G_fr_c. apply inG_app. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma G_fr_c_val : G_fr_c = G_fr_obj ++ [(TFIB_ERRNO_A, 4)].
Proof. unfold G_fr_c. rewrite HEV. reflexivity. Qed.

(* ---- the coverage hypotheses, verbatim with G_fr := G_fr_c ---- *)
(* HGs: _drain.v, _exit.v, _small.v, _write.v, W_xends.v, W_xreset.v, W_xrf.v *)
Lemma c_HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HGnout: _head.v; XRF_Gnout: W_xrf.v *)
Lemma c_HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_nout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HGlock: _drain.v; HGlk: _small.v *)
Lemma c_HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_lock fr_RG) 12 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_client: _pro.v; HGcl: _small.v *)
Lemma c_HG_client : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_client fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_cbroken: _pro.v *)
Lemma c_HG_cbroken : forall a, rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_client_broken fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_nfd: _pro.v (A_NFD := 0x5d8820, _pro.v:65) *)
Lemma c_HG_nfd : forall a, 0x5d8820 <= a < 0x5d8820 + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover 0x5d8820 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_smax: _pro.v; HGmx: _small.v *)
Lemma c_HG_smax : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_max fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_gone: _pro.v; HGgn: _small.v *)
Lemma c_HG_gone : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_gone fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_sdead: _pro.v; HGdd: _small.v *)
Lemma c_HG_sdead : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_dead fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_seintr: _pro.v; HGei: _small.v *)
Lemma c_HG_seintr : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_eintr fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_SL: _exit.v, W_xends.v, W_xrf.v - send_line's G, errno included *)
Lemma c_HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr_c a.
Proof.
  apply inG_sub. unfold G_SL.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client_broken fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_eintr fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_capout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_out fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [|constructor].
  intros a Ha. apply err_c. unfold in_zr in Ha. cbn [fst snd] in Ha. exact Ha.
Qed.
(* HG_DR: _drain.v - drain's G, g_s then send_line's *)
Lemma c_HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr_c a.
Proof.
  intros a Ha. unfold G_DR in Ha. apply inG_cons in Ha as [Ha|Ha]; [|exact (c_HG_SL a Ha)].
  exact (obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
Qed.
(* HG_RIG: W_LLVMFuzzerTestOneInput_gone_base.v's GN_HG_RIG - relay_instance_gone's G_RIG, the lock and
   drain's G (W_contract.v:1349) *)
Lemma c_HG_RIG : forall a, inG (G_RIG B fr_RG) a -> inG G_fr_c a.
Proof.
  intros a Ha. unfold G_RIG in Ha. apply inG_cons in Ha as [Ha|Ha]; [|exact (c_HG_DR a Ha)].
  apply c_HGlock. unfold in_zr in Ha. cbn [fst snd] in Ha. exact Ha.
Qed.
(* HGcells: W_LLVMFuzzerTestOneInput_gone_base.v's GN_HGcells - every cell amodel_at (_cut.v:289) names,
   so that a callee's journal keeps them (its image clause asks ~ allocator static, which the walk knows
   only through G_fr).  The list is gn_cells, spelled out here so this file does not import the piece. *)
Lemma c_HGcells : forall a,
  inG [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
       (rg_out fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_send_max fr_RG, 8);
       (rg_send_eintr fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_client fr_RG, 4);
       (rg_client_broken fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4);
       (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a ->
  inG G_fr_c a.
Proof.
  (* one range per step, each by its own closed vm_compute (no evar is ever computed on) *)
  apply inG_sub.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_src fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_capsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_out fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_capout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_max fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_eintr fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_dead fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_gone fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client_broken fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_lock fr_RG) 12 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_wake fr_RG + 4) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_NFD 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_THREAD_UP 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_LISTEN 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor.
Qed.
(* CELLS_ERRNO: W_LLVMFuzzerTestOneInput_gone_base.v's GN_CELLS_ERRNO - errno (0x5d93cc) is none of the cells
   amodel_at names.  The list is gn_cells, named here so the closed vm_compute below never sees an evar. *)
Definition cells_c : list (Z * Z) :=
  [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
   (rg_out fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_send_max fr_RG, 8);
   (rg_send_eintr fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_client fr_RG, 4);
   (rg_client_broken fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4);
   (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Lemma c_CELLS_ERRNO : forall a, inG cells_c a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV.
  pose proof (rng_all_in (fun x => negb ((TFIB_ERRNO_A <=? x) && (x <? TFIB_ERRNO_A + 4))) cells_c a
    ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. intros [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in H. discriminate.
Qed.
(* HG_RF: _exit.v, W_xends.v, W_xrf.v, at GL = g_listen (_cut.v AG_LISTEN) *)
Lemma c_HG_RF : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr_c a.
Proof.
  apply inG_sub.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_lock fr_RG) 12 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_LISTEN 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor.
Qed.
(* HG_cnl: _drain.v, at check_no_loss's G = [(g_s, 384)] (W3's status line: cnl_spec over G = [(g_s, 384)]) *)
Lemma c_HG_cnl : forall a, inG [(rg_s fr_RG, 4 * ASRC)] a -> inG G_fr_c a.
Proof.
  apply inG_sub.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor.
Qed.
(* XRF_Gcells / XRF_ERRNO: W_xrf.v (SEG_EXIT's relay_finish piece) - proofs in XRf.md (sha256 58b0bcdac815; internal record), pasted *)
Lemma c_XRF_Gcells : forall a,
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr_c a.
Proof.
  intros a [Ha | [Ha | [Ha | Ha]]].
  - exact (obj_c a (rng_cover (rg_gone fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
  - exact (obj_c a (rng_cover (rg_wake fr_RG + 4) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
  - exact (obj_c a (rng_cover AG_NFD 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
  - exact (obj_c a (rng_cover AG_THREAD_UP 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
Qed.
Lemma c_XRF_ERRNO : 0x5d8b48 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Proof. rewrite HEV. unfold TFIB_ERRNO_A. lia. Qed.
(* the program globals ARM_event's tail carries across its calls: a verbatim copy of et_GL,
   W_LLVMFuzzerTestOneInput_event.v:124 *)
Definition et_GL_c : list (Z * Z) :=
  [ (rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_gone fr_RG, 1);
    (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4);
    (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4);
    (rg_client_broken fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1) ].
(* HG_carry: _event.v - every et_GL byte is in G_fr (each range lies in one of G_fr_obj's 20 objects) *)
Lemma c_HG_carry : forall a, inG et_GL_c a -> inG G_fr_c a.
Proof.
  apply inG_sub. unfold et_GL_c.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_src fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_capsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_gone fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_lock fr_RG) 12 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_wake fr_RG + 4) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_NFD 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_THREAD_UP 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr AG_LISTEN 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_max fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_nout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_capout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_out fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_client_broken fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_dead fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_send_eintr fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor.
Qed.
(* HERR_AP: _event.v - every et_GL byte is apart from errno's four bytes *)
Lemma c_HERR_AP : forall a, inG et_GL_c a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV.
  assert (Hf : ((a <? TFIB_ERRNO_A) || (TFIB_ERRNO_A + 4 <=? a))%bool = true).
  { revert Ha. apply (rng_all_in (fun x => (x <? TFIB_ERRNO_A) || (TFIB_ERRNO_A + 4 <=? x))%bool).
    vm_compute. reflexivity. }
  apply orb_prop in Hf as [Hf|Hf]; [apply Z.ltb_lt in Hf | apply Z.leb_le in Hf]; lia.
Qed.

(* ---- the image facts ---- *)
(* GWL: _pro.v; GWR: _small.v, _write.v - every byte of G_fr_c is writable in every memory *)
Lemma c_glob_wr : glob_wr_law G_fr_c.
Proof.
  intros H m a Ha. apply wr_of_seg. apply segwb_ok. rewrite G_fr_c_val in Ha. revert Ha. apply rng_all_in.
  vm_compute. reflexivity.
Qed.
(* HG (_cut.v, every piece): gx_ok at G_fr_c, from its image half (vm_compute) and HOWN *)
Lemma c_img : forall a, inG G_fr_c a -> in_img segs a.
Proof.
  intros a Ha. apply segin_ok. rewrite G_fr_c_val in Ha. revert Ha. apply rng_all_in. vm_compute. reflexivity.
Qed.
(* QMm W0': gx_ok's third clause (no kept byte in G) is the premise HKEPT, as HOWN is its second (addI's zz_HKEPT) *)
Lemma c_gx_ok : (forall a, inG G_fr_c a -> ~ Exists (in_zr a) (as_owned_static B)) ->
  (forall a, inG G_fr_c a -> ~ Exists (in_zr a) (as_kept B)) -> gx_ok segs B G_fr_c.
Proof. intros HOWN HKEPT a Ha. exact (conj (c_img a Ha) (conj (HOWN a Ha) (HKEPT a Ha))). Qed.
(* XRF_ROM_OUT's G_fr conjunct (W_xrf.v): no read-only byte is in G_fr_c *)
Lemma c_rom_apart : forall a, in_rom segs a -> ~ inG G_fr_c a.
Proof. intros a. rewrite G_fr_c_val. apply rom_apart_ok. vm_compute. reflexivity. Qed.
(* ET_ROM_OUT: _event.v (the W_journal.v:396 rom_out text, as W_xrf.v's XRF_ROM_OUT): conjunct 1 is c_rom_apart;
   conjuncts 3 and 4 are image checks (no read-only segment meets errno's 4 bytes or the sink's overflow head
   [AOFL_HEAD, AOFL_HEAD + 8)); conjunct 2 is the premise HPIN, an instance fact: every owned read-only byte is
   pinned by one of AR's AV const cells - AF0m's Tfib_const_abs pins all 408 owned read-only bytes of image A
   (56fc92fe6b0; measured by rom_owned_check.py (sha256 13958cb8b3c1; internal record)), discharged at the
   milestone from AF0m's ts_owned / ts_const *)
Lemma c_ROM_OUT : (forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a) ->
  rom_out segs B G_fr_c.
Proof.
  intros HPIN. unfold rom_out. intros a Ha.
  split; [exact (c_rom_apart a Ha)|]. split; [exact (HPIN a Ha)|]. split.
  - rewrite HEV. intros He. apply (rom_apart_ok segs [(TFIB_ERRNO_A, 4)] a ltac:(vm_compute; reflexivity) Ha).
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact He.
  - (* refine, not apply (... ltac:(...)): AOFL_HEAD's sink_head instance is resolved before vm_compute runs *)
    intros Ho. refine (rom_apart_ok segs [(AOFL_HEAD, 8)] a _ Ha _); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Ho.
Qed.
(* relay_event's own G at _event.v's call site: a verbatim copy of et_GRE, W_LLVMFuzzerTestOneInput_event.v:101 *)
Definition et_GRE_c : list (Z * Z) := (rg_lock fr_RG, 12) :: G_SL B fr_RG.
(* RE's gx_ok side fact at _event.v's relay_event call: every et_GRE byte is in G_fr_c (the lock by c_HGlock, G_SL by
   c_HG_SL), then c_gx_ok's two halves; HOWN is the premise c_gx_ok takes (AF0m's ts_owned, see the header) *)
Lemma c_gx_ok_GRE : (forall a, inG G_fr_c a -> ~ Exists (in_zr a) (as_owned_static B)) ->
  (forall a, inG G_fr_c a -> ~ Exists (in_zr a) (as_kept B)) -> gx_ok segs B et_GRE_c.
Proof.
  intros HOWN HKEPT a Ha.
  assert (Hg : inG G_fr_c a).
  { unfold et_GRE_c in Ha. apply inG_cons in Ha as [Ha|Ha]; [|exact (c_HG_SL a Ha)].
    unfold in_zr in Ha. cbn [fst snd] in Ha. exact (c_HGlock a Ha). }
  exact (conj (c_img a Hg) (conj (HOWN a Hg) (HKEPT a Hg))).
Qed.
(* the lock's 12 bytes are apart from errno's 4 (_event.v's relay_event call site) *)
Lemma c_GRE_err_ap : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV.
  assert (Hf : ((rg_lock fr_RG + 12 <=? TFIB_ERRNO_A) || (TFIB_ERRNO_A + 4 <=? rg_lock fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in Hf as [Hf|Hf]; apply Z.leb_le in Hf; lia.
Qed.

(* ---- errno's place ---- *)
(* HERRNO: _head.v; XRF_ERRNO: W_xrf.v *)
Lemma c_HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
Proof. rewrite HEV. vm_compute. split; [discriminate|]. split; [discriminate|]. right. discriminate. Qed.
(* ERRNO_LOW: _latch.v (CEIL8 = alloc_ceiling + 8) *)
Lemma c_ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling + 8.
Proof. rewrite HEV. pose proof alloc_ceiling_value as (Hc & _). unfold TFIB_ERRNO_A. lia. Qed.
(* HERRHI: _small.v - errno's cell lies above g_out (0x5d8b40), the highest of the program's globals *)
Lemma c_HERRHI : rg_out fr_RG + 8 <= as_errno B.
Proof. rewrite HEV. vm_compute. discriminate. Qed.

(* ---- the image objects ARM_drain reads are apart from g_s: HAP (_drain.v:579) ---- *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Lemma c_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
              (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).
Proof.
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 32)) || (VAL (A_OBJ 32) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1. split.
  - destruct H0 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
  - destruct H1 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.
(* ---- ARM_remove (W_LLVMFuzzerTestOneInput_remove.v Section rmw): its G_fr / errno / image hypotheses ---- *)
(* HGnsrc *)
Lemma c_HGnsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* g_s is one of the 20 objects, and no byte of the 20 objects is errno's *)
Lemma c_gs_obj : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr_obj a.
Proof. exact (fun a Ha => rng_cover (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha). Qed.
Lemma c_obj_noerr : forall a, inG G_fr_obj a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha He. rewrite HEV in He.
  assert (Hf : forallb (rng_all (fun x => negb ((TFIB_ERRNO_A <=? x) && (x <? TFIB_ERRNO_A + 4)))) G_fr_obj = true)
    by (vm_compute; reflexivity).
  pose proof (rng_all_in _ G_fr_obj a Hf Ha) as Hx. apply negb_true_iff in Hx.
  rewrite (proj2 (Z.leb_le _ _) (proj1 He)), (proj2 (Z.ltb_lt _ _) (proj2 He)) in Hx. discriminate Hx.
Qed.
(* HGRT_s: gx_rt of g_s (errno apart: c_obj_noerr; the shadow GOT slot and cell apart: c_HAP) *)
Lemma c_HGRT_s : gx_rt B [(rg_s fr_RG, 4 * ASRC)].
Proof.
  intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha. cbn [fst snd] in Ha.
  split; [exact (c_obj_noerr a (c_gs_obj a Ha))|].
  pose proof c_HAP as (H0 & H32). clear - Ha H0 H32. split; lia.
Qed.
(* no read-only byte is errno's or the sink head's (both in the writable segment) *)
Lemma c_rom_noerr : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4) /\ ~ (AOFL_HEAD <= a < AOFL_HEAD + 8).
Proof.
  intros a Ha. rewrite HEV.
  assert (R1 : rom_apart segs [(TFIB_ERRNO_A, 4)] = true) by (vm_compute; reflexivity).
  assert (R2 : rom_apart segs [(AOFL_HEAD, 8)] = true) by (vm_compute; reflexivity).
  split.
  - intros He. apply (rom_apart_ok segs [(TFIB_ERRNO_A, 4)] a R1 Ha).
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact He.
  - intros Hh. apply (rom_apart_ok segs [(AOFL_HEAD, 8)] a R2 Ha).
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Hh.
Qed.
(* HRO: rom_out at G_fr_c.  Premise HPIN, an instance fact as HOWN is: every owned read-only byte is pinned
   (AF0m's Tfib_const_abs cells cover all 408 owned read-only bytes; a working branch 56fc92fe6b0, checked by
   the remove arm's pin script) *)
Lemma c_HRO : (forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a) ->
  rom_out segs B G_fr_c.
Proof.
  intros HPIN a Ha. destruct (c_rom_noerr a Ha) as [He Hh].
  exact (conj (c_rom_apart a Ha) (conj (HPIN a Ha) (conj He Hh))).
Qed.
(* HMG: rm_mglob's 13 cells (its text, spelled out) are image bytes of the 20 objects, so not errno's; not owned by
   the premise (AF0m's Tfib_owned_static: none of their 50 bytes, measured) *)
Definition c_mglob (a : Z) : Prop :=
  rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 \/ rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 \/
  rg_nout fr_RG <= a < rg_nout fr_RG + 8 \/ rg_capout fr_RG <= a < rg_capout fr_RG + 8 \/
  rg_out fr_RG <= a < rg_out fr_RG + 8 \/ rg_client fr_RG <= a < rg_client fr_RG + 4 \/
  rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 \/ rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 \/
  rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 \/ rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 \/ AG_LISTEN <= a < AG_LISTEN + 4.
Lemma c_mglob_obj : forall a, c_mglob a -> inG G_fr_obj a.
Proof.
  intros a Ha. unfold c_mglob in Ha.
  repeat match type of Ha with
  | _ \/ _ => destruct Ha as [Ha | Ha];
      [lazymatch type of Ha with ?lo <= _ < ?lo + ?n =>
         exact (rng_cover lo n G_fr_obj ltac:(vm_compute; reflexivity) a Ha) end |]
  end.
  lazymatch type of Ha with ?lo <= _ < ?lo + ?n => exact (rng_cover lo n G_fr_obj ltac:(vm_compute; reflexivity) a Ha) end.
Qed.
Lemma c_HMG : (forall a, c_mglob a -> ~ Exists (in_zr a) (as_owned_static B)) ->
  forall a, c_mglob a -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros HOWNm a Ha. pose proof (c_mglob_obj a Ha) as Ho.
  exact (conj (c_img a (obj_c a Ho)) (conj (HOWNm a Ha) (c_obj_noerr a Ho))).
Qed.
(* HGP: gx_prog of each slot g_s[si] (source_reset's own G).  Its errno, G and segment clauses are proved here; its
   three B-table clauses are premises (instance facts, as HOWN): g_s is no owned static, the owned read-only bytes are
   pinned, and the shadow hull of every range inside g_s is visible in every AR state (zero-shadow range (0x5d88e0,
   0x180) and Tfib_const_shadow cells pin every shadow byte of the hulls 0x800b3118-0x800b3150; the pin script) *)
Lemma c_HGP : (forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ Exists (in_zr a) (as_owned_static B)) ->
  (* QMm W0': gx_ok's kept clause over g_s (AF0m's Tfib_kept), as HOWNs is its owned clause *)
  (forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ Exists (in_zr a) (as_kept B)) ->
  (forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a) ->
  (forall ly S W mem md a n, AR segs B ly S W mem md -> 0 < n ->
     (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
     shadow_hull_vis (aview segs (w_H W) mem) a n) ->
  forall si, (si < 4)%nat -> gx_prog B [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)].
Proof.
  intros HOWNs HKEPTs HPIN HSHV si Hsi.
  assert (Hsub : forall a, inG [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
  { intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
    unfold in_zr in Ha. cbn [fst snd] in Ha. clear - Ha Hsi. unfold ASRC in *. lia. }
  assert (Hgs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG [(rg_s fr_RG, 4 * ASRC)] a)
    by (intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; exact Ha).
  split; [intros a Ha; pose proof (Hsub a Ha) as Hs; exact (conj (c_img a (obj_c a (c_gs_obj a Hs))) (conj (HOWNs a Hs) (HKEPTs a Hs)))|].
  split; [eapply gx_rt_sub; [|exact c_HGRT_s]; intros a Ha; exact (Hgs a (Hsub a Ha))|].
  split.
  { intros a Ha. destruct (c_rom_noerr a Ha) as [He Hh]. split; [|exact (conj (HPIN a Ha) (conj He Hh))].
    intros HGa. apply (c_rom_apart a Ha). apply obj_c. apply c_gs_obj. exact (Hsub a HGa). }
  split.
  { intros a Ha.
    assert (Hf : forallb (rng_all (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end))
      [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
    pose proof (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha))) as Hx.
    cbv beta in Hx. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hx]. }
  split.
  { intros a Ha m.
    assert (Hf : forallb (rng_all (segwb segs)) [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
    pose proof (segwb_ok segs a (rng_all_in _ _ a Hf (Hgs a (Hsub a Ha)))) as Hw.
    unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hw]. }
  intros ly S W mem md a n HAR Hn Hx. apply (HSHV ly S W mem md a n HAR Hn). intros x Hxr. exact (Hsub x (Hx x Hxr)).
Qed.

(* ---- ARM_write's facts (_write.v HGW, HERRS, ROM_ERR), verbatim with G_fr := G_fr_c and _write.v's wr_G written
   out ---- *)
(* HGW: the model's globals other than g_s *)
Lemma c_HGW : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8);
    (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1);
    (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_gone fr_RG, 1); (rg_lock fr_RG, 12);
    (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr_c a.
Proof.
  apply inG_sub.
  repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
  apply Forall_nil.
Qed.
(* errno apart from every range of a list, as a boolean *)
Lemma apart_of_b : forall L lo n, forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) L = true ->
  forall a, inG L a -> ~ (lo <= a < lo + n).
Proof.
  intros L lo n H a Ha Hlo. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Hz.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* HERRS: errno apart from g_s and the model's globals *)
Lemma c_HERRS : forall a, inG ((rg_s fr_RG, 4 * ASRC) :: [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4);
    (rg_client_broken fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)]) a ->
  ~ (as_errno B <= a < as_errno B + 4).
Proof. rewrite HEV. apply apart_of_b. vm_compute. reflexivity. Qed.
(* ROM_ERR: errno is no read-only byte *)
Lemma c_ROM_ERR : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha He. rewrite HEV in He.
  eapply (rom_apart_ok _ [(TFIB_ERRNO_A, 4)] a); [| exact Ha | apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia].
  vm_compute. reflexivity.
Qed.
End g.

(* ------------------------------------------------------------------ the re-based rom_out's instance obligation *)
(* W_journal.v rom_out (a working branch 45a3cc9bdd0) asks that an owned read-only byte be pinned by AR's const
   cells (rom_pinned).  At the start-up instance (AF0m's TfibSyms) every such byte is: 408 bytes in 18 runs of
   Tfib_owned_static lie in fuzz_reply.asan's read-only LOADs, and each is an AV (ANum v) cell of Tfib_const_abs at
   an ANum address holding the image's byte (W1's rom_owned_check.py (sha256 13958cb8b3c1; internal record): 408 pinned, 0 wrong, 0 missing; run by
   own-zsh-check.py (sha256 5876c8bf7a46; internal record)).  Checked here by one vm_compute over Tfib_owned_static's bytes. *)
Definition num_of (e : YG0f.aexp) : option Z := match e with YG0f.ANum z => Some z | _ => None end.
Definition av_num (v : YG0f.aval) : option Z := match v with YG0f.AV (YG0f.ANum z) => Some z | _ => None end.
Lemma num_of_some : forall e z, num_of e = Some z -> e = YG0f.ANum z.
Proof. intros e z H. destruct e; cbn in H; congruence. Qed.
Lemma av_num_some : forall v z, av_num v = Some z -> v = YG0f.AV (YG0f.ANum z).
Proof. intros v z H. destruct v as [e|m w]; [destruct e|]; cbn in H; congruence. Qed.

Section rp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Definition romb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma romb_of : forall a, in_rom segs a -> romb a = true.
Proof.
  intros a (sg & Hs & Hw & Hr). unfold romb. apply existsb_exists. exists sg. split; [exact Hs|].
  rewrite Hw. cbn [negb andb]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* `if`, not `&&` / `||`: the VM evaluates both arguments of andb / orb (a `||` here walked all 5.4 MB of owned bytes), and seg_rom (a walk of the read-only segment's bytes) for
   every one of Tfib_const_abs's 440 cells per byte ran > 1 h (measured 09:2x-10:2xZ on b5) *)
Definition pin_ok (a : Z) (c : YG0f.acell) : bool :=
  match num_of (YG0f.c_at c), av_num (YG0f.c_val c) with
  | Some z, Some v =>
      if (z <=? a) && (a <? z + Z.of_nat (YG0f.c_w c)) then
        match seg_rom segs (Z_to_bv 64 a) with
        | Some b => YG0f.le_byte v (YG0f.c_w c) (Z.to_nat (a - z)) =? bv_unsigned b
        | None => false
        end
      else false
  | _, _ => false
  end.
Lemma pin_ok_spec : forall a c, pin_ok a c = true -> exists z v,
  YG0f.c_at c = YG0f.ANum z /\ YG0f.c_val c = YG0f.AV (YG0f.ANum v) /\ z <= a < z + Z.of_nat (YG0f.c_w c) /\
  Some (YG0f.le_byte v (YG0f.c_w c) (Z.to_nat (a - z))) =
    option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof.
  intros a c H. unfold pin_ok in H.
  destruct (num_of (YG0f.c_at c)) as [z|] eqn:E1; [|discriminate].
  destruct (av_num (YG0f.c_val c)) as [v|] eqn:E2; [|discriminate].
  exists z, v. apply num_of_some in E1. apply av_num_some in E2.
  destruct ((z <=? a) && (a <? z + Z.of_nat (YG0f.c_w c))) eqn:H1; [|discriminate].
  apply andb_prop in H1 as [H1a H1b]. apply Z.leb_le in H1a. apply Z.ltb_lt in H1b.
  split; [exact E1|]. split; [exact E2|]. split; [lia|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate]. apply Z.eqb_eq in H. cbn. rewrite H. reflexivity.
Qed.
(* a range that meets no read-only segment holds no in_rom byte; only the others are walked byte by byte (the
   first version walked every owned byte, 5.4 MB of them, and ran > 30 min: measured 09:2xZ on b5) *)
Definition rom_free (r : Z * Z) : bool :=
  forallb (fun sg => seg_writable sg || (fst r + snd r <=? Z.of_N (seg_base sg)) ||
    (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) segs.
Lemma rom_free_ok : forall r a, rom_free r = true -> in_zr a r -> in_rom segs a -> False.
Proof.
  intros r a H Hz (sg & Hs & Hw & Hr). unfold rom_free in H. rewrite forallb_forall in H. specialize (H sg Hs).
  rewrite Hw in H. cbn [orb] in H. unfold in_zr in Hz.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Definition owned_rom_pinned_b : bool :=
  forallb (fun r => if rom_free r then true else
    rng_all (fun a => if romb a then existsb (pin_ok a) AF0m.Tfib_const_abs else true) r) AF0m.Tfib_owned_static.
Lemma owned_rom_pinned_ok : owned_rom_pinned_b = true.
Proof. vm_compute. reflexivity. Qed.

Variable B : asyms.
Hypothesis TS : AF0m.TfibSyms B.
(* the obligation: an owned read-only byte is pinned *)
Lemma c_rom_pinned : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
Proof.
  intros a Hr Ho ly.
  rewrite (AF0m.ts_owned B TS) in Ho.
  pose proof owned_rom_pinned_ok as HO. unfold owned_rom_pinned_b in HO. rewrite forallb_forall in HO.
  apply Exists_exists in Ho as (r & Hr' & Hz).
  specialize (HO r Hr'). destruct (rom_free r) eqn:Hfree; [exfalso; exact (rom_free_ok r a Hfree Hz Hr)|].
  pose proof (rng_all_in (fun a => if romb a then existsb (pin_ok a) AF0m.Tfib_const_abs else true) [r] a
    ltac:(cbn [forallb]; rewrite HO; reflexivity) (Exists_cons_hd _ _ _ Hz)) as H.
  cbv beta in H.
  rewrite (romb_of a Hr) in H.
  apply existsb_exists in H as (c & Hc & Hp).
  destruct (pin_ok_spec a c Hp) as (z & v & Ea & Ev & Hzr & Hbyte).
  exists c, (YG0f.ANum v).
  rewrite (AF0m.ts_const B TS ly). unfold AF0m.Tfib_const.
  split; [apply in_or_app; right; apply in_or_app; left; exact Hc|].
  split; [exact Ev|]. rewrite Ea. cbn [YG0f.aeval]. split; [exact Hzr | exact Hbyte].
Qed.

(* XRF_ROM_OUT (W_xrf.v:192) at G_fr := G_fr_c B, with the ASan sink_head (AE2k.tfib_sink_head, ofl_head
   0x5f9b68) passed explicitly: rom_out itself *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
Lemma c_rom_out : @rom_out AE2k.tfib_sink_head segs B (G_fr_c B).
Proof.
  intros a Hr. pose proof (romb_of a Hr) as Hb.
  split; [exact (c_rom_apart B HEV a Hr)|].
  split; [exact (c_rom_pinned a Hr)|].
  assert (Hx : forall lo, forallb (fun i => negb (romb (lo + Z.of_nat i))) (seq 0 8) = true ->
                 ~ (lo <= a < lo + 4)).
  { intros lo H Ha. rewrite forallb_forall in H.
    assert (Hi : In (Z.to_nat (a - lo)) (seq 0 8)) by (apply in_seq; lia).
    specialize (H _ Hi). rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia.
    rewrite Hb in H. cbn in H. discriminate H. }
  split.
  - rewrite HEV. apply Hx. vm_compute. reflexivity.
  - intros Ha. assert (Hy : forall lo, forallb (fun i => negb (romb (lo + Z.of_nat i))) (seq 0 8) = true ->
                 ~ (lo <= a < lo + 8)).
    { intros lo H Ha'. rewrite forallb_forall in H.
      assert (Hi : In (Z.to_nat (a - lo)) (seq 0 8)) by (apply in_seq; lia).
      specialize (H _ Hi). rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia.
      rewrite Hb in H. cbn in H. discriminate H. }
    exact (Hy (@AOFL_HEAD AE2k.tfib_sink_head) ltac:(vm_compute; reflexivity) Ha).
Qed.
End rp.
