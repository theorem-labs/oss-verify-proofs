(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The global set G_fr of fuzz_reply.asan-ubsan's LLVMFuzzerTestOneInput, concretely, and every G_fr / errno /
   image fact that the image-B W8 segment files (W_LLVMFuzzerTestOneInput_*.v) take as a Section hypothesis, proved
   for it.  At integration these lemmas discharge the hypotheses.  The image-B twin of
   lib/A/W_LLVMFuzzerTestOneInput_G.v.

   THE METHOD (lib/A's, unchanged): write ONE concrete witness for the objects the segments share and prove every
   hypothesis TEXT about them for it, in one file.  A single model that satisfies all of them rules out a
   contradiction among them, across files too, which reading pairs never can.  On image A this found HG_SL
   (send_line's G_SL, which names errno, inside G_fr) against HG_err / HGRT (errno outside G_fr): five A files had
   to be re-cut.  NEVER state `gx_rt B G_fr` or `inG G_fr a -> ~ errno` at this G: G_fr_c HOLDS errno's 4 bytes.
   What the witness does NOT check: the RINV / LS rule families (predicate Variables) and single-object instance
   facts; but SEG_HEAD's four model rules are restated at the instance's own model invariants (Section hm, last).

   G_fr_c = the program's 20 objects [addr, addr + plain size) ++ errno's 4 bytes (send_line stores errno, and its
   G_SL names it, lib/B/W_contract.v G_SL).  The 20 B addresses are the symbol table of the pinned
   fuzz_reply.asan-ubsan (sha256 10ffb5f9202ae2bd...) and OBJMAP-W4.md (sha256 1f0edf2c6e59; internal record); the plain sizes are the C
   source's, the same as image A's (nm's sizes are ASan's padded ones: 0x20 for a scalar, 0x60 for g_lock,
   0x1e0 for g_s).  509 bytes + errno's 4 = 513, as on A.

   Premises, each a start-up / instance fact discharged at the milestone, and the MEASUREMENT this witness rests
   on (a change of either lib/B/YF0m.v row invalidates it):
     HEV  : as_errno B = 0x5d994c - YF0m's `ts_errno : as_errno B = TFIB_ERRNO` with `TFIB_ERRNO : Z := 0x5d994c`
            (lib/B/YF0m.v:21 and :874; = TFIB_TP 0x5d99f0 - 164);
     HOWN : the bytes of G_fr_c are not in as_owned_static B - YF0m's `ts_owned : as_owned_static B =
            Tfib_owned_static` (YF0m.v:821 and :883), by vm_compute at the milestone.
            MEASURED on this tree's lib/B/YF0m.v: 0 of G_fr_c's 513 bytes lie in its 61 Tfib_owned_static ranges;
            every byte of each object's ASan redzone (padded size minus plain size) DOES lie in them; and
            Tfib_zero_shadow (YF0m.v:819, `ts_zsh` :874) has the range (0x5d8e60, 0x5d8fe0 - 0x5d8e60) = g_s's
            384 bytes, which makes `azs B (rg_s fr_RG) (4 * ASRC)` (HZS / AZS_s) true.
            Also measured here: 19 of the 61 owned ranges (408 bytes in all) meet a read-only LOAD of image B, and
            every one of those 408 bytes is an AV (ANum v) cell of YF0m's Tfib_const_abs at an ANum address holding
            the image's byte - 0 missing, 0 wrong - which is what owned_rom_pinned_ok below vm_computes. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
(* YE01 and YE2k are lib/B's: the program contract lib/B/YCfn.v states ameta_inv / arodata_okS /
   asink_none over them, so the cf twin below says the same words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
(* ashp and shp_ashp (g_s's shadow facts, c_gs_ashp below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
(* the generated start-up table of image B (home: a working branch; carried by path), for rom_pinned *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* SEG_HEAD's model functions and a Theorem Labs lane's model invariants (Section hm below); Require only, so none of their names
   shadows a name used here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_head ReplyLSB ReplyRINVB.
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
   hidden byte, and wview then reads the segment) *)
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
(* fuzz_reply.asan-ubsan's 20 program objects, [addr, addr + plain size), in the table order of GLOBALS.md (sha256 d3788bf0c2b6; internal record): g_s, g_nfd,
   g_out, g_nout, g_capout, g_send_max, g_send_eintr, g_send_dead, g_gone, g_lock, g_thread, g_thread_up, g_stop,
   g_listen, g_client, g_client_broken, g_wake, g_src, g_nsrc, g_capsrc (509 bytes). *)
Definition G_fr_obj : list (Z * Z) :=
  [ (0x5d8e60, 384); (0x5d8da0, 4); (0x5d90c0, 8); (0x5d8e40, 8); (0x5d90a0, 8); (0x5d8dc0, 8);
    (0x5d8e20, 1); (0x5d8e00, 1); (0x5d8de0, 1); (0x5d9040, 40); (0x5d8cc0, 8); (0x5d8ce0, 1);
    (0x5d8d00, 4); (0xa2540, 4); (0xa2560, 4); (0x5d8d60, 1); (0xa2520, 8); (0x5d8d40, 8);
    (0x5d8d20, 4); (0x5d8d80, 4) ].
Definition TFIB_ERRNO_B : Z := 0x5d994c.

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Definition G_fr_c : list (Z * Z) := G_fr_obj ++ [(as_errno B, 4)].
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.

Lemma obj_c : forall a, inG G_fr_obj a -> inG G_fr_c a.
Proof. intros a Ha. unfold G_fr_c. apply inG_app. left. exact Ha. Qed.
Lemma err_c : forall a, as_errno B <= a < as_errno B + 4 -> inG G_fr_c a.
Proof. intros a Ha. unfold G_fr_c. apply inG_app. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma G_fr_c_val : G_fr_c = G_fr_obj ++ [(TFIB_ERRNO_B, 4)].
Proof. unfold G_fr_c. rewrite HEV. reflexivity. Qed.

(* ---- the coverage hypotheses, verbatim with G_fr := G_fr_c ---- *)
(* HGs: the drain, exit, small, write arms and the relay-finish pieces *)
Lemma c_HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HGnout: the head segment *)
Lemma c_HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_nout fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HGlock / HGlk *)
Lemma c_HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_lock fr_RG) 12 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_client / HGcl *)
Lemma c_HG_client : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_client fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_cbroken *)
Lemma c_HG_cbroken : forall a, rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_client_broken fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_nfd (B's g_nfd is 0x5d8da0; the cut file's AG_NFD) *)
Lemma c_HG_nfd : forall a, AG_NFD <= a < AG_NFD + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover AG_NFD 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_smax / HGmx *)
Lemma c_HG_smax : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_max fr_RG) 8 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_gone / HGgn *)
Lemma c_HG_gone : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_gone fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_sdead / HGdd *)
Lemma c_HG_sdead : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_dead fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_seintr / HGei *)
Lemma c_HG_seintr : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_send_eintr fr_RG) 1 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* HG_SL: send_line's G, errno included *)
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
(* HG_DR: drain's G, g_s then send_line's *)
Lemma c_HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr_c a.
Proof.
  intros a Ha. unfold G_DR in Ha. apply inG_cons in Ha as [Ha|Ha]; [|exact (c_HG_SL a Ha)].
  exact (obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
Qed.
(* HG_RF: relay_finish's G, at GL = g_listen (the cut file's AG_LISTEN) *)
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
(* HG_cnl: check_no_loss's G = [(g_s, 384)] *)
Lemma c_HG_cnl : forall a, inG [(rg_s fr_RG, 4 * ASRC)] a -> inG G_fr_c a.
Proof.
  apply inG_sub.
  constructor; [exact (fun a Ha => obj_c a (rng_cover_zr (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha))|].
  constructor.
Qed.

(* ---- the image facts ---- *)
(* GWL / GWR: every byte of G_fr_c is writable in every memory *)
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
(* the rom_out conjunct: no read-only byte is in G_fr_c *)
Lemma c_rom_apart : forall a, in_rom segs a -> ~ inG G_fr_c a.
Proof. intros a. rewrite G_fr_c_val. apply rom_apart_ok. vm_compute. reflexivity. Qed.

(* ---- errno's place ---- *)
(* HERRNO: the head segment *)
Lemma c_HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
Proof. rewrite HEV. vm_compute. split; [discriminate|]. split; [discriminate|]. right. discriminate. Qed.
(* ERRNO_LOW: the latch segment (CEIL8 = alloc_ceiling + 8) *)
Lemma c_ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling + 8.
Proof. rewrite HEV. pose proof alloc_ceiling_value as (Hc & _). unfold TFIB_ERRNO_B. lia. Qed.
(* HERRHI: errno's cell lies above g_out (0x5d90c0), the highest of the program's globals *)
Lemma c_HERRHI : rg_out fr_RG + 8 <= as_errno B.
Proof. rewrite HEV. vm_compute. discriminate. Qed.

(* ---- the image objects the drain arm reads are apart from g_s: HAP.
   On image B the shadow GOT slot is A_OBJ 0 (0x9df50) and __asan_shadow_memory_dynamic_address is A_OBJ 30
   (0xa6638); on image A they are A_OBJ 0 and A_OBJ 32 (OBJMAP-W4.md sha256 1f0edf2c6e59; internal record). ---- *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Lemma c_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
              (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG).
Proof.
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 30)) || (VAL (A_OBJ 30) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1. split.
  - destruct H0 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
  - destruct H1 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.

(* ---- ARM_write's facts (W_LLVMFuzzerTestOneInput_write.v HGW, HERRS, ROM_ERR), verbatim with G_fr := G_fr_c and
   _write.v's wr_G written out (the B globals of fr_globals_b, g_nfd 0x5d8da0, g_thread_up 0x5d8ce0,
   g_listen 0xa2540) ---- *)
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
  eapply (rom_apart_ok _ [(TFIB_ERRNO_B, 4)] a); [| exact Ha | apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia].
  vm_compute. reflexivity.
Qed.

(* ---- ARM_remove (lib/B/W_LLVMFuzzerTestOneInput_remove.v Section rmw): its G_fr / errno / image facts ---- *)
(* HGnsrc *)
Lemma c_HGnsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr_c a.
Proof. exact (fun a Ha => obj_c a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)). Qed.
(* g_s is one of the 20 objects, and no byte of the 20 objects is errno's *)
Lemma c_gs_obj : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr_obj a.
Proof. exact (fun a Ha => rng_cover (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity) a Ha). Qed.
Lemma c_obj_noerr : forall a, inG G_fr_obj a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha He. rewrite HEV in He.
  assert (Hf : forallb (rng_all (fun x => negb ((TFIB_ERRNO_B <=? x) && (x <? TFIB_ERRNO_B + 4)))) G_fr_obj = true)
    by (vm_compute; reflexivity).
  pose proof (rng_all_in _ G_fr_obj a Hf Ha) as Hx. apply negb_true_iff in Hx.
  rewrite (proj2 (Z.leb_le _ _) (proj1 He)), (proj2 (Z.ltb_lt _ _) (proj2 He)) in Hx. discriminate Hx.
Qed.
(* HGRT_s: gx_rt of g_s (errno apart: c_obj_noerr; the shadow GOT slot A_OBJ 0 and cell A_OBJ 30 apart: c_HAP) *)
Lemma c_HGRT_s : gx_rt B [(rg_s fr_RG, 4 * ASRC)].
Proof.
  intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha. cbn [fst snd] in Ha.
  split; [exact (c_obj_noerr a (c_gs_obj a Ha))|].
  pose proof c_HAP as (H0 & H30). clear - Ha H0 H30. split; lia.
Qed.
(* HMG's cells: rm_mglob's 13 cells (its text, spelled out) are bytes of the 20 objects *)
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
End g.

(* ------------------------------------------------------------------ the re-based rom_out's instance obligation *)
(* W_journal.v rom_out asks that an owned read-only byte be pinned by AR's const cells (rom_pinned).  At image B's
   start-up instance (YF0m's TfibSyms) every such byte is: 408 bytes in 19 runs of Tfib_owned_static lie in
   fuzz_reply.asan-ubsan's read-only LOADs, and each is an AV (ANum v) cell of Tfib_const_abs at an ANum address
   holding the image's byte.  Checked here by one vm_compute over Tfib_owned_static's bytes. *)
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
(* `if`, not `&&` / `||`: the VM evaluates both arguments of andb / orb (a `||` here walked all 5.4 MB of owned
   bytes on image A), and seg_rom (a walk of the read-only segment's bytes) for every one of Tfib_const_abs's 440
   cells per byte ran > 1 h there *)
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
(* a range that meets no read-only segment holds no in_rom byte; only the others are walked byte by byte *)
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
    rng_all (fun a => if romb a then existsb (pin_ok a) YF0m.Tfib_const_abs else true) r) YF0m.Tfib_owned_static.
Lemma owned_rom_pinned_ok : owned_rom_pinned_b = true.
Proof. vm_compute. reflexivity. Qed.

Variable B : asyms.
Hypothesis TS : YF0m.TfibSyms B.
(* the obligation: an owned read-only byte is pinned *)
Lemma c_rom_pinned : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
Proof.
  intros a Hr Ho ly.
  rewrite (YF0m.ts_owned B TS) in Ho.
  pose proof owned_rom_pinned_ok as HO. unfold owned_rom_pinned_b in HO. rewrite forallb_forall in HO.
  apply Exists_exists in Ho as (r & Hr' & Hz).
  specialize (HO r Hr'). destruct (rom_free r) eqn:Hfree; [exfalso; exact (rom_free_ok r a Hfree Hz Hr)|].
  pose proof (rng_all_in (fun a => if romb a then existsb (pin_ok a) YF0m.Tfib_const_abs else true) [r] a
    ltac:(cbn [forallb]; rewrite HO; reflexivity) (Exists_cons_hd _ _ _ Hz)) as H.
  cbv beta in H.
  rewrite (romb_of a Hr) in H.
  apply existsb_exists in H as (c & Hc & Hp).
  destruct (pin_ok_spec a c Hp) as (z & v & Ea & Ev & Hzr & Hbyte).
  exists c, (YG0f.ANum v).
  rewrite (YF0m.ts_const B TS ly). unfold YF0m.Tfib_const.
  split; [apply in_or_app; right; apply in_or_app; left; exact Hc|].
  split; [exact Ev|]. rewrite Ea. cbn [YG0f.aeval]. split; [exact Hzr | exact Hbyte].
Qed.

(* rom_out at G_fr := G_fr_c B, with the ASan+UBSan sink_head (YE2k.tfib_sink_head, ofl_head 0x5fa0e8) passed
   explicitly (ReplyGuardB removed every sink hint) *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.
Lemma c_rom_out : @rom_out YE2k.tfib_sink_head segs B (G_fr_c B).
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
    exact (Hy (@AOFL_HEAD YE2k.tfib_sink_head) ltac:(vm_compute; reflexivity) Ha).
Qed.
(* ---- ARM_remove's instance facts at image B's start-up instance (TS), decided by vm_compute ---- *)
(* no byte of the 20 objects is an owned static (YF0m's Tfib_owned_static, 61 ranges) *)
Lemma c_obj_unowned : forall a, inG G_fr_obj a -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
  intros a Ha Ho. rewrite (YF0m.ts_owned B TS) in Ho.
  assert (Hf : forallb (rng_all (fun x => negb (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r))
                 YF0m.Tfib_owned_static))) G_fr_obj = true) by (vm_compute; reflexivity).
  pose proof (rng_all_in _ G_fr_obj a Hf Ha) as Hx. apply negb_true_iff in Hx.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hb : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) YF0m.Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hb in Hx. discriminate Hx.
Qed.
(* QMm W0' (a Theorem Labs lane): gx_ok's kept clause at G_fr_c B - no byte of G_fr_c (the 20 objects and errno's 4) is a kept byte
   (YF0m's Tfib_kept: the non-owned RELRO and part 3c's five read-only read ranges). The B twin of lib/A's
   W_LLVMFuzzerTestOneInput_addI.zz_HKEPT; this vm_compute is a Theorem Labs lane's check that no concrete G meets as_kept. *)
Lemma c_HKEPT : forall a, inG (G_fr_c B) a -> ~ Exists (in_zr a) (as_kept B).
Proof.
  intros a Ha Ho. rewrite (YF0m.ts_kept B TS) in Ho. unfold G_fr_c in Ha. rewrite HEV in Ha.
  assert (Hf : forallb (rng_all (fun x => negb (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r))
                 YF0m.Tfib_kept))) (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]) = true) by (vm_compute; reflexivity).
  pose proof (rng_all_in _ _ a Hf Ha) as Hx. apply negb_true_iff in Hx.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hb : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) YF0m.Tfib_kept = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hb in Hx. discriminate Hx.
Qed.
Lemma c_obj_unkept : forall a, inG G_fr_obj a -> ~ Exists (in_zr a) (as_kept B).
Proof. intros a Ha. exact (c_HKEPT a (obj_c B a Ha)). Qed.
(* HMG *)
Lemma c_HMG : forall a, c_mglob a ->
  in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. pose proof (c_mglob_obj a Ha) as Ho.
  exact (conj (c_img B HEV a (obj_c B a Ho)) (conj (c_obj_unowned a Ho) (c_obj_noerr B HEV a Ho))).
Qed.
(* HZS: g_s's 384 bytes are one of the instance's zero-shadow ranges (YF0m's Tfib_zero_shadow (0x5d8e60, 0x180)) *)
Lemma c_HZS : azs B (rg_s fr_RG) (4 * ASRC).
Proof.
  exists (0x5d8e60, 0x180). rewrite (YF0m.ts_zsh B TS).
  split; [unfold YF0m.Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right])|].
  cbn [fst snd]. assert (VS : rg_s fr_RG = 0x5d8e60) by reflexivity. rewrite VS. unfold ASRC.
  split; [reflexivity | lia].
Qed.
(* g_s's shadow facts in every AR state: shp_check over YF0m's const shadow and zero-shadow tables *)
Lemma c_gs_ashp : ashp (PI := PB_fr) B (rg_s fr_RG) (4 * ASRC).
Proof.
  apply (shp_ashp B YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow).
  - intros ly c Hc. rewrite (YF0m.ts_const B TS ly). unfold YF0m.Tfib_const.
    apply in_or_app. right. apply in_or_app. right. exact Hc.
  - intros r Hr. rewrite (YF0m.ts_zsh B TS). exact Hr.
  - vm_compute. reflexivity.
Qed.
(* HGP: gx_prog of each slot g_s[si] (source_reset's own G; check_no_loss's and check_shape_ends' through
   gx_prog_sub) *)
Lemma c_HGP : forall si, (si < 4)%nat ->
  gx_prog (SK := YE2k.tfib_sink_head) (PI := PB_fr) B [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)].
Proof.
  intros si Hsi.
  assert (Hsub : forall a, inG [(rg_s fr_RG + ASRC * Z.of_nat si, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
  { intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
    unfold in_zr in Ha. cbn [fst snd] in Ha. clear - Ha Hsi. unfold ASRC in *. lia. }
  assert (Hgs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG [(rg_s fr_RG, 4 * ASRC)] a)
    by (intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; exact Ha).
  split; [intros a Ha; pose proof (Hsub a Ha) as Hs;
          exact (conj (c_img B HEV a (obj_c B a (c_gs_obj a Hs)))
            (conj (c_obj_unowned a (c_gs_obj a Hs)) (c_obj_unkept a (c_gs_obj a Hs))))|].
  split; [eapply gx_rt_sub; [|exact (c_HGRT_s B HEV)]; intros a Ha; exact (Hgs a (Hsub a Ha))|].
  split.
  { intros a Ha. destruct (c_rom_out a Ha) as (Hn & Hp & He & Hh). split; [|exact (conj Hp (conj He Hh))].
    intros HGa. apply (c_rom_apart B HEV a Ha). apply (obj_c B). apply c_gs_obj. exact (Hsub a HGa). }
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
  intros ly S W mem md a n HAR Hn Hx.
  assert (Ha0 : rg_s fr_RG <= a) by exact (proj1 (Hsub a (Hx a ltac:(lia)))).
  assert (Ha1 : a + n - 1 < rg_s fr_RG + 4 * ASRC) by exact (proj2 (Hsub (a + n - 1) (Hx (a + n - 1) ltac:(lia)))).
  destruct (c_gs_ashp ly S W mem md HAR) as [_ Hh].
  intros s Hs. apply (Hh ltac:(unfold ASRC; lia)).
  assert (M0 : shadow_addr (rg_s fr_RG) / 8 * 8 <= shadow_addr a / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
    apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  assert (M1 : shadow_addr (a + n - 1) / 8 * 8 <= shadow_addr (rg_s fr_RG + 4 * ASRC - 1) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
    apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  lia.
Qed.
End rp.

(* ------------------------------------------------------------------ SEG_HEAD's four model rules at the instance *)
(* lib/B/W_LLVMFuzzerTestOneInput_head.v :274 / :275 / :278 / :281 (B head_x's Section hypotheses RI_head_nout /
   LS_head_nout / RI_head_skip / LS_head_skip, top_x's verbatim hypotheses) at the instance's model invariants
   RINV := ReplyRINVB.fr_RINV and LS := ReplyLSB.fr_LS B CALL_ROOM_B, text for text: a Theorem Labs lane's ruling that the
   head premises' instance facts are plugged here; the B cf top (which instantiates top_x's LSx / RINV) cites them.
   They are a Theorem Labs lane's RI_head_nout_b / LS_head_nout_b / RI_head_skip_b / LS_head_skip_b
   (a working branch fdb3ee1c6ffa) and hold at every CALL_ROOM_B. *)
Section hm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Local Notation LS := (ReplyLSB.fr_LS B CALL_ROOM_B).
Local Notation RINV := ReplyRINVB.fr_RINV.
Local Notation lm_clear_O := W_LLVMFuzzerTestOneInput_head.lm_clear_O.
Local Notation lm_set_k := W_LLVMFuzzerTestOneInput_head.lm_set_k.
Local Notation hd_kb := W_LLVMFuzzerTestOneInput_head.hd_kb.
Local Notation hd_k' := W_LLVMFuzzerTestOneInput_head.hd_k'.
Lemma c_RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Proof. exact ReplyRINVB.RI_head_nout_b. Qed.
Lemma c_LS_head_nout : forall cx t m ly S, LS cx t m ly S -> LS cx t (lm_clear_O m) ly S.
Proof. exact (ReplyLSB.LS_head_nout_b B CALL_ROOM_B). Qed.
Lemma c_RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Proof. exact ReplyRINVB.RI_head_skip_b. Qed.
Lemma c_LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LS cx t m ly S -> LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. exact (ReplyLSB.LS_head_skip_b B CALL_ROOM_B). Qed.
End hm.
