(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the ENT segment of the image-B walk of fuzz_reply's relay_add over a
   GENERIC allocator relation ARx (route (b), CONVERSION.md (sha256 1015972e02a9; internal record)), in the ROOM form:
   pb_rb_ent_x : rb_ent_stmt B PST ARx MT RP G RG CTX (lib/B/W_relay_add_cut_x.v).  Converted from the AR segment
   lib/B/W_relay_add_ent.v (pb_ra_ent : ra_ent_stmt, a working branch 22c3862876d), whose machine-code
   account holds unchanged: the entry 0x82af4, the prologue 0x82af4-0x82b14 (sp -= 64; ra, s0 .. s6 saved at
   56(sp) .. 0(sp)), s1 = -1, the test `bltz a0` 0x82b1c, and then either

     fd < 0   the epilogue 0x82c18-0x82c3c and the return (a0 = -1): ra_post_x's left arm, in this segment; or
     fd >= 0  s0 = fd, s2 = the shadow offset (the GOT slot -> the shadow cell, 0x82b24-0x82b2c), a0 = &g_lock
              (0x82b30-0x82b34) and pthread_mutex_lock 0x82b38 (ALOCK over ARx, through W_sites_x.v
              aj_gx_entry_at_x) -> the cut RBH at 0x82b3c.

   NO TRAP EDGE in this segment: the only branch is `bltz a0` (the fd test), not a check.
   The conversion: afn_pre -> afn_pre_x, and the entry seat rbe_entry over it (image A's ra_entry in its room-form
   walk is the model); ajournal_gx_init, the token runs, ajournal_gx_AR and ajournal_gx_materialize -> their _x twins
   (W_journal_x.v; W_kit_x.v paj_run_tok_x), with the head set Hp after S; the AR laws -> the AR_laws_x fields
   (alx_const, alx_owned_image, alx_blocks, alx_client_img); alock_realizes -> alock_realizes_x B ARx.  No step of
   this segment changes the allocator state or its head set (the runs write the frame, the lock call keeps ly S Hp),
   so RBH holds at the entry's bxly / bxS / bxHp with k = 0.
   The room: the fd < 0 return makes no allocator call, so ra_post_x's `rp_RM RP S' kr` at S' = the entry's state is
   BBASE's `rp_RM RP S (Z.to_nat (ra_cost MT_rk T) + kr)` by the budget's monotonicity (W_journal_x.v RMM_of).
   rom_view at RBH is read off the bytes the walk keeps (a ROM byte is an image byte, so below alloc_ceiling, and by
   HNROM it is off the lock word), so this segment takes no rom_out or PST fact.
   errno's four bytes keep their view: they lie below kLowMemEnd, so outside the frame (the runs' only write window)
   and outside the lock call's scratch, and off g_lock's lock word (ra_spec_x's premise that RA_G excludes errno),
   the one byte range the lock call writes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_kit_x W_sites_x W_contract_x W_relay_add_cut_x.
(* route R: SRrG / wle' (YA0nH) and relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag the donor's proofs run with, whatever a Required file leaves *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* the fd test `bltz a0` reads a0 signed: the 32-bit fd of ra_spec_x is its own signed value *)
Lemma rbe_fd_signed : forall fd, - 2 ^ 31 <= fd < 2 ^ 31 -> bv_signed (Z_to_bv 64 fd) = fd.
Proof.
intros fd Hfd. assert (HU : bv_unsigned (Z_to_bv 64 fd) = if fd <? 0 then fd + 2 ^ 64 else fd).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec fd 0); [symmetry; apply (Z.mod_unique fd (2 ^ 64) (-1)); lia | apply Z.mod_small; lia]. }
destruct (Z.ltb_spec fd 0).
- rewrite bv_signed_hi by lia. lia.
- rewrite bv_signed_small by lia. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The entry state at 0x82af4.  The frame [sp - 64, sp) is the one writable window; the GOT slot and the
   shadow cell are read-only chunk regions (the prologue's two loads); atom 32 is the shadow offset SB. ---- *)
Definition rbe_Bx : sv := SOff 32 0.
Definition rbe_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rbe_regions : smem := [ stack_region RA_FRAME; got_regionP; bcell_regionP 32 ].
Definition rbe_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rbe : sstate := mkSS A_relay_add sr_atoms rbe_regions None rbe_facts.
Definition rbe_SH : list shent := [].
Definition rbe_extra : list word := [Z_to_bv 64 SB].

(* ---- Small forms the segment needs (W_gestures_end.v's, W_frame.v's, at arm). ---- *)
Lemma rbe_vm_kept : forall H H' (m m' : word -> option byte) a n v, val_mem SEGS (mrestrict H m) a n v ->
(forall b, a <= b < a + Z.of_nat n -> aview SEGS H' m' b = aview SEGS H m b) -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply (val_mem_kept SEGS H H' m m' a n v); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
Lemma rbe_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma rbe_wkept : forall (W : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W) m' a) -> writable_at SEGS (arm W m) a -> writable_at SEGS (arm W m') a.
Proof. intros W m m' a Hp Hw. unfold arm in *. exact (writable_kept (w_H W) m m' a Hp Hw). Qed.
Lemma rbe_req_pos : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma rbe_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round's record (W_journal_x.v Record roomp): the room invariant rp_RM with its laws rp_RMM / rp_RPF *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* the allocator rules' caller-context table (W_contract_x.v Section w5's CTX) *)
Variable CTX : list (list Z).
Context {hl : Z}.
(* the generic allocator relation's laws (YCbqG.AR_laws_x), in place of the donor's AR_laws SEGS B *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
(* placement (W_relay_add_cut.v Section fr decides them TRUE at the pin: ra_hv_fr, ra_aligned_fr, ra_cells_fr) *)
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HRGA : ra_aligned RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
(* pthread_mutex_lock's entry over ARx (W_sites_x.v alock_realizes_x: keeps ly S Hp) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- Bytes kept.  A byte of relay_add's globals is an image byte of RA_G; a byte of a live block is below
   alloc_ceiling and outside the image; both are far below every stack frame. ---- *)
Lemma rbe_glob_in_img : forall a, inG (RA_G RG) a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
Lemma rbe_not_owned : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* alock_at at a memory that keeps the lock's twelve bytes and presence *)
Lemma rbe_alock_kept : forall (W : world SEGS) m m' b,
alock_at RG W m b ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
alock_at RG W m' b.
Proof.
intros W m m' b (V0 & V4 & V8 & VW) KL KP. unfold arm in V0, V4, V8, VW |- *.
split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V0 | intros x Hx; apply KL; cbn in Hx; lia]|].
split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V4 | intros x Hx; apply KL; cbn in Hx; lia]|].
split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V8 | intros x Hx; apply KL; cbn in Hx; lia]|].
intros i Hi. apply (rbe_wkept W m m'); [exact (KP (rg_lock RG + i)) | exact (VW i Hi)].
Qed.
(* ---- Every byte the relay's predicate reads is a byte of one of its global cells or of a live block. ---- *)
Lemma rbe_efp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Proof.
intros ly S W m e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
  destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [exact Hin|].
  unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd] in Ha.
  rewrite (rbe_req_pos (re_cap e) Hcp). lia.
- destruct Hr as [<- | Hr].
  + destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)].
    * unfold gfp, bzs in Ha. rewrite length_map, Hk in Ha. cbn in Ha. lia.
    * exists (re_hp e), (re_kh e). split; [exact Hin|].
      unfold gfp, bzs in Ha. rewrite length_map, rbe_key_ptrs_len in Ha. cbn [fst snd] in Ha.
      unfold re_nheld in Hk1. rewrite (rbe_req_pos (re_kh e)) by lia. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4).
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [exact K1|].
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
    rewrite (rbe_req_pos (Z.of_nat (length (key_text k)) + 1)) by lia. lia.
Qed.
Lemma rbe_relay_blks : forall ly S W m T1 es, arelay_at B RG ly S W m T1 es ->
forall b, In b (arelay_blks T1 es) -> In b (ablocks B ly S).
Proof.
intros ly S W m T1 es HR b Hb.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & _ & HF & _).
unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact HinT|].
apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
rewrite Forall_forall in HF.
destruct (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15).
unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (Z.eqb_spec (re_cap e) 0); [destruct Hb|]. destruct Hb as [<- | []].
  destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_app_or in Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_hp e) 0); [destruct Hb|]. destruct Hb as [<- | []].
    destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
(* ra_rel at a later memory of the SAME allocator state (over ARx, at its head set Hp): the walk wrote only its frame
   and the lock word, so every byte the relay reads (a global cell, or a byte of a live block) keeps its view, and
   presence is kept. *)
Lemma rbe_rel_kept : forall ly S Hp (W : world SEGS) m m' md' T es,
ARx ly S Hp W m' md' ->
ra_rel B RG ly S W m T es ->
(forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG <= a < rg_lock RG + 12) ->
 aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
ra_rel B RG ly S W m' T es.
Proof.
intros ly S Hp W m m' md' T es HAR' HR KV KP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
ra_pick HRGP 2%nat 3%nat D23. ra_pick HRGP 2%nat 4%nat D24. ra_pick HRGP 2%nat 5%nat D25.
assert (KS : forall x, rg_src RG <= x < rg_src RG + 8 ->
  aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros x Hx. pose proof (rbe_glob_in_img x (ra_src_in RG x Hx)) as HR8. apply KV; lia. }
assert (KN : forall x, rg_nsrc RG <= x < rg_nsrc RG + 4 ->
  aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros x Hx. pose proof (rbe_glob_in_img x (ra_nsrc_in RG x Hx)) as HR8. apply KV; lia. }
assert (KC : forall x, rg_capsrc RG <= x < rg_capsrc RG + 4 ->
  aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros x Hx. pose proof (rbe_glob_in_img x (ra_capsrc_in RG x Hx)) as HR8. apply KV; lia. }
destruct HR as [(HT & Hes & (V1 & V2 & V3 & V4 & V5 & V6)) | HR].
- left. split; [exact HT|]. split; [exact Hes|].
  unfold arm in V1, V2, V3, V4, V5, V6 |- *.
  split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V1 | intros b Hb; apply KS; cbn in Hb; lia]|].
  split; [intros i Hi; apply (rbe_wkept W m m'); [exact (KP _) | exact (V2 i Hi)]|].
  split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V3 | intros b Hb; apply KN; cbn in Hb; lia]|].
  split; [intros i Hi; apply (rbe_wkept W m m'); [exact (KP _) | exact (V4 i Hi)]|].
  split; [apply (rbe_vm_kept (w_H W) (w_H W) m m'); [exact V5 | intros b Hb; apply KC; cbn in Hb; lia]|].
  intros i Hi. apply (rbe_wkept W m m'); [exact (KP _) | exact (V6 i Hi)].
- right.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & _ & HFe & _).
  assert (KB : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n -> abyte_kept W m W m' x).
  { intros p n x Hin Hx.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W m' md' p n HAR' Hin) as (_ & H4096 & Hceil & _ & HP & _).
    destruct (alx_client_img _ _ _ LAWS ly S Hp W m' md' x HAR'
      ltac:(left; exists p, n; split; [exact Hin | exact Hx])) as (_ & Hnimg).
    split.
    - apply KV; [lia|]. intros Hl. apply Hnimg. exact (proj1 (HG x (ra_lock_in RG x Hl))).
    - intros _. apply (apresent_writable SEGS). exact (proj1 (HP x Hx)). }
  assert (KG : forall x, (rg_src RG <= x < rg_src RG + 8 \/ rg_nsrc RG <= x < rg_nsrc RG + 4 \/
    rg_capsrc RG <= x < rg_capsrc RG + 4) -> abyte_kept W m W m' x).
  { intros x Hx. split.
    - destruct Hx as [Hx | [Hx | Hx]]; [apply KS | apply KN | apply KC]; exact Hx.
    - intros Hw. exact (rbe_wkept W m m' x (KP x) Hw). }
  apply (arelay_at_kept B RG ly S W m ly S W m' T es HR).
  + intros r Hr a Ha. unfold arelay_fp in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
    * apply KG. left. lia.
    * apply KG. right; left. lia.
    * apply KG. right; right. lia.
    * apply (KB T ATABLE a HinT). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
    * apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
      rewrite Forall_forall in HFe.
      destruct (rbe_efp_blk ly S W m e (HFe e He) r Hr a Ha) as (p & n & Hin & Hpa).
      exact (KB p n a Hin Hpa).
  + intros b Hb. exact (rbe_relay_blks ly S W m T es HR b Hb).
Qed.

(* ---- The entry seat at 0x82af4, from afn_pre_x (image A's room-form ra_entry is the model). ---- *)
Lemma rbe_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs rbe_extra)) ss_rbe
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_addP) mem (seg_rom SEGS)))
/\ sh_ok SEGS rbe_Bx rbe_SH (Eimg (Ereg regs rbe_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE Hal32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RA_STK = 16512) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs rbe_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_rbe, A_relay_addP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rbe_regions, stack_region, got_regionP, bcell_regionP, RA_FRAME.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ecell) by (pose proof (pa_val_range (A_OBJ 30)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 rbe_Bx SB);
      [cbn [sv_denot rbe_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold rbe_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ecell) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    cbn [base_val]. rewrite Usp. unfold RA_FRAME.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rbe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal32 C1 C3 WS Hstk0. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rbe_SH. constructor.
Qed.

(* every byte outside the frame [sp - 64, sp) is outside the write windows of the walk's states.  The caller
   leaves only Usp (sp's atom), HSPB (the frame is far above alloc_ceiling) and the byte's bound in the context. *)
Local Ltac rbe_outw Usp :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?Usp in Hr; unfold RA_STK, RA_FRAME, ASTACK in *; lia | ]);
destruct Hin.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this segment at a world relation R, over the cut interface's R forms
   (W_relay_add_cut_x.v Section cR): its runs and branches at their G twins, the call steps at R, the strict callees
   and the return lifted.  At the cf instance R := wle' SEGS RZ_cf. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Theorem pb_rb_ent_xR : rb_ent_stmtR B PST ARx MT RP G RG CTX R.
Proof.
unfold rb_ent_stmtR. intros cx HB K.
pose proof HB as (HPRE & Hal32 & HCNT & H10 & Rfd & HLOCK & HWAKE & HROM & HREL & HNEW & HGin & HGerr & HLIVE
  & HCTX & HMOK & HRM & HPK).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RA_STK = 16512) by reflexivity.
assert (HSPB : alloc_ceiling + RA_STK <= spZ (bxregs cx)) by lia.
(* errno's cell: four image bytes below kLowMemEnd (so below alloc_ceiling, far below the frame), none of them a byte
   of g_lock (ra_spec_x's premise: RA_G excludes errno) *)
assert (EL : forall i, 0 <= i < 4 -> 0 <= as_errno B + i < kLowMemEnd)
  by (intros i Hi; first [exact (proj1 (ra_errno_low B TL i Hi)) | exact (proj1 (ra_errno_low B MT G RG TL i Hi))]).
assert (ENL : forall i, 0 <= i < 4 -> ~ (rg_lock RG <= as_errno B + i < rg_lock RG + 12))
  by (intros i Hi Hl; exact (HGerr _ (ra_lock_in RG _ Hl) ltac:(lia))).
pose proof (rbe_glob_in_img (rg_lock RG) (ra_lock_in RG (rg_lock RG) ltac:(lia))) as BL0.
pose proof (rbe_glob_in_img (rg_lock RG + 11) (ra_lock_in RG (rg_lock RG + 11) ltac:(lia))) as BL1.
pose proof HRGA as (HLA & _ & _ & _).
destruct (rbe_entry (bxW cx) (bxly cx) (bxS cx) (bxHp cx) (bxregs cx) (bxmem cx) (bxmd cx) (bxch cx) HPRE Hal32)
  as [HS SHOK].
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl (RA_G RG) 0 [] RA_STK (ra_FP (bxT cx) (bxes cx))
  (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxregs cx) (bxmem cx) (bxmd cx) (bxch cx) HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg (bxregs cx) rbe_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (bxregs cx) r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (bxregs cx) _ 0)).
assert (HAE : env_agree 32 (Ereg (bxregs cx) rbe_extra) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ (bxregs cx)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10b : sv_denot E (SOff 10 0) = Z_to_bv 64 (bxfd cx))
by (cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), H10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
unfold cfg_at. change (w64 A_relay_addP) with (Z_to_bv 64 A_relay_addP).
unfold A_relay_addP, A_relay_add.
(* ---- 0x82af4-0x82b1c: the prologue and s1 = -1, to the fd test ---- *)
paj_run_tok_xR RUNR HS HJ SHOK rbe_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KR1 : forall a, 0 <= a < alloc_ceiling ->
  aview SEGS (w_H (bxW cx)) (ms_mem ms) a = aview SEGS (w_H (bxW cx)) (bxmem cx) a).
{ intros a Ha. apply (aview_kept_out E _ (w_H (bxW cx)) (bxmem cx) (ms_mem ms) HFr a ltac:(lia)).
  clear - Usp HSPB Ha. rbe_outw Usp. }
assert (PR1 : forall a, apresent (w_H (bxW cx)) (bxmem cx) a -> apresent (w_H (bxW cx)) (ms_mem ms) a).
{ intros a Hp. lazymatch goal with
  | Hg : mem_grows (mrestrict (w_H (bxW cx)) (bxmem cx)) (mrestrict (w_H (bxW cx)) (ms_mem ms)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
psrr_branch_tok RUNR BRR HS SHOK rbe_Bspan.
-
(* ======== fd < 0: the epilogue and the return (ra_post_xR's left arm) ======== *)
assert (Hneg : bxfd cx < 0).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  rewrite (rbe_fd_signed (bxfd cx) Rfd) in Hc. change (bv_signed (sv_denot E (SLit 0))) with 0 in Hc. exact Hc. }
paj_run_tok_xR RUNR HS HJ SHOK rbe_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KR2 : forall a, 0 <= a < alloc_ceiling ->
  aview SEGS (w_H (bxW cx)) (ms_mem ms0) a = aview SEGS (w_H (bxW cx)) (bxmem cx) a).
{ intros a Ha.
  lazymatch goal with
  | H : frame_of E ?rs (mrestrict (w_H (bxW cx)) (ms_mem ms)) (mrestrict (w_H (bxW cx)) (ms_mem ms0)) |- _ =>
    rewrite (aview_kept_out E rs (w_H (bxW cx)) (ms_mem ms) (ms_mem ms0) H a ltac:(lia))
    by (clear - Usp HSPB Ha; rbe_outw Usp) end.
  exact (KR1 a Ha). }
assert (PR2 : forall a, apresent (w_H (bxW cx)) (bxmem cx) a -> apresent (w_H (bxW cx)) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
  | Hg : mem_grows (mrestrict (w_H (bxW cx)) (ms_mem ms)) (mrestrict (w_H (bxW cx)) (ms_mem ms0)) |- _ =>
    exact (apresent_grows _ _ _ a Hg (PR1 a Hp)) end. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET (bxW cx) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold bPOSTR, ra_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists (bxly cx), (bxS cx), (bxHp cx), r, m, d, 0 end.
split; [cbn [ms_regs]; rewrite R1, (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split.
{ cbn [ms_mem]. eapply rb_liftR; [exact HB|].
  apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs). exact HJ. }
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ (bxregs cx) rbe_extra HS); [exact HAE | vm_compute; reflexivity] end. }
split. { intros a _ _ _ Hp. cbn [ms_mem]. exact (PR2 a Hp). }
split; [reflexivity|].
split.
{ apply (mle_weaken MT (bxS cx) (bxS cx) 0 (ra_cost MT (bxT cx)) MTL (mo_le_refl MT MTL (bxS cx))).
  unfold ra_cost. destruct (bxT cx =? 0);
  [pose proof (mo_malloc_nonneg MT MTL ATABLE ltac:(unfold ATABLE; lia)); pose proof (mo_free_nonneg MT MTL); lia | lia]. }
(* the room: no allocator call on this path, so the budget kr is BBASE's, less the realloc's charge (rp_RMM) *)
split; [exact (RMM_of RP (bxS cx) (bxkr cx) _ (Nat.le_add_l (bxkr cx) _) HRM)|].
split.
{ cbn [ms_mem]. apply (rbe_alock_kept (bxW cx) (bxmem cx) (ms_mem ms0) false HLOCK);
  [intros a Ha; apply KR2; lia | exact PR2]. }
split.
{ left. split; [exact Hneg|].
  split; [cbn [ms_regs]; rewrite R10; apply bv_eq; reflexivity | reflexivity]. }
(* errno: the two runs wrote only the frame *)
intros i Hi. cbn [ms_mem]. apply KR2. pose proof (EL i Hi). lia.
-
(* ======== fd >= 0: the shadow offset, &g_lock, the lock, and the cut RBHR ======== *)
assert (Hpos : 0 <= bxfd cx).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
  rewrite (rbe_fd_signed (bxfd cx) Rfd) in Hc. change (bv_signed (sv_denot E (SLit 0))) with 0 in Hc. exact Hc. }
paj_run_tok_xR RUNR HS HJ SHOK rbe_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KR2 : forall a, 0 <= a < alloc_ceiling ->
  aview SEGS (w_H (bxW cx)) (ms_mem ms0) a = aview SEGS (w_H (bxW cx)) (bxmem cx) a).
{ intros a Ha.
  lazymatch goal with
  | H : frame_of E ?rs (mrestrict (w_H (bxW cx)) (ms_mem ms)) (mrestrict (w_H (bxW cx)) (ms_mem ms0)) |- _ =>
    rewrite (aview_kept_out E rs (w_H (bxW cx)) (ms_mem ms) (ms_mem ms0) H a ltac:(lia))
    by (clear - Usp HSPB Ha; rbe_outw Usp) end.
  exact (KR1 a Ha). }
assert (PR2 : forall a, apresent (w_H (bxW cx)) (bxmem cx) a -> apresent (w_H (bxW cx)) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
  | Hg : mem_grows (mrestrict (w_H (bxW cx)) (ms_mem ms)) (mrestrict (w_H (bxW cx)) (ms_mem ms0)) |- _ =>
    exact (apresent_grows _ _ _ a Hg (PR1 a Hp)) end. }
(* the eight saved registers, in the frame as the call finds it *)
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
assert (SLOT : forall (od z : Z) (n : nat) (r : bv 5),
  In (YP09.mkChunk od (CVal 8 (SOff n 0)))
    [YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  ew E n = getr (bxregs cx) r -> z = spZ (bxregs cx) + od ->
  val_mem SEGS (mrestrict (w_H (bxW cx)) (ms_mem ms0)) z 8 (bv_unsigned (getr (bxregs cx) r))).
{ intros od z n r Hin' Hew ->.
  lazymatch type of HRG with region_ok _ _ _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
  apply (slot_of_region E (mrestrict (w_H (bxW cx)) (ms_mem ms0)) (spZ (bxregs cx)) cs lo hi wlo whi od (SOff n 0)
    (bv_unsigned (getr (bxregs cx) r)) HRG Usp) end.
  - clear - Hin'. vm_compute in Hin' |- *. tauto.
  - cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr (bxregs cx) r)) as Hrr;
    change (bv_modulus 64) with (2 ^ 64) in Hrr; lia. }
assert (SAVED0 : forall i, (i < 8)%nat ->
  val_mem SEGS (mrestrict (w_H (bxW cx)) (ms_mem ms0)) (spZ (bxregs cx) - RA_FRAME + 8 * Z.of_nat i) 8
    (bv_unsigned (getr (bxregs cx) (nth i RA_SAVED 0%bv)))).
{ intros i Hi.
  assert (Hc8 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat) by lia.
  unfold RA_FRAME; destruct Hc8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  cbn [RA_SAVED nth];
  [ apply (SLOT (-64) _ 22%nat 22%bv ltac:(cbv; tauto) (EE 22%nat 22%bv eq_refl))
  | apply (SLOT (-56) _ 21%nat 21%bv ltac:(cbv; tauto) (EE 21%nat 21%bv eq_refl))
  | apply (SLOT (-48) _ 20%nat 20%bv ltac:(cbv; tauto) (EE 20%nat 20%bv eq_refl))
  | apply (SLOT (-40) _ 19%nat 19%bv ltac:(cbv; tauto) (EE 19%nat 19%bv eq_refl))
  | apply (SLOT (-32) _ 18%nat 18%bv ltac:(cbv; tauto) (EE 18%nat 18%bv eq_refl))
  | apply (SLOT (-24) _ 9%nat 9%bv ltac:(cbv; tauto) (EE 9%nat 9%bv eq_refl))
  | apply (SLOT (-16) _ 8%nat 8%bv ltac:(cbv; tauto) (EE 8%nat 8%bv eq_refl))
  | apply (SLOT (-8) _ 1%nat 1%bv ltac:(cbv; tauto) (EE 1%nat 1%bv eq_refl)) ]; lia. }
(* the lock, as the call finds it *)
assert (LKc : alock_at RG (bxW cx) (ms_mem ms0) false)
  by (apply (rbe_alock_kept (bxW cx) (bxmem cx) (ms_mem ms0) false HLOCK);
      [intros a Ha; apply KR2; lia | exact PR2]).
pose proof LKc as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  aview SEGS (w_H (bxW cx)) (ms_mem ms0) a <> None).
{ intros a Ha. destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply (rbe_view_some _ _ _ 4 _ _ LK0). lia.
  - replace a with (rg_lock RG + 4 + (a - (rg_lock RG + 4))) by lia. apply (rbe_view_some _ _ _ 4 _ _ LK4). lia.
  - replace a with (rg_lock RG + 8 + (a - (rg_lock RG + 8))) by lia. apply (rbe_view_some _ _ _ 4 _ _ LK8). lia. }
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B (bxly cx) (bxS cx) a).
{ intros a Ha. destruct (HG a (ra_lock_in RG a Ha)) as (Hi & Hno & _).
  exact (rbe_not_owned _ _ _ _ _ _ a HAR Hi Hno). }
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0. prreg HS (8%bv : bv 5) QS0. prreg HS (18%bv : bv 5) QS2.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (HSPc : spZ (ms_regs ms0) = spZ (bxregs cx) + -64).
{ unfold spZ at 1. rewrite QSP, Usp. apply unsigned_lit_small. lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3).
  rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). rewrite HV3. reflexivity. }
(* ---- pthread_mutex_lock (&g_lock), over ARx: the call keeps ly S Hp ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (RA_G RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) =>
       val_mem SEGS (mrestrict (w_H (bxW cx)) mem') (rg_lock RG + 4) 4 16)
    (bxW cx) _ _ RA_STK (spZ (bxregs cx)) (ra_FP (bxT cx) (bxes cx))
    (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx) _ _ _ _ _ _ (-64) _ HG eq_refl HJ).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply ra_lock_in. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + exact HLA.
    + lia.
    + unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X.
      rewrite X. vm_compute. reflexivity.
    + reflexivity.
    + exact LK4.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply LKW. lia.
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))). apply ra_lock_in. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HLK3 & HK3 & HPR3).
(* back at 0x82b3c: what the call kept *)
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG <= a < rg_lock RG + 12) ->
  aview SEGS (w_H (bxW cx)) mem3 a = aview SEGS (w_H (bxW cx)) (bxmem cx) a).
{ intros a Ha Hl.
  rewrite (HK3 a ltac:(lia) ltac:(cbv beta; lia) ltac:(unfold ESTACK; lia)). exact (KR2 a Ha). }
assert (PR3 : forall a, apresent (w_H (bxW cx)) (bxmem cx) a -> apresent (w_H (bxW cx)) mem3 a)
  by (intros a Hp; exact (HPR3 a (PR2 a Hp))).
assert (HAR3 : ARx (bxly cx) (bxS cx) (bxHp cx) (bxW cx) mem3 md3)
  by (exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)).
assert (HPK3 : forall (z : Z) (r : bv 5), acallee_saved z -> Z_to_bv 5 z = r ->
  getr regs3 r = getr (ms_regs ms0) r) by (intros z r Hz <-; exact (HP3 z Hz)).
assert (P2 : getr regs3 2 = getr (ms_regs ms0) 2)
  by (apply (HPK3 2 2%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P3 : getr regs3 3 = getr (ms_regs ms0) 3)
  by (apply (HPK3 3 3%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P4 : getr regs3 4 = getr (ms_regs ms0) 4)
  by (apply (HPK3 4 4%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P8 : getr regs3 8 = getr (ms_regs ms0) 8)
  by (apply (HPK3 8 8%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P18 : getr regs3 18 = getr (ms_regs ms0) 18)
  by (apply (HPK3 18 18%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P23 : getr regs3 23 = getr (ms_regs ms0) 23)
  by (apply (HPK3 23 23%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P24 : getr regs3 24 = getr (ms_regs ms0) 24)
  by (apply (HPK3 24 24%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P25 : getr regs3 25 = getr (ms_regs ms0) 25)
  by (apply (HPK3 25 25%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P26 : getr regs3 26 = getr (ms_regs ms0) 26)
  by (apply (HPK3 26 26%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
assert (P27 : getr regs3 27 = getr (ms_regs ms0) 27)
  by (apply (HPK3 27 27%bv ltac:(unfold acallee_saved; lia)); apply bv_eq; reflexivity).
(* ---- the cut RBHR, at the entry's ly / S / Hp, k = 0 ---- *)
apply K. unfold RBHR. exists regs3, mem3, md3.
split; [reflexivity|].
split.
{ unfold bregs_held, bregs_base, bsp0.
  split.
  { split.
    { unfold spZ at 1. rewrite P2. unfold spZ at 1 in HSPc. rewrite HSPc. unfold RA_FRAME. lia. }
    split; [rewrite P3, QGP, (EE 3%nat 3%bv eq_refl); reflexivity|].
    split; [rewrite P4, QTP, (EE 4%nat 4%bv eq_refl); reflexivity|].
    split; [rewrite P23, Q23, (EE 23%nat 23%bv eq_refl); reflexivity|].
    split; [rewrite P24, Q24, (EE 24%nat 24%bv eq_refl); reflexivity|].
    split; [rewrite P25, Q25, (EE 25%nat 25%bv eq_refl); reflexivity|].
    split; [rewrite P26, Q26, (EE 26%nat 26%bv eq_refl); reflexivity|].
    rewrite P27, Q27, (EE 27%nat 27%bv eq_refl); reflexivity. }
  split; [rewrite P8, QS0, (EE 10%nat 10%bv eq_refl), H10; reflexivity|].
  rewrite P18, QS2, E32. reflexivity. }
split; [exact Hpos|].
split.
{ unfold BLIVER, bsp0, bFP.
  split; [exact HJ3|].
  split.
  { (* .rodata: every ROM byte is an image byte (below alloc_ceiling) off the lock word (HNROM), so kept *)
    intros a Ha.
    assert (HaI : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range a HaI) as HaR.
    rewrite (KLOW a ltac:(lia) ltac:(intros Hl; exact (HNROM a (ra_lock_in RG a Hl) Ha))).
    exact (HROM a Ha). }
  split; [intros a _ _ _ Hp; exact (PR3 a Hp)|].
  split.
  { unfold rb_saved, bsp0. intros i Hi. unfold arm.
    apply (rbe_vm_kept (w_H (bxW cx)) (w_H (bxW cx)) (ms_mem ms0) mem3); [exact (SAVED0 i Hi)|].
    intros b Hb. apply HK3; unfold RA_FRAME, ESTACK in *; cbn in Hb; lia. }
  split.
  { split.
    { apply (rbe_vm_kept (w_H (bxW cx)) (w_H (bxW cx)) (ms_mem ms0) mem3); [exact LK0|].
      intros b Hb. apply HK3; cbn in Hb; unfold ESTACK in *; lia. }
    split; [exact HLK3|].
    split.
    { apply (rbe_vm_kept (w_H (bxW cx)) (w_H (bxW cx)) (ms_mem ms0) mem3); [exact LK8|].
      intros b Hb. apply HK3; cbn in Hb; unfold ESTACK in *; lia. }
    intros i Hi. apply (rbe_wkept (bxW cx) (ms_mem ms0) mem3);
    [exact (HPR3 (rg_lock RG + i)) | unfold arm; apply LKW; lia]. }
  split.
  { unfold awake_at in HWAKE |- *. unfold arm in HWAKE |- *.
    apply (rbe_vm_kept (w_H (bxW cx)) (w_H (bxW cx)) (bxmem cx) mem3); [exact HWAKE|].
    intros b Hb. cbn in Hb.
    pose proof (HWK b ltac:(lia)) as (HbI & _). pose proof (pa_img_range b HbI) as HbR.
    ra_pick HRGP 2%nat 6%nat D26. apply KLOW; lia. }
  split; [reflexivity|].
  (* errno: the runs wrote only the frame, the lock call only the lock word and its scratch below the frame *)
  intros i Hi. apply KLOW; [pose proof (EL i Hi); lia | exact (ENL i Hi)]. }
apply (rbe_rel_kept (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) mem3 md3 (bxT cx) (bxes cx)
  HAR3 HREL KLOW PR3).
Qed.
End cR.
(* the strict segment is its R twin at R := wle (route R's rule: one walk text) *)
Theorem pb_rb_ent_x : rb_ent_stmt B PST ARx MT RP G RG CTX.
Proof.
eapply (pb_rb_ent_xR (@wle SEGS));
  first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Qed.
End c.
End b.
End a.
