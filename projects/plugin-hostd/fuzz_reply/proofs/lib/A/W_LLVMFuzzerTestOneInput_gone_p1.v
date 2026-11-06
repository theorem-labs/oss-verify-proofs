(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, PHASE 1
   (lib/A/W_LLVMFuzzerTestOneInput_gone.v's GP1): the join 0x846f0 to the reads[] loop's head 0x84738
   (fuzz_reply.asan 0x846f0-0x84734, fuzz_reply.c:635-639).  The six shadow bytes of `char prefix[48]` (the fake
   frame's +32) go from 0xf8 to 0 and `size_t at = 0` is stored at F+208 (one plain run: it writes the fake frame's
   shadow, which the token run refuses); then `snprintf(prefix, 48, "%s %d ", PHD_EVENT_PARAM_GESTURE, id)`
   (W_sites.v asnprintf_realizes, lifted into the arm's journal by W_sites.v aj_gx_entry_at); then
   `li a2,0; li t0,4; addi t1,s1,192`.  The stack premise of the call is discharged here: aj_gx_entry_at checks
   3 * ESTACK - (F - sp0) <= LLVMF_STK (12,288 + at most 352 <= 32,768) and hands back the scratch's presence from
   the journal (ascratch_ok), which ecall_pre_stk_of turns into the contract's ecall_pre_stk. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require SnpNarrowSites.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a register of a symbolic state after a run, its value left as the symbolic expression *)
Ltac p1_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* membership in a concrete list *)
Ltac p1_in := repeat (first [left; reflexivity | right]).
(* a concrete register is callee-saved *)
Ltac p1_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* fuzz_reply.asan's globals, as numbers *)
Ltac p1_rg := cbn [fst snd fr_RG fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max
  rg_send_eintr rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.

Section gp1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---- this phase's Section hypotheses ---- *)
(* the allocator instance (W_kit.v): errno's 4 bytes lie in the image (pal_env, Reusable/YCbq.v api_env) *)
Hypothesis TL : PALib B.
(* snprintf at the interceptor's entry: W_sites.v:305's contract, at the image's two stack-protector cells *)
Hypothesis SNP : asnprintf_realizes B (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
(* INSTANCE FACT, W6's text verbatim (lib/A/W_relay_instance_gone_cx.v on 6a1bcf9f403, :201-217).  The GOT word
   FR_GOT_GUARD = 0x9e658 holds &__stack_chk_guard = FR_GUARD in every AR state: on image A it is one of the
   instance's pinned const cells (AF0m Tfib_const_abs `z8 (ANum 0x9e658) 0x5f94b0`), which AR holds (YG0n.v
   am_const).  It cannot be carried from the entry state through the journal instead (the base's GN_GUARD form):
   the journal keeps an image byte only outside as_owned_static, and 0x9e658 is an owned static (AF0m
   Tfib_owned_static `(0x9e658, 8)`).  B is a Section variable here, so as_const B is not computable.  The canary
   cell FR_GUARD needs no hypothesis: the image holds bytes there (seg_rom is Some 0 on [0x5f94b0, +8)), so every
   memory shows them. *)
Hypothesis HGOTG : forall ly S W mem md, AR segs B ly S W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* INSTANCE FACT.  The shadow checks snprintf makes of its two .rodata strings pass in every AR state: the format
   .str.8 "%s %d " (A_OBJ 20, 0x20f80, 7 bytes with the NUL) and the argument .str.5 "param_gesture" (A_OBJ 21,
   0x20f20, 14 bytes).  Their shadow is not zero (the strings end inside a granule: the shadow bytes are the partial
   values 7 and 6, AF0m Tfib_const_shadow 0x7fffc1f0 / 0x7fffc1e5), so `azs` does not give this; on image A the
   granules of both hulls are AF0m const cells or zero-shadow ranges, which AR holds (am_const, am_zshadow). *)
Hypothesis GN_LITS : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14.

(* ================================================================== the printf text *)
Definition p1_fmt : list Z := [37; 115; 32; 37; 100; 32].      (* "%s %d " *)
Definition p1_ps : list printf_facts_c.pf_piece :=
  [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32].
Lemma p1_dec_ok : forall id, 0 <= id < 256 ->
  (1 <= length (printf_facts_c.pf_dec id) <= 3)%nat /\
  Forall (fun c => 48 <= c <= 57) (printf_facts_c.pf_dec id).
Proof.
  intros id Hid.
  assert (K : forallb (fun v => ((1 <=? length (printf_facts_c.pf_dec v))%nat
      && (length (printf_facts_c.pf_dec v) <=? 3)%nat
      && forallb (fun c => (48 <=? c) && (c <=? 57)) (printf_facts_c.pf_dec v))%bool)
    (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K.
  specialize (K id ltac:(apply in_map_iff; exists (Z.to_nat id); split; [lia | apply in_seq; lia])).
  apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
  apply Nat.leb_le in K1. apply Nat.leb_le in K2.
  split; [lia|]. rewrite Forall_forall. rewrite forallb_forall in K3. intros c Hc.
  specialize (K3 c Hc). apply andb_prop in K3 as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.
Lemma p1_kg : Forall (fun c => 0 < c < 256) K_GESTURE /\ length K_GESTURE = 13%nat.
Proof.
  split; [|reflexivity]. apply Forall_forall. intros c Hc. vm_compute in Hc.
  repeat (destruct Hc as [<- | Hc]; [lia|]). destruct Hc.
Qed.
Lemma p1_text_ok : forall id, 0 <= id < 256 ->
  printf_facts_c.pf_text p1_ps [printf_facts_c.APtr K_GESTURE; printf_facts_c.AInt id]
    = Some (relay_instance_gone_b_c.instance_prefix id) /\
  (16 <= length (relay_instance_gone_b_c.instance_prefix id) <= 18)%nat /\
  Forall (fun c => 0 < c < 256) (relay_instance_gone_b_c.instance_prefix id).
Proof.
  intros id Hid. destruct (p1_dec_ok id Hid) as [L D]. destruct p1_kg as [KG KL].
  split; [reflexivity|]. unfold relay_instance_gone_b_c.instance_prefix.
  split; [rewrite !length_app, KL; cbn [length]; lia|].
  apply Forall_app. split; [exact KG|]. apply Forall_cons; [lia|]. apply Forall_app. split.
  - eapply Forall_impl; [|exact D]. intros c Hc. cbv beta in Hc |- *. lia.
  - apply Forall_cons; [lia | apply Forall_nil].
Qed.
Lemma p1_nz : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l Hl Hin. apply in_map_iff in Hin as (x & Hx & Hxl). rewrite Forall_forall in Hl.
  pose proof (Hl x Hxl) as Hr. apply (f_equal bv_unsigned) in Hx. rewrite !Z_to_bv_unsigned in Hx.
  unfold bv_wrap in Hx. change (bv_modulus 8) with 256 in Hx. rewrite !Z.mod_small in Hx by lia. lia.
Qed.

(* ================================================================== memory views *)
Lemma p1_vis_seg : forall H (m : word -> option byte) a b,
  seg_rom segs (Z_to_bv 64 a) = Some b -> aview segs H m a <> None.
Proof.
  intros H m a b Hs. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)); [discriminate|].
  rewrite Hs. discriminate.
Qed.
Definition p1_segb (lo n : Z) : bool :=
  forallb (fun i => match seg_rom segs (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat n)).
Lemma p1_vis_rng : forall H (m : word -> option byte) lo n, p1_segb lo n = true ->
  forall a, lo <= a < lo + n -> aview segs H m a <> None.
Proof.
  intros H m lo n Hb a Ha. unfold p1_segb in Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (lo + (a - lo)) with a in Hb by lia.
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Hs; [|discriminate]. exact (p1_vis_seg H m a b Hs).
Qed.
Lemma p1_vis_pres : forall H (m : word -> option byte) a, apresent H m a -> aview segs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma p1_rdword_some : forall (rd : reader) a, (forall i, 0 <= i < 8 -> rd (a + i) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
  intros rd a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
  pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
  pose proof (H 7 ltac:(lia)) as H7.
  destruct (rd a); [|congruence]. destruct (rd (a + 1)); [|congruence]. destruct (rd (a + 2)); [|congruence].
  destruct (rd (a + 3)); [|congruence]. destruct (rd (a + 4)); [|congruence]. destruct (rd (a + 5)); [|congruence].
  destruct (rd (a + 6)); [|congruence]. destruct (rd (a + 7)); [|congruence]. eexists. reflexivity.
Qed.
Definition p1_romb (lo n : Z) : bool :=
  match find_segment segs lo n with Some sg => negb (seg_writable sg) | None => false end.
Lemma p1_in_rom : forall lo n a, p1_romb lo n = true -> lo <= a < lo + n -> in_rom segs a.
Proof.
  intros lo n a Hb Ha. unfold p1_romb in Hb. destruct (find_segment segs lo n) as [sg|] eqn:Hf; [|discriminate].
  destruct (find_segment_hit segs lo n sg Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin|].
  split; [destruct (seg_writable sg); [discriminate | reflexivity] | lia].
Qed.
Definition p1_bytesb (f : Z) (l : list byte) : bool :=
  forallb (fun i => match seg_rom segs (Z_to_bv 64 (f + Z.of_nat i)) with
                    | Some b => bv_unsigned b =? bv_unsigned (nth i l (Z_to_bv 8 0)) | None => false end)
    (seq 0 (length l)).
Lemma p1_abytes : forall (W : world segs) mem f (l : list byte), rom_view segs W mem ->
  p1_romb f (Z.of_nat (length l)) = true -> p1_bytesb f l = true -> abytes_at W mem f l.
Proof.
  intros W mem f l HR Hr Hb i Hi.
  rewrite (HR (f + Z.of_nat i) (p1_in_rom f (Z.of_nat (length l)) (f + Z.of_nat i) Hr ltac:(lia))).
  unfold p1_bytesb in Hb. rewrite forallb_forall in Hb. specialize (Hb i ltac:(apply in_seq; lia)).
  destruct (seg_rom segs (Z_to_bv 64 (f + Z.of_nat i))) as [b|]; [|discriminate].
  apply Z.eqb_eq in Hb. cbn [option_map]. rewrite Hb. reflexivity.
Qed.
Lemma p1_vm1_of_aview : forall H (m : word -> option byte) a, aview segs H m a = Some 0 ->
  val_mem segs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hz j Hj. assert (Ej : j = 0%nat) by lia. subst j. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  destruct (aview_byte segs H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal.
  apply bv_eq. rewrite <- Hv. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma p1_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma p1_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma p1_sv_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* the fake frame's shadow once prefix[48]'s six granules are unpoisoned *)
Lemma p1_shadow_open : forall (m m' : word -> option byte) s,
  garr8 segs m s fake_shadow ->
  (forall j, (j < 4 \/ 10 <= j < 16)%nat -> forall v, val_mem segs m (s + Z.of_nat j) 1 v ->
     val_mem segs m' (s + Z.of_nat j) 1 v) ->
  (forall j, (4 <= j < 10)%nat -> val_mem segs m' (s + Z.of_nat j) 1 0) ->
  garr8 segs m' s fake_shadow_open.
Proof.
  intros m m' s Hg Hk Hz j Hj. cbn [length fake_shadow_open] in Hj.
  assert (Hc : (j < 4 \/ 10 <= j < 16)%nat \/ (4 <= j < 10)%nat) by lia.
  destruct Hc as [Hc | Hc].
  - destruct (Hg j ltac:(cbn [length fake_shadow]; lia)) as [Hv Hr].
    assert (E : nth j fake_shadow_open 0 = nth j fake_shadow 0)
      by (do 16 (destruct j as [|j]; [first [reflexivity | lia] |]); lia).
    rewrite E. split; [exact (Hk j Hc _ Hv) | exact Hr].
  - assert (E : nth j fake_shadow_open 0 = 0)
      by (do 16 (destruct j as [|j]; [first [reflexivity | lia] |]); lia).
    rewrite E. split; [exact (Hz j Hc) | lia].
Qed.

(* ================================================================== the model's bytes, kept
   The kit of W_LLVMFuzzerTestOneInput_latch.v (lt_alist .. lt_amodel_kept), with "below alloc_ceiling + 8"
   sharpened to "in the image or in a live block": this phase writes the fake frame (prefix[48]) and its shadow,
   which lie below alloc_ceiling but in neither. *)
Definition p1_ib (ly : alayout) (S : astate) (a : Z) : Prop :=
  (0x10000 <= a < 0x5fb000) \/ (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n).
Definition p1_fp (ly : alayout) (S : astate) (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> p1_ib ly S a.
Lemma p1_fp_nil : forall ly S, p1_fp ly S [].
Proof. intros ly S r []. Qed.
Lemma p1_fp_cons : forall ly S r fp, (forall a, fst r <= a < snd r -> p1_ib ly S a) -> p1_fp ly S fp ->
  p1_fp ly S (r :: fp).
Proof. intros ly S r fp H1 H2 r' [<- | Hr] a Ha; [exact (H1 a Ha) | exact (H2 r' Hr a Ha)]. Qed.
Lemma p1_fp_app : forall ly S f1 f2, p1_fp ly S f1 -> p1_fp ly S f2 -> p1_fp ly S (f1 ++ f2).
Proof. intros ly S f1 f2 H1 H2 r Hr. apply in_app_or in Hr as [Hr|Hr]; [exact (H1 r Hr) | exact (H2 r Hr)]. Qed.
Lemma p1_ib_img : forall ly S lo hi, 0x10000 <= lo -> hi <= 0x5fb000 -> forall a, lo <= a < hi -> p1_ib ly S a.
Proof. intros ly S lo hi H1 H2 a Ha. left. lia. Qed.
Lemma p1_ib_blk : forall ly S b n lo hi, In (b, n) (ablocks B ly S) -> b <= lo -> hi <= b + req_size n ->
  forall a, lo <= a < hi -> p1_ib ly S a.
Proof. intros ly S b n lo hi Hin H1 H2 a Ha. right. exists b, n. split; [exact Hin | lia]. Qed.
Lemma p1_akept : forall ly S (W W' : world segs) mem mem' fp,
  (forall a, p1_ib ly S a -> abyte_kept W mem W' mem' a) -> p1_fp ly S fp -> akept W mem W' mem' fp.
Proof. intros ly S W W' mem mem' fp HK Hf r Hr a Ha. exact (HK a (Hf r Hr a Ha)). Qed.
Lemma p1_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma p1_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma p1_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma p1_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, p1_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma p1_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
Lemma p1_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0x10000 <= LA -> LA + 16 <= 0x5fb000 ->
  p1_fp ly S (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  rewrite Forall_forall in H9.
  assert (HREC : p1_fp ly S (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))).
  { intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). destruct (H9 x Hx) as (K1 & _).
    destruct (p1_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
    apply (p1_ib_blk ly S _ _ _ _ K1); cbn [gfp fst snd]; [lia|].
    rewrite p1_bzs_len, length_app. cbn [length]. lia. }
  split.
  - unfold alist_fp. apply p1_fp_cons; [apply p1_ib_img; cbn [fst snd]; lia|].
    apply p1_fp_app; [|exact HREC].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply p1_fp_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (p1_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply p1_fp_cons; [|apply p1_fp_nil].
    apply (p1_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
    rewrite p1_bzs_len, length_app, p1_concat_len. unfold hl_n in *. unfold AREC in *. lia.
  - intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
      destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)).
Qed.
Lemma p1_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0x10000 <= HA -> HA + ASRC <= 0x5fb000 ->
  p1_fp ly S (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (p1_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (p1_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (p1_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (p1_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply p1_fp_cons; [apply p1_ib_img; cbn [fst snd]; unfold ASRC in *; lia|].
    apply p1_fp_cons.
    + apply (p1_ib_blk ly S _ _ _ _ Hpb); cbn [gfp fst snd]; [lia|].
      rewrite p1_bzs_len, Hpj. lia.
    + apply p1_fp_app; [exact A1|]. apply p1_fp_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
Lemma p1_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  p1_fp ly S (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  rewrite Forall_forall in K15.
  assert (HK : p1_fp ly S (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))).
  { intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). destruct (K15 k Hk) as (M1 & _).
    destruct (p1_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
    apply (p1_ib_blk ly S _ _ _ _ M1); cbn [gfp fst snd]; [lia|].
    rewrite p1_bzs_len, length_app. cbn [length]. lia. }
  unfold aentry_fp, aentry_blks. split.
  - apply p1_fp_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply p1_fp_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (p1_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply p1_fp_cons; [|apply p1_fp_nil].
      apply (p1_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
      rewrite p1_bzs_len, length_app. lia.
    + apply p1_fp_cons; [|exact HK].
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * intros a Ha. cbn [gfp fst snd] in Ha. rewrite p1_bzs_len, p1_key_ptrs_len, Hks in Ha.
        cbn [length] in Ha. lia.
      * destruct (p1_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        apply (p1_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
        rewrite p1_bzs_len, p1_key_ptrs_len. unfold re_nheld in Hk1. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|apply in_map_iff in Hb as (k & <- & Hk); exact (proj1 (K15 k Hk))].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma p1_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  p1_fp ly S (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (p1_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  rewrite Forall_forall in R10.
  assert (HE1 : p1_fp ly S (concat (map aentry_fp es))).
  { intros r Hr. apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    exact (proj1 (p1_aentry ly S W mem md e HAR (R10 e He)) r Hr). }
  assert (HE2 : forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S)).
  { intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
    exact (proj2 (p1_aentry ly S W mem md e HAR (R10 e He)) b Hb). }
  unfold arelay_fp, arelay_blks. split.
  - apply p1_fp_cons; [apply p1_ib_img; p1_rg; lia|].
    apply p1_fp_cons; [apply p1_ib_img; p1_rg; lia|].
    apply p1_fp_cons; [apply p1_ib_img; p1_rg; lia|].
    apply p1_fp_cons; [|exact HE1].
    apply (p1_ib_blk ly S _ _ _ _ R8); cbn [fst snd]; lia.
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.
Lemma p1_errno : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000.
Proof.
  pose proof (pal_env B TL) as ((HE0 & HE1) & HEI & _).
  pose proof (pa_img_range (as_errno B) (HEI (as_errno B) ltac:(lia))) as X0.
  pose proof (pa_img_range (as_errno B + 3) (HEI (as_errno B + 3) ltac:(lia))) as X3. lia.
Qed.
Lemma p1_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  p1_fp ly S (aout_fp B fr_RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  pose proof p1_errno as HER.
  unfold aout_fp, aout_blks. split.
  - do 8 (apply p1_fp_cons; [apply p1_ib_img; p1_rg; lia|]).
    apply p1_fp_cons; [apply p1_ib_img; cbn [fst snd]; lia|].
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply p1_fp_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (p1_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply p1_fp_cons; [|apply p1_fp_nil]. apply (p1_ib_blk ly S _ _ _ _ Hin); cbn [fst snd]; lia.
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma p1_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  (forall a, p1_ib ly S a -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KEEP.
  assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W mem W' mem' x)
    by (intros x Hx; apply KEEP; left; exact Hx).
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0x10000 <= rg_s fr_RG + ASRC * Z.of_nat i) by (p1_rg; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= 0x5fb000) by (p1_rg; unfold ASRC; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (p1_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (p1_akept ly S W W' mem mem' _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply KI. unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KI. unfold ASRC in *. lia. }
  split.
  { destruct (p1_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3 (p1_akept ly S W W' mem mem' _ KEEP F1) F2). }
  split.
  { destruct (p1_aout ly S W mem md _ _ _ _ _ _ HAR M4) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4 (p1_akept ly S W W' mem mem' _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] x Hx. apply KI. p1_rg. lia. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] x Hx. apply KI. p1_rg. lia. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] x Hx. apply KI. p1_rg. lia. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KI. unfold AG_NFD in *. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KI. unfold AG_NFD in *. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KI. unfold AG_THREAD_UP in *. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KI. unfold AG_LISTEN in *. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KI. unfold AG_LISTEN in *. lia.
Qed.
Lemma p1_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, p1_ib ly S a -> abyte_kept W mem W' mem' a) -> ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (p1_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  apply KEEP. right. exists (c_p cx), (c_n cx). split; [exact Hin | lia].
Qed.

(* ================================================================== the two symbolic states *)
(* 0x846f0: the six shadow bytes of prefix[48] (s8 = x24 = SB + FF / 8, bytes 4..9) and the frame cell F+208
   (s1 = x9 = F) are written; nothing is read *)
Definition p1_regs : smem :=
  [ YP09.mkRegion (Some 24%nat) 0 16 4 10 [];
    YP09.mkRegion (Some 9%nat) 208 216 208 216 [] ].
Definition p1_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF (SB + 512) (SB + 17592186044416) 2)] [] [].
Definition ss_p1 : sstate := mkSS AF_gn_join sr_atoms p1_regs None p1_facts.
(* 0x8472c, back from snprintf: `li a2,0; li t0,4; addi t1,s1,192`, no memory *)
Definition AF_p1_ret : Z := 0x2440.
Definition ss_p1b : sstate := mkSS AF_p1_ret sr_atoms [] None (mkFacts [] [] []).

(* ================================================================== the phase *)
Lemma gp1_join_l1 : forall cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GJN B G_fr fr_FP LS RINV cx t m W c ->
  SRr segs W c (GL1 B G_fr fr_FP LS RINV cx t m 0%nat).
Proof.
  intros cx t m W c HB HJN.
  destruct HJN as (regs & mem & md & ly & S & kk & fpos & -> & HC & HMOD & HSEP & HLS & HRI & HOP & HKR & R20 & R21).
  destruct HC as (HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  assert (Hlen : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf in HPRE0.
    destruct HPRE0 as (_ & _ & _ & _ & _ & Hn & _). lia. }
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (FF := frame_addr ly 1 fpos) in *.
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (al_frames _ _ LAWS ly S W mem md 1 fpos HAR Hfin) as (_ & _ & HFpres & _).
  change (fs_frame_bytes 1) with 128 in HFpres. fold FF in HFpres.
  pose proof (frm_off_imgP B ly S W mem md 1 fpos HAR Hfin) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frame_al64 segs B ly S W mem md 1 fpos HAR Hfin) as (HF64 & _ & _). fold FF in HF64.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFFq : FF = 64 * (FF / 64)) by (pose proof (Z.div_mod FF 64 ltac:(lia)); lia).
  assert (HFF8 : FF / 8 = 8 * (FF / 64))
    by (rewrite HFFq at 1; replace (64 * (FF / 64)) with (8 * (FF / 64) * 8) by lia; rewrite Z.div_mul by lia;
        reflexivity).
  assert (HFFe : FF = 8 * (FF / 8)) by lia.
  pose proof HFR as (GSV & GAW & G24 & G48 & G56 & G64 & G72 & G80 & G88 & G96 & G184 & G32 & G104 & G112 & G120 &
                     G128 & G136 & G152 & GF0 & GF8 & GF16 & GAWF & GSH & GAWS).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  (* ---- the entry state at 0x846f0 ---- *)
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (EI : forall n, (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n))
    by (intros n Hn; subst E; apply Eimg_img; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = SB + FF / 8)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SB; lia).
  assert (HS : st_ok_pi segs VAL E ss_p1
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_join)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_p1. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold p1_regs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U24. split; [unfold SB; lia|]. split; [unfold SB; lia|].
        split; [intros o Ho; exact (GAWS o ltac:(lia)) | constructor].
      + rewrite U9. split; [lia|]. split; [lia|].
        split; [intros o Ho; exact (GAW o ltac:(lia)) | constructor].
    - apply pairwise_disjoint_of_extents. unfold p1_regs, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [p1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U24. change (2 ^ 5) with 32. change (2 ^ 2) with 4. unfold SB.
      repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_join)) with (Z_to_bv 64 (BASE + AF_gn_join)).
  pose (RUNP := SRr_run_pi_AJX0 B LAWS G_fr).
  pose (RUNC := SRr_run_pi_AJX0_call B LAWS G_fr).
  pose (RUNTOP := SRr_run_to_pi_AJX0 (PL := PL_fr) (PI := PB_fr) B LAWS G_fr).
  (* ---- 0x846f0-0x84728: the unpoison, at = 0, snprintf's arguments; a plain run, it writes the fake frame's
     shadow; it stops at the jal ---- *)
  paj_run_shc RUNP RUNC HS HJ.
  { intros a (r & Hin & Hr). cbn [ss_mem ss_p1 p1_regs In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U24, ?U9 in Hr.
    - right; right; right. exists 1, fpos. split; [left; reflexivity|]. right.
      unfold in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      fold FF. lia.
    - left. rewrite WS. lia. }
  rename ms into msT. rename mat into matT.
  pmkst HS.
  p1_reg HS (1%bv : bv 5) Q1. p1_reg HS (2%bv : bv 5) Q2. p1_reg HS (3%bv : bv 5) Q3. p1_reg HS (4%bv : bv 5) Q4.
  p1_reg HS (10%bv : bv 5) Q10. p1_reg HS (11%bv : bv 5) Q11. p1_reg HS (12%bv : bv 5) Q12. p1_reg HS (13%bv : bv 5) Q13. p1_reg HS (14%bv : bv 5) Q14.
  cbn [sv_denot] in Q1. rewrite (img_env_codeptr E HEI 9280) in Q1.
  rewrite p1_sv_off0, (EE 2%nat 2%bv eq_refl), R2 in Q2.
  rewrite p1_sv_off0, (EE 3%nat 3%bv eq_refl), R3 in Q3.
  rewrite p1_sv_off0, (EE 4%nat 4%bv eq_refl), R4 in Q4.
  rewrite p1_sv_off0, (EE 19%nat 19%bv eq_refl), R19 in Q10.
  rewrite p1_sv_off0, (EI 261%nat ltac:(cbv; lia)) in Q12.
  rewrite p1_sv_off0, (EI 262%nat ltac:(cbv; lia)) in Q13.
  rewrite p1_sv_off0, (EE 21%nat 21%bv eq_refl), R21 in Q14.
  pose proof (regs_kept_of_st_ok segs E _ _ regs [] CALLEE_SAVED HS HAE ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as RG0.
  pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RG1.
  cbn [ms_mem restrict] in RG0, RG1.
  assert (ZS : forall j, 4 <= j < 10 -> aview segs (w_H W) (ms_mem msT) (SB + FF / 8 + j) = Some 0).
  { intros j Hj. apply (aview_of_val_mem1 segs (w_H W) (ms_mem msT) _ 0); [|lia].
    assert (Hc : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (apply (field_of_region E _ 24%nat (SB + FF / 8) _ _ _ _ _ _ 1%N (SLit 0) 0 RG0);
       [exact U24 | p1_in | reflexivity | zside | zside]). }
  assert (Z208 : val_mem segs (mrestrict (w_H W) (ms_mem msT)) (F + 208) 8 0).
  { apply (field_of_region E _ 9%nat F _ _ _ _ _ 208 8%N (SLit 0) 0 RG1); [exact U9 | p1_in | reflexivity | zside | zside]. }
  assert (KV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + FF / 8 + 4 <= a < SB + FF / 8 + 10) -> ~ (F + 208 <= a < F + 216) ->
      aview segs (w_H W) (ms_mem msT) a = aview segs (w_H W) mem a).
  { intros a Ha N1 N2. apply (aview_kept_out E _ (w_H W) mem (ms_mem msT) HFr a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_p1 p1_regs In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U24, ?U9 in Hr;
      lia. }
  assert (KP1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msT) a)
    by (intros a Hp; exact (p1_pres_grows W _ _ a HG0 Hp)).
  clear HF HFr HG0.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
  assert (HRVT : rom_view segs W (ms_mem msT)).
  { intros a Ha. assert (Hi : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
    pose proof (pa_img_range a Hi) as Hr. rewrite (KV1 a ltac:(lia)); [exact (HRV a Ha) | unfold SB in *; lia | lia]. }
  (* ---- snprintf (prefix, 48, "%s %d ", "param_gesture", id) ---- *)
  set (id := gn_id cx m) in *.
  assert (Hid : 0 <= id < 256).
  { unfold id, gn_id. destruct (gn_more cx m); [|lia]. unfold in_byte.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (lm_k m + 1)) (c_pl cx) (Z_to_bv 8 0))) as Hr.
    change (bv_modulus 8) with 256 in Hr. lia. }
  set (T := relay_instance_gone_b_c.instance_prefix id).
  destruct (p1_text_ok id Hid) as (HTX & HTL & HTF). fold T in HTX, HTL, HTF.
  assert (HT47 : firstn (Z.to_nat (48 - 1)) T = T) by (apply firstn_all2; lia).
  assert (Hosp : spZ (ms_regs msT) = sp0 + (F - sp0)).
  { unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Ho16 : (F - sp0) mod 16 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HF32 in D1. rewrite Hal in D2.
    replace (F - sp0) with ((2 * (F / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
  assert (V20 : VAL (A_OBJ 20) = 135040) by (vm_compute; reflexivity).
  assert (V21 : VAL (A_OBJ 21) = 134944) by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS G_fr 0 [] (3 * ESTACK) (SIGMA WS_snprintf)
      (fun a => FF + 32 <= a < FF + 32 + 48)
      (fun (regs' : bvmap 5 word) (mem' : word -> option byte) => getr regs' 10 = w64 (Z.of_nat (length T)) /\
         abytes_at W mem' (FF + 32) (printf_facts_c.pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])))
      W (ms_regs msT) (ms_mem msT) LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly S _ kk (F - sp0) (Z_to_bv 64 (BASE + 9280)) HG eq_refl HJ).
    - exact Hosp.
    - exact Ho16.
    - lia.
    - rewrite Hes. lia.
    - rewrite WS, Hes. lia.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a. destruct (Z_lt_le_dec a (FF + 32)); [right; lia|].
      destruct (Z_lt_le_dec a (FF + 32 + 48)); [left; lia | right; lia].
    - intros a Ha HGa. exfalso. destruct (HG a HGa) as [Hi _]. pose proof (pa_img_range a Hi). lia.
    - intros a Ha _. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - intros HPRE HSC.
      eapply SRr_mono.
      { apply (SNP ly S W (ms_regs msT) (ms_mem msT) _ (FF + 32) 48 (VAL (A_OBJ 20)) p1_fmt p1_ps
          [printf_facts_c.APtr K_GESTURE; printf_facts_c.AInt id] T).
        - (* the stack-protector cells *)
          split.
          + exact (HGOTG ly S W (ms_mem msT) _ HART).
          + apply p1_rdword_some. intros i Hi.
            apply (p1_vis_rng _ _ FR_GUARD 8 ltac:(vm_compute; reflexivity)). lia.
        - (* the stack: 3 * ESTACK = 12,288 bytes of present scratch below sp = F, from the journal *)
          exact (ecall_pre_stk_of B (3 * ESTACK) ly S W (ms_regs msT) (ms_mem msT) _ HPRE HSC).
        - exact Q10.
        - rewrite Q11. reflexivity.
        - rewrite Q12. reflexivity.
        - lia.
        - lia.
        - rewrite V20. lia.
        - split; [apply (p1_abytes W _ _ _ HRVT); vm_compute; reflexivity|].
          apply p1_nz. unfold p1_fmt. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
        - reflexivity.
        - (* the narrowing (W_sites.v asnprintf_realizes): reply's four pieces; the format and "param_gesture" below
             the GOT word, prefix[48] above the image (SnpNarrowSites.v san_M1 / san_M3 / san_M2_AR) *)
          reflexivity.
        - exact (proj1 (SnpNarrowSites.san_M1 p1_fmt eq_refl)).
        - exact (proj2 (SnpNarrowSites.san_M1 p1_fmt eq_refl)).
        - intros s Hs. apply (SnpNarrowSites.san_M3 (getr (ms_regs msT) 13) id s); [|exact Hs].
          rewrite Q13. change 262%nat with (A_OBJ 21). rewrite V21. apply unsigned_lit_small. lia.
        - exact (SnpNarrowSites.san_M2_AR B ly S W (ms_mem msT) _ fpos HART Hfin).
        - exact HTX.
        - lia.
        - destruct (GN_LITS ly S W (ms_mem msT) _ HART) as (LA1 & LV1 & _ & _).
          change (Z.of_nat (length p1_fmt) + 1) with 7. rewrite V20 in LA1, LV1 |- *.
          split; [lia|]. split; [lia|]. split; [lia|].
          split; [intros a Ha; split;
            [apply (p1_vis_rng _ _ 135040 8 ltac:(vm_compute; reflexivity)); lia
            | unfold ascratch_stk; rewrite Hosp; lia]|].
          split; [left; lia|]. split; [exact LA1 | intros _; exact LV1].
        - intros a Ha. rewrite V20 in Ha. change (Z.of_nat (length p1_fmt)) with 6 in Ha.
          apply (p1_vis_rng _ _ 135040 8 ltac:(vm_compute; reflexivity)). lia.
        - destruct (GN_LITS ly S W (ms_mem msT) _ HART) as (_ & _ & LA2 & LV2).
          rewrite V21 in LA2, LV2.
          assert (U13 : bv_unsigned (getr (ms_regs msT) 13) = 134944).
          { rewrite Q13. change 262%nat with (A_OBJ 21). rewrite V21. apply unsigned_lit_small. lia. }
          cbn [apf_args_ok apf_arg_ok]. rewrite U13. destruct p1_kg as [KG KL]. rewrite KL.
          split; [|split; [|exact I]].
          + split; [exact KG|]. split; [lia|].
            split; [split; [apply (p1_abytes W _ _ _ HRVT); vm_compute; reflexivity | apply p1_nz; exact KG]|].
            split.
            { change (Z.of_nat 13 + 1) with 14.
              split; [lia|]. split; [lia|]. split; [lia|].
              split; [intros a Ha; split;
                [apply (p1_vis_rng _ _ 134944 16 ltac:(vm_compute; reflexivity)); lia
                | unfold ascratch_stk; rewrite Hosp; lia]|].
              split; [left; lia|]. split; [exact LA2 | intros _; exact LV2]. }
            split.
            { intros a Ha. change (Z.of_nat 13) with 13 in Ha.
              apply (p1_vis_rng _ _ 134944 16 ltac:(vm_compute; reflexivity)). lia. }
            change (Z.of_nat 13) with 13. lia.
          + split; [lia|]. rewrite Q14. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
        - (* the destination: prefix[48], the fake frame's own bytes; addressable from the shadow just written *)
          destruct (al_frames _ _ LAWS ly S W (ms_mem msT) _ 1 fpos HART Hfin) as (_ & _ & HFp2 & _).
          change (fs_frame_bytes 1) with 128 in HFp2. fold FF in HFp2.
          split; [lia|]. split; [lia|]. split; [lia|].
          split; [intros a Ha; destruct (HFp2 a ltac:(lia)) as [Hp Hno];
                  split; [exact (apresent_writable segs _ _ _ Hp)
                         | split; [exact Hno | unfold ascratch_stk; rewrite Hosp; lia]]|].
          split; [exact (amem_range_sub_app FF 128 (FF + 32) 48 HFFapp HFFc ltac:(lia) ltac:(lia) ltac:(lia))|].
          split.
          + intros x Hx. exists 0. split; [|left; reflexivity].
            unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
            assert (Hq : FF / 8 + 4 <= x / 8 < FF / 8 + 10).
            { pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
            replace (SB + x / 8) with (SB + FF / 8 + (x / 8 - FF / 8)) by lia. apply ZS. lia.
          + intros _. exact (shadow_hull_vis_of_frame segs B LAWS ly S W (ms_mem msT) _ 1 fpos (FF + 32) 48 HART Hfin
              ltac:(fold FF; lia) ltac:(change (fs_frame_bytes 1) with 128; fold FF; lia) ltac:(lia)).
        - (* seven bytes past prefix[48] (W_sites.v:319, W6's f4dbfd816b6): [FF + 32, FF + 87) still lies in the
             128-byte fake frame, application memory below the ceiling (in_app, either memory arm) *)
          exact (amem_range_sub_app FF 128 (FF + 32) (48 + 7) HFFapp HFFc ltac:(lia) ltac:(lia) ltac:(lia)).
        - exact (rt_rom_view_of_rom_view B W (ms_mem msT) HRVT). }
      intros W' c' _ Hc'. exact (aentry_post_of_art_post B _ _ _ _ _ _ _ _ _ _ _ Hc'). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Q10b & HT) & Hfr2 & Hpres2).
  rewrite HT47 in HT.
  (* ---- 0x8472c-0x84734: back from snprintf ---- *)
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 []) E2)
    by (rewrite HE2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; subst E2; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (HS2 : st_ok_pi segs VAL E2 ss_p1b
                  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + AF_p1_ret)) mem2 (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_p1b. apply pa_entry_st_ok_full.
    - rewrite HE2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn. repeat split.
    - split; [|split; [exact I | exact I]]. cbn. repeat split. }
  clear HE2.
  change (Z_to_bv 64 (BASE + 9280)) with (Z_to_bv 64 (BASE + AF_p1_ret)).
  paj_run_to_shx RUNTOP HS2 HJ2 AF_gn_l1.
  { intros a (r & Hin & _). cbn in Hin. destruct Hin. }
  pmkst HS2.
  pose proof (frame_of_read_only E2 (ss_mem ss_p1b) _ _ eq_refl HF) as Em3.
  cbn [ms_mem mkst] in Em3.
  pose proof (regs_kept_of_st_ok_pi E2 _ _ regs2 [] CALLEE_SAVED HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  p1_reg HS2 (5%bv : bv 5) Q5. p1_reg HS2 (6%bv : bv 5) Q6. p1_reg HS2 (12%bv : bv 5) Q12c.
  assert (KR : forall r, In r CALLEE_SAVED -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (KR2 r Hr). rewrite (p1_pres _ _ r HP2); [exact (KR1 r Hr)|].
    cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<- | Hr]; [p1_cs|]). destruct Hr. }
  cbn [sv_denot] in Q6. rewrite (EE2 9%nat 9%bv eq_refl) in Q6.
  rewrite (p1_pres _ _ 9%bv HP2 ltac:(p1_cs)), (KR1 9%bv ltac:(cbv; tauto)), R9 in Q6.
  unfold w64 in Q6. rewrite unsigned_lit_small in Q6 by lia.
  (* ---- what the snprintf call and the two runs kept ---- *)
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (FF + 32 <= a < FF + 32 + 48) -> ~ (F - 3 * ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem msT) a).
  { intros a Ha N1 N2. apply Hfr2; [exact Ha | exact N1 | intros Hx; apply N2; lia]. }
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + FF / 8 + 4 <= a < SB + FF / 8 + 10) -> ~ (F + 208 <= a < F + 216) ->
      ~ (FF + 32 <= a < FF + 32 + 48) -> ~ (F - 3 * ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha N1 N2 N3 N4. rewrite (KV2 a Ha N3 N4). exact (KV1 a Ha N1 N2). }
  assert (KP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
    by (intros a Hp; exact (Hpres2 a (KP1 a Hp))).
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem2) a)
    by (intros a Hw; exact (writable_kept (w_H W) mem mem2 a (KP a) Hw)).
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + FF / 8 + 4 <= a < SB + FF / 8 + 10) -> ~ (F + 208 <= a < F + 216) ->
      ~ (FF + 32 <= a < FF + 32 + 48) -> ~ (F - 3 * ESTACK <= a < F) -> abyte_kept W mem W mem2 a)
    by (intros a Ha N1 N2 N3 N4; split; [exact (KV a Ha N1 N2 N3 N4) | exact (WK a)]).
  assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (FF + 32 <= a < FF + 32 + 48) -> ~ (F - 3 * ESTACK <= a < F) ->
      abyte_kept W (ms_mem msT) W mem2 a)
    by (intros a Ha N1 N2; split; [exact (KV2 a Ha N1 N2) | intros Hw; exact (writable_kept (w_H W) _ mem2 a (Hpres2 a) Hw)]).
  assert (KIB : forall a, p1_ib ly S a -> abyte_kept W mem W mem2 a).
  { intros a [Hi | (b & n & Hin & Hb)].
    - apply KB; try lia; unfold SB in *; lia.
    - destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & B1 & B2 & B3 & _).
      pose proof (sep_block_frame segs B LAWS ly S W mem md b n 1 fpos HAR Hin Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd.
      apply KB; [lia | | lia | lia | rewrite Hes; lia].
      intros Hx. apply (fshadow_not_app FF 10 b (req_size n) a HFF4 ltac:(lia) B3 ltac:(unfold SB in Hx; lia) Hb). }
  assert (KS : forall a v, F <= a -> a + 8 <= F + 208 \/ F + 216 <= a -> a + 8 <= 2 ^ 64 ->
      sv8 W mem a v -> sv8 W mem2 a v).
  { intros a v H1 H2 H3 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia | unfold SB in *; lia | lia | lia | rewrite Hes; lia]. }
  assert (KFF : forall x, FF <= x < FF + 32 -> abyte_kept W mem W mem2 x).
  { intros x Hx. apply KB; [lia | | lia | lia | rewrite Hes; lia].
    intros Hs. apply (fshadow_not_app FF 10 FF 128 x HFF4 ltac:(lia) HFFapp ltac:(unfold SB in Hs; lia) ltac:(lia)). }
  (* the fake frame's flag word, its last 8 bytes: kept like its first 32 *)
  assert (KFL : forall x, FF + 120 <= x < FF + 128 -> abyte_kept W mem W mem2 x).
  { intros x Hx. apply KB; [lia | | lia | lia | rewrite Hes; lia].
    intros Hs. apply (fshadow_not_app FF 10 FF 128 x HFF4 ltac:(lia) HFFapp ltac:(unfold SB in Hs; lia) ltac:(lia)). }
  rewrite Em3.
  change (Z_to_bv 64 (BASE + AF_gn_l1)) with (w64 (fr_B0 + AF_gn_l1)).
  apply SRr_ret.
  exists (ms_regs ms), mem2, (with_vm_backing (m_vm_lazy md2) mat md2), ly, S, kk, fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact (p1_amodel_kept ly S W mem md W mem2 m HAR HMOD KIB) | exact HSEP]].
    split; [rewrite <- Em3; exact HJ2|].
    split.
    { (* the frame, with prefix[48]'s shadow open *)
      split.
      { intros o r Hin. assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
        apply KS; [lia | lia | lia | exact (GSV o r Hin)]. }
      split; [intros i Hi; apply WK; exact (GAW i Hi)|].
      do 9 (split; [apply KS; [lia | lia | lia | assumption]|]).
      do 7 (split; [apply KS; [lia | lia | lia | assumption]|]).
      split; [apply (akept_vm W mem); [intros x Hx; apply KFF; change (Z.of_nat 8) with 8 in Hx; lia | exact GF0]|].
      split; [apply (akept_vm W mem); [intros x Hx; apply KFF; change (Z.of_nat 8) with 8 in Hx; lia | exact GF8]|].
      split; [apply (akept_vm W mem); [intros x Hx; apply KFF; change (Z.of_nat 8) with 8 in Hx; lia | exact GF16]|].
      split; [intros i Hi; apply WK; exact (GAWF i Hi)|].
      split; [|intros i Hi; apply WK; exact (GAWS i Hi)].
      apply (p1_shadow_open (arm W mem) (arm W mem2) (SB + FF / 8) GSH).
      - intros j Hj v Hv. apply (akept_vm W mem); [|exact Hv]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
        assert (Hs16 : SB + FF / 8 <= x < SB + FF / 8 + 16) by lia.
        unfold SB in *.
        apply KB; [lia | lia | lia | | rewrite Hes; lia].
        intros Hs. apply (fshadow_not_app FF 16 FF 128 x HFF4 ltac:(lia) HFFapp Hs16 ltac:(lia)).
      - intros j Hj. unfold arm. apply p1_vm1_of_aview.
        rewrite (KV2 (SB + FF / 8 + Z.of_nat j) ltac:(unfold SB; lia)); [apply ZS; lia | |rewrite Hes; unfold SB; lia].
        intros Hs. apply (fshadow_not_app FF 16 FF 128 (SB + FF / 8 + Z.of_nat j) HFF4 ltac:(lia) HFFapp
                            ltac:(unfold SB in *; lia) ltac:(lia)). }
    split; [apply KS; [lia | lia | lia | exact H40]|].
    split; [apply KS; [lia | lia | lia | exact H144]|].
    split; [exact (p1_ainput_kept cx ly S W mem md W mem2 HAR HIN Hlen KIB)|].
    split.
    { intros a Ha. assert (Hi : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
      pose proof (pa_img_range a Hi) as Hr.
      rewrite (KV a ltac:(lia)); [exact (HRV a Ha) | unfold SB in *; lia | lia | lia | rewrite Hes; lia]. }
    split.
    { intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
      intros x Hx. apply KIB. left. unfold fr_jtab in *. cbn in Hx. lia. }
    apply (akept_vm W mem); [intros x Hx; apply KFL; change (Z.of_nat 8) with 8 in Hx; lia | exact HFL]. }
  split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27. }
  split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
  split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact R21|].
  split; [rewrite Q12c; reflexivity|].
  split; [rewrite Q5; reflexivity|].
  split; [exact Q6|].
  split; [lia|].
  split; [intros j Hj; lia|].
  split; [intros i Hi; apply WK; fold F; replace (F + 192 + i) with (F + (192 + i)) by lia; apply GAW; lia|].
  split; [apply (akept_vm W (ms_mem msT)); [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply KB2; [lia | lia | rewrite Hes; lia] | exact Z208]|].
  (* the prefix *)
  unfold gn_prefix_at, gn_pre. fold id. fold T. unfold printf_facts_c.pf_bytes in HT. rewrite map_app in HT.
  rewrite length_map.
  split.
  { intros i Hi. pose proof (HT (Z.to_nat i) ltac:(rewrite length_app, !length_map; cbn [length]; lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite app_nth1 in X by (rewrite length_map; lia). exact X. }
  split.
  { pose proof (HT (length T) ltac:(rewrite length_app, !length_map; cbn [length]; lia)) as X.
    rewrite app_nth2 in X by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag in X. exact X. }
  split.
  { intros a Ha. apply p1_vis_pres. apply KP. exact (proj1 (HFpres a ltac:(lia))). }
  split; [exact (p1_nz T HTF) | lia].
Qed.

End gp1.
