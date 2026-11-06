(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segments STEP and OUTER of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82c2c .. 0x830dc), against the segment interface lib/A/W_relay_instance_gone_cx.v.
   STEP  RGE i 0x82f44 -> RGO (S i) 0x82d98 | RGU 0x82fa4: F's shadow bytes 4 .. 9 := 0xf8 (0x82f48-0x82f60),
         g_nsrc reread through 72(sp) (0x82f64-0x82f68), i reloaded from 88(sp) and incremented (0x82f6c-0x82f70),
         s6 reloaded from 40(sp) (0x82f74), the test blt a4, a0 (0x82f78) and j 0x82fa4 (0x82f7c).  No call.  The
         shadow stores are a plain run (the token run keeps its windows off the shadow), the journal is opened
         around it and packed again; every other fact of the cut is kept because the six stored bytes are shadow
         bytes of the fake frame F, apart from the image, the heap blocks and the stack.
   OUTER the outer loop by induction on |es| - i (lib/A/W_drain_outer.v's form, cgif lib/A/ACfj.v:157-163).
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): converted IN PLACE to the
   generic Section of the segment interface (commit 863f3bb0f69, lib/A/W_relay_instance_gone_cx.v): any allocator
   relation ARx with its laws, the program statics PST and the room record RP; Section c below is the cx's list.  STEP
   runs over the generic journal (W_frame_x.v's paj_run_sh_x / paj_run_to_sh_x / psrr_branch_pi_x on YCbqG.v's
   ajournal_x, packed again by W_journal_x.v ajournal_gx_pack_x); the cut's head set Hp1 is kept (no call), and gbud,
   room and counts included, is carried unchanged: the step keeps the layout, the allocator state and the trace
   still owed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia's division reading on (Stdlib's default), as this walk was proved: the twin kits' Require chain leaves the
   flag off, and HSFb below needs F / 8 tied to F *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies: lib/A/W_relay_instance_gone_cx.v Section c's list (commit
   863f3bb0f69), names, order and texts; the cx's comments say what each one is. ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the meter does not charge the fake frame's seat or its release, both a set_fs of the state (W8's ruling, KF-COUNT
   #4: the old text over an ablocks equation is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x82d58 (kept at 72(sp), listing A_HI 44) and 0x82d74
   (s6, A_HI 45).  The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges
   both by vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH44 : VAL (A_HI 44) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH45 : VAL (A_HI 45) = rg_src RG + RIG_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx) *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata): k3's HEND5L, verbatim *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells: the GOT word, a fact of every ARx state; the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the literals of the snprintf call and " end\0", in the cx's glit_at_x form (its one definition, at ARx) *)
Hypothesis HLIT20 : glit_at_x ARx 20 (RIG_FMT ++ [0]).
Hypothesis HLIT21 : glit_at_x ARx 21 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9e658, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x
   (W_sites_x.v), which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v
   HLITGOT_PB_fr, whose statement is this text at PI := PB_fr (commit 2f48fc47493's hypothesis, carried here). *)
Hypothesis HLITGOT : VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD.
Hypothesis HLIT31 : glit_at_x ARx 31 ([32; 101; 110; 100] ++ [0]).
(* the program statics PST hold no byte this walk carries through a journal's image clause *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNTOP := SRr_run_to_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let BR := paj_branch (PI := PI).

(* ---- STEP's entry state at RGE (0x82f44).  Atoms: s1 = sp (9); 32 = g_src's register image (40(sp)), 33 = F's
   shadow (48(sp)), 34 = g_nsrc's register image (72(sp)), 35 = i (88(sp)), 36 = g_nsrc.  Regions: the four frame
   slots, F's shadow bytes 4 .. 9 (written), g_nsrc (read). ---- *)
Definition stp_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 40 96 40 40
    [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
     YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 4 10 4 10 [];
  YP09.mkRegion (Some 34%nat) (-1464) (-1460) (-1464) (-1464) [YP09.mkChunk (-1464) (CVal 4 (SOff 36 0))] ].
Definition stp_facts : facts := mkFacts [(35%nat, mkAF 0 16 0); (36%nat, mkAF 0 16 0)] [] [].
Definition ss_stp : sstate := mkSS A_rig_step sr_atoms stp_regions None stp_facts.
Definition stp_extra (F i n : Z) : list word :=
map (Z_to_bv 64) [rg_src RG + RIG_HI_SRC; shadow_addr F; rg_nsrc RG + RIG_HI_NSRC; i; n].

(* ---- What the shadow stores keep.  Every fact the cut carries reads bytes of the image (the relay's and the
   output's globals, g_s, errno), of heap blocks, of the fake frame F or of the stack; the stores write six shadow
   bytes of F, which are none of these.  The footprint lemmas below say, for each representation predicate of
   W_rep.v, that every byte of its footprint is an image byte (given), or a byte of a block it names, and that the
   blocks it names are live: the premises W_rep.v's *_kept lemmas take. ---- *)
Lemma stp_len_bzs : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma stp_req_ge : forall n, 0 <= n -> n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma stp_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8. cbn [length]. lia.
Qed.
Lemma stp_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.

Section fp.
Variable ok : Z -> Prop.
Variables (ly : alayout) (S : astate).
Hypothesis OKB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ok a.
Lemma stp_ok_in : forall p n a, In (p, n) (ablocks B ly S) -> 0 <= n -> p <= a < p + n -> ok a.
Proof. intros p n a Hin Hn Ha. apply (OKB p n a Hin). pose proof (stp_req_ge n Hn). lia. Qed.

Lemma stp_entry_fp : forall W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> ok a.
Proof.
intros W m e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
  destruct H10 as [(Hc0 & _) | (Hc & Hin & Hj & _)]; [lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs, length_app in Ha.
  apply (stp_ok_in _ _ a Hin); lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs, stp_key_ptrs_len in Ha.
    destruct H12 as [(_ & Hk) | (_ & Hin & Hk1 & Hk2 & _)].
    * rewrite Hk in Ha. cbn [length] in Ha. lia.
    * unfold re_nheld in Hk1. apply (stp_ok_in _ _ a Hin); lia.
  + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _).
    unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs, length_app in Ha. cbn [length] in Ha.
    apply (stp_ok_in _ _ a K1); lia.
Qed.
Lemma stp_entry_blks : forall W m e, aentry_ok B ly S W m e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros W m e (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15) b Hb.
unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
- destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
  destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- destruct (re_hp e =? 0) eqn:Eh; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Eh.
  destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.

Lemma stp_list_fp : forall W m LA l lines, alist_at B ly S W m LA l lines ->
  (forall a, LA <= a < LA + 16 -> ok a) ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> ok a.
Proof.
intros W m LA l lines (_ & _ & _ & _ & H5 & H6 & _ & _ & H9) HLA r Hr a Ha.
destruct Hr as [<- | Hr]; [exact (HLA a Ha)|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
  destruct H6 as [(Hc0 & _) | (Hc & Hin & Hj & _)]; [lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs, length_app, stp_recs_len in Ha.
  unfold hl_n, AREC in *. apply (stp_ok_in _ _ a Hin); lia.
- apply in_map_iff in Hr as (xr & <- & Hxr). rewrite Forall_forall in H9. destruct (H9 xr Hxr) as (K1 & _).
  unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs, length_app in Ha. cbn [length] in Ha.
  apply (stp_ok_in _ _ a K1); lia.
Qed.
Lemma stp_list_blks : forall W m LA l lines, alist_at B ly S W m LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros W m LA l lines (_ & _ & _ & _ & _ & H6 & _ & _ & H9) b Hb.
unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
  destruct H6 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (xr & <- & Hxr). rewrite Forall_forall in H9. exact (proj1 (H9 xr Hxr)).
Qed.

Lemma stp_src_fp : forall W m HA h, asrc_at B ly S W m HA h ->
  (forall a, HA <= a < HA + ASRC -> ok a) ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> ok a.
Proof.
intros W m HA h (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & H19 & _ & _ & H22 & H23 & _)
  HHA r Hr a Ha.
destruct Hr as [<- | [<- | Hr]].
- exact (HHA a Ha).
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite stp_len_bzs in Ha.
  apply (stp_ok_in _ _ a H18); unfold APARTIAL in *; lia.
- apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
  + refine (stp_list_fp W m (HA + 16) _ false H10 _ r Hr a Ha). intros x Hx. apply HHA. unfold ASRC. lia.
  + refine (stp_list_fp W m (HA + 64) _ true H22 _ r Hr a Ha). intros x Hx. apply HHA. unfold ASRC. lia.
  + refine (stp_list_fp W m (HA + 80) _ true H23 _ r Hr a Ha). intros x Hx. apply HHA. unfold ASRC. lia.
Qed.
Lemma stp_src_blks : forall W m HA h, asrc_at B ly S W m HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros W m HA h (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _ & H22 & H23 & _)
  b Hb.
destruct Hb as [<- | Hb]; [exact H18|].
apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
- exact (stp_list_blks W m _ _ _ H10 b Hb).
- exact (stp_list_blks W m _ _ _ H22 b Hb).
- exact (stp_list_blks W m _ _ _ H23 b Hb).
Qed.

Lemma stp_relay_fp : forall W m G es, arelay_at B RG ly S W m G es ->
  (forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
     rg_capsrc RG <= a < rg_capsrc RG + 4 -> ok a) ->
  forall r, In r (arelay_fp RG G es) -> forall a, fst r <= a < snd r -> ok a.
Proof.
intros W m G es (_ & _ & _ & _ & _ & _ & _ & A8 & _ & A10 & _) HG r Hr a Ha.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
- apply HG; lia.
- apply HG; lia.
- apply HG; lia.
- apply (stp_ok_in _ _ a A8); unfold ATABLE in *; lia.
- apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
  rewrite Forall_forall in A10. exact (stp_entry_fp W m e (A10 e He) r Hr a Ha).
Qed.
Lemma stp_relay_blks : forall W m G es, arelay_at B RG ly S W m G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
intros W m G es (_ & _ & _ & _ & _ & _ & _ & A8 & _ & A10 & _) b Hb.
destruct Hb as [<- | Hb]; [exact A8|].
apply in_concat in Hb as (bl & Hbl & Hb). apply in_map_iff in Hbl as (e & <- & He).
rewrite Forall_forall in A10. exact (stp_entry_blks W m e (A10 e He) b Hb).
Qed.

(* the output's cells: nine globals and errno *)
Definition stp_outg (a : Z) : Prop :=
rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4.
Lemma stp_out_fp : forall W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out ->
  (forall a, stp_outg a -> ok a) ->
  forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> ok a.
Proof.
intros W m c O mx no cap out HO HG r Hr a Ha.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
unfold aout_fp in Hr.
do 9 (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; apply HG; unfold stp_outg; lia|]).
destruct (cap =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
destruct H26 as [(Hc0 & _) | (Hc & _ & Hin & _)]; [lia|]. cbn [fst snd] in Ha. apply (stp_ok_in _ _ a Hin); lia.
Qed.
Lemma stp_out_blks : forall W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out ->
  forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros W m c O mx no cap out HO b Hb.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
destruct H26 as [(Hc0 & _) | (_ & _ & Hin & _)]; [lia | exact Hin].
Qed.
End fp.

(* The cut's memory facts hold again after a run that changed at most F's shadow bytes 4 .. 9 of the view and lost no
   present byte (STEP's two runs). *)
Lemma stp_keep : forall cx (j : nat) F FL fpos ly1 S1 Hp1 W1 m1 md1 m2 qd c2 O2 cap2 out2 spent,
  GBASE B ARx MT RP MMAX RG cx -> ARx ly1 S1 Hp1 W1 m1 md1 ->
  4096 <= F -> F + 128 <= alloc_ceiling -> in_app F 128 ->
  alloc_ceiling + RIG_FRAME <= gsp0 cx <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
  rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
  alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
  GOUT B MT RP MMAX RG cx j qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  rom_view SEGS W1 m2 /\ apres_kept B (gxW cx) (gxmem cx) W1 m2 /\ g_frame cx fpos F FL ly1 W1 m2 /\
  alock_at RG W1 m2 true /\ g_lslots RG cx F W1 m2 /\ GOUT B MT RP MMAX RG cx j qd c2 O2 cap2 out2 spent ly1 S1 W1 m2.
Proof.
intros cx j F FL fpos ly1 S1 Hp1 W1 m1 md1 m2 qd c2 O2 cap2 out2 spent HB HAR HF4096 HFceil HFapp HSP HAV HGR
  HROM HAPK HFR HLK HLS HGO.
destruct HB as (_ & _ & _ & HRP & _ & _ & _ & _ & _ & _ & HLH & HDS & _).
destruct HRP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
set (K := abyte_kept W1 m1 W1 m2).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) -> K a).
{ intros a Ha Hn. split; [exact (HAV a Ha Hn)|]. unfold arm. apply writable_kept. exact (HGR a). }
assert (KIMG : forall a, in_img SEGS a -> K a).
{ intros a Ha. pose proof (Hsegs a Ha). apply KW; [lia|].
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos F 8 ltac:(lia)). lia. }
assert (KAPP : forall p n a, in_app p n -> p <= a < p + n -> K a).
{ intros p n a Hp Ha. apply KW.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hp. lia.
  - intros Hw. apply (fshadow_not_app F 10 p n a HF4096 ltac:(lia) Hp); [|exact Ha].
    unfold shadow_addr, SHADOW_OFF in Hw. lia. }
assert (KBLK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n -> K a).
{ intros p n a Hin Ha. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & Happ & _).
  exact (KAPP _ _ a Happ Ha). }
assert (KSTK : forall a, alloc_ceiling <= a < 2 ^ 47 -> K a).
{ intros a Ha. apply KW; [lia|]. unfold shadow_addr, SHADOW_OFF in *.
  assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (KRNG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_lock RG <= a < rg_lock RG + 12 \/
  rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_src RG <= a < rg_src RG + 8 -> K a).
{ intros a Ha. apply KIMG. apply (proj1 (RGIMG a ltac:(unfold rg_rng; tauto))). }
assert (GIN : forall a, inG (G_RIG B RG) a -> K a) by (intros a Ha; apply KIMG; exact (proj1 (HGRIG a Ha))).
assert (KOUT : forall a, stp_outg a -> K a).
{ intros a Ha. unfold stp_outg in Ha.
  destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]];
  first [ apply KIMG; apply (proj1 (HRGI a ltac:(tauto)))
        | apply GIN; unfold G_RIG, G_DR, G_SL, inG;
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]) ]. }
assert (KRG3 : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 -> K a).
{ intros a [H|[H|H]]; [apply KRNG; tauto | apply KRNG; tauto |].
  apply KIMG. apply (proj1 (HRGI a ltac:(tauto))). }
assert (HJ4 : forall i', (i' < length (gxes cx))%nat -> re_eof (gnth cx i') = 0 -> (snd (ghj cx i') < 4)%nat).
{ intros i' Hi' He. rewrite Forall_forall in HDS.
  assert (Hn : nth i' (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i', ghj cx i'))
    by (unfold gps, gnth, ghj; apply combine_nth; symmetry; exact HLH).
  assert (Hin : In (gnth cx i', ghj cx i') (gps cx))
    by (rewrite <- Hn; apply nth_In; unfold gps; rewrite length_combine, HLH; lia).
  destruct (HDS _ Hin He) as (Hj & _). exact Hj. }
assert (KSRC : forall jj h, (jj < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat jj) h ->
  asrc_at B ly1 S1 W1 m2 (rg_s RG + ASRC * Z.of_nat jj) h).
{ intros jj h Hjj Hs. apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ Hs).
  - intros r Hr a Ha. eapply (stp_src_fp K ly1 S1 KBLK); [exact Hs | | exact Hr | exact Ha].
    intros x Hx. apply KRNG. left. unfold ASRC in *. lia.
  - intros b Hb. eapply stp_src_blks; [exact Hs | exact Hb]. }
destruct HGO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
destruct HFR as (EF & EFL & VFL & V16 & V24 & V80 & HSV).
destruct HLS as (V40 & V48 & V56 & V64 & V72).
assert (KS : forall o n v, 16 <= o -> o + Z.of_nat n <= RIG_FRAME ->
  val_mem SEGS (arm W1 m1) (gsp1 cx + o) n v -> val_mem SEGS (arm W1 m2) (gsp1 cx + o) n v).
{ intros o n v Ho Hn Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply KSTK.
  unfold gsp1, RIG_FRAME in *. lia. }
split.
{ intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  rewrite (proj1 (KIMG a Hi)). exact (HROM a Ha). }
split; [intros a Hi Ho He Hp; apply HGR; exact (HAPK a Hi Ho He Hp)|].
split.
{ split; [exact EF|]. split; [exact EFL|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply (KAPP F 128 x HFapp); cbn in Hx; lia | exact VFL]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V16]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V24]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V80]|].
  intros k Hk. replace (gsp1 cx + 120 + 8 * Z.of_nat k) with (gsp1 cx + (120 + 8 * Z.of_nat k)) by lia.
  apply KS; [lia | cbn; unfold RIG_FRAME; lia |].
  replace (gsp1 cx + (120 + 8 * Z.of_nat k)) with (gsp1 cx + 120 + 8 * Z.of_nat k) by lia. exact (HSV k Hk). }
split.
{ apply (alock_at_kept RG W1 m1 W1 m2 true HLK). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  apply KRNG. tauto. }
split.
{ split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V40]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V48]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V56]|].
  split; [apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V64]|].
  apply KS; [lia | cbn; unfold RIG_FRAME; lia | exact V72]. }
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ apply (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ G4).
  - intros r Hr a Ha. eapply (stp_relay_fp K ly1 S1 KBLK); [exact G4 | exact KRG3 | exact Hr | exact Ha].
  - intros b Hb. eapply stp_relay_blks; [exact G4 | exact Hb]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ G5).
  - intros r Hr a Ha. eapply (stp_out_fp K ly1 S1 KBLK); [exact G5 | exact KOUT | exact Hr | exact Ha].
  - intros b Hb. eapply stp_out_blks; [exact G5 | exact Hb]. }
split.
{ intros i' Hi' He. unfold gslot. apply KSRC; [apply (HJ4 i'); [lia | exact He] | exact (G6 i' Hi' He)]. }
split.
{ eapply Forall_impl; [|exact G7]. intros p Hp He. destruct (Hp He) as (Hj & Hs & Hoth & Hrest).
  split; [exact Hj|]. split; [exact (KSRC _ _ Hj Hs)|]. split; [|exact Hrest].
  intros i0 Hi0 Hne. destruct (Hoth i0 Hi0 Hne) as (f & o & Vf & Vo & Hfo). exists f, o.
  split; [|split; [|exact Hfo]]; (apply (akept_vm W1 m1); [intros x Hx; apply KRNG; left; unfold ASRC in *; cbn in Hx; lia|]);
  assumption. }
split.
{ intros a Ha Hns. destruct (G8 a Ha Hns) as (Q1 & Q2). destruct (KRNG a (or_introl Ha)) as (Q3 & Q4).
  split; [rewrite Q3; exact Q1 | intros Hw; apply Q4; apply Q2; exact Hw]. }
split; [exact G9 | exact G10].
Qed.

(* the regions' writable windows are F's shadow bytes 4 .. 9 only: a byte outside them is not in any window *)
Ltac stp_nowr U33 Hn :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U33 in Hr; lia | ]);
destruct Hin.
(* the stores are F's own shadow bytes: the journal's own-frame window *)
Ltac stp_awr U33 EF fpos :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U33 in Hr;
    first [ lia
          | right; right; right; exists 1, fpos; split; [left; reflexivity|]; right; rewrite EF; unfold in_zr; cbn [fst snd];
            change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; lia ]
  | ]);
destruct Hin.

Theorem rig_step_proof : rig_step_stmt B PST ARx MT RP MMAX RG.
Proof.
intros cx i W1 c1 HB HE KO KU.
destruct HE as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & R20 & V88 &
  Hi & HL & HLS & HGO).
destruct HL as (fpos & Hp1 & HJX & HROM & HAPK & HFR & HLK).
pose proof HFR as (EF & EFL & VFL & V16 & V24 & V80 & HSV).
pose proof HRB as (Rsp & R3 & R4 & R8 & R9 & R18).
pose proof HLS as (V40 & V48 & V56 & V64 & V72).
destruct HJX as (HSTK0 & HXO & (memS & HJi & Hag) & Hout).
pose proof HGO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof G4 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
pose proof HJi as (HAR1 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _ & _).
destruct HSTK as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFapp).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, HFpres, HFSpres. change (128 / 8) with 16 in HFSpres.
rewrite EF in HF4096, HFceil, HFapp, HFal, HFpres, HFSpres.
assert (WS : RIG_STK_x = 17200) by reflexivity.
assert (HG1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (HLEN : length (map fst qd ++ skipn (S i) (gxes cx)) = length (gxes cx)).
{ rewrite length_app, length_map, length_skipn. lia. }
set (nsrc := Z.of_nat (length (gxes cx))).
rewrite HLEN in A3, A7.
set (E := Eimg (Ereg regs1 (stp_extra F (Z.of_nat i) nsrc))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (stp_extra F (Z.of_nat i) nsrc)) E)
by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (stp_extra F (Z.of_nat i) nsrc) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E9 : ew E 9 = Z_to_bv 64 (gsp1 cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 (rg_src RG + RIG_HI_SRC)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr F)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (rg_nsrc RG + RIG_HI_NSRC)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat i)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 nsrc) by exact (EX 4%nat ltac:(lia)).
assert (Hnb : (length (gxes cx) <= 16)%nat) by exact A7.
assert (HSPb : alloc_ceiling + 17200 <= gsp0 cx <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HNS : 0 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= kLowMemEnd /\ 0 <= rg_src RG /\ rg_src RG + 8 <= kLowMemEnd).
{ pose proof HB as (_ & _ & _ & HRGP0 & _). destruct HRGP0 as (_ & _ & _ & _ & _ & _ & RGIMG & _).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG + 3) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; lia)))). lia. }
assert (HSFb : kLowMemEnd <= shadow_addr F /\ shadow_addr F + 16 <= kHighMemBeg).
{ unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. pose proof (Z.div_pos F 8 ltac:(lia)).
  assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (U9 : bv_unsigned (ew E 9) = gsp1 cx) by (rewrite E9; apply unsigned_lit_small; rewrite HG1; lia).
assert (U33 : bv_unsigned (ew E 33) = shadow_addr F)
by (rewrite E33; apply unsigned_lit_small; unfold kHighMemBeg in *; lia).
assert (U34 : bv_unsigned (ew E 34) = rg_nsrc RG + RIG_HI_NSRC)
by (rewrite E34; apply unsigned_lit_small; unfold RIG_HI_NSRC, kLowMemEnd in *; lia).
assert (U35 : bv_unsigned (ew E 35) = Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = nsrc) by (rewrite E36; apply unsigned_lit_small; unfold nsrc; lia).
assert (HS : st_ok_pi SEGS VAL E ss_stp
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rig_step)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_stp. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stp_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; [rewrite U9 | rewrite U33 | rewrite U34].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold RIG_HI_SRC, RIG_HI_NSRC, kLowMemEnd, kHighMemBeg in *.
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 40 8 (SOff 32 0) (rg_src RG + 1460));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V40].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 48 8 (SOff 33 0) (shadow_addr F));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V48].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 72 8 (SOff 34 0) (rg_nsrc RG + 1464));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V72].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 88 8 (SOff 35 0) (Z.of_nat i));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V88].
    + split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + unfold RIG_HI_NSRC in *. split; [lia|]. split; [unfold kLowMemEnd in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG + RIG_HI_NSRC) (-1464) 4 (SOff 36 0) nsrc);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold nsrc; zside | lia |].
      replace (rg_nsrc RG + RIG_HI_NSRC + -1464) with (rg_nsrc RG) by (unfold RIG_HI_NSRC; lia). exact A3.
  - cbn [stp_regions pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U34.
    unfold RIG_HI_NSRC, kLowMemEnd, kHighMemBeg in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [stp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U35, U36, !Z.pow_0_r, !Z.mod_1_r. unfold nsrc. repeat split; lia. }
assert (HSP' : alloc_ceiling + RIG_FRAME <= gsp0 cx <= 2 ^ 47) by (unfold RIG_FRAME; lia).
unfold cfg_at, w64.
(* 0x82f44 .. 0x82f78: s5 = F's shadow, its bytes 4 .. 9 := 0xf8, a0 = g_nsrc, a4 = i + 1, s6 = g_src's image *)
paj_run_sh_x RUNP HS HJi.
{ stp_awr U33 EF fpos. }
cbn [ms_mem mkst] in HF, HFr, HG.
psrr_branch_pi_x RUNP BR HS.
- (* i + 1 < g_nsrc: on to entry i + 1 *)
  assert (Hlt : (S i < length (gxes cx))%nat).
  { cbn [branch_taken sv_denot] in Hc.
    rewrite U35, U36, Z.add_0_r, bv_lts_signed in Hc.
    rewrite !bv_signed_small, !unsigned_lit_small in Hc
      by (rewrite ?unsigned_lit_small by (unfold nsrc in *; lia); unfold nsrc in *; lia). apply Z.ltb_lt in Hc. unfold nsrc in Hc. lia. }
  paj_run_to_sh_x RUNTOP HS HJi A_rig_outer.
  { stp_awr U33 EF fpos. }
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha Hn. rewrite (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(stp_nowr U33 Hn)).
    exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha ltac:(stp_nowr U33 Hn)). }
  assert (MGR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; apply (apresent_grows _ _ _ a HG0); apply (apresent_grows _ _ _ a HG); exact Hp).
  destruct (stp_keep cx (S i) F FL fpos ly1 S1 Hp1 W1 m1 md1 (ms_mem ms0) qd c2 O2 cap2 out2 spent HB HAR1 HF4096 HFceil
    HFapp HSP' MEQ MGR HROM HAPK HFR HLK HLS HGO) as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20]%bv HS HAE ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (14%bv : bv 5) N14.
  apply KO.
  lazymatch goal with |- RGO _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst _ _ _ _) ?mdx) =>
    exists (ms_regs ms0), ly1, S1, (ms_mem ms0), mdx, k1, F, FL, qd, c2, O2, cap2, out2, spent end.
  split; [reflexivity|].
  split.
  { unfold gregs_base. unfold spZ. rewrite !HK by (cbv; tauto).
    split; [exact Rsp|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9 | exact R18]. }
  split; [rewrite HK by (cbv; tauto); exact R20|].
  split; [rewrite N21, E33; reflexivity|].
  split; [rewrite N22, E32; reflexivity|].
  split; [rewrite N14, U35; unfold w64; f_equal; lia|].
  split; [exact Hlt|].
  split; [exists fpos, Hp1; split; [|exact (conj K1 (conj K2 (conj K3 K4)))]|].
  { eapply ajournal_gx_pack_x; [exact HSTK0 | exact HXO | exact HJi | exact Hag | intros a Ha; lia]. }
  exact (conj K5 K6).
- (* i + 1 >= g_nsrc: every entry done, the unlock *)
  assert (Hend : S i = length (gxes cx)).
  { cbn [branch_taken sv_denot] in Hc. rewrite U35, U36, Z.add_0_r, bv_lts_signed in Hc.
    rewrite !bv_signed_small, !unsigned_lit_small in Hc
      by (rewrite ?unsigned_lit_small by (unfold nsrc in *; lia); unfold nsrc in *; lia). apply Z.ltb_ge in Hc. unfold nsrc in Hc. lia. }
  paj_run_to_sh_x RUNTOP HS HJi A_rig_unlock.
  { stp_awr U33 EF fpos. }
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha Hn. rewrite (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(stp_nowr U33 Hn)).
    exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha ltac:(stp_nowr U33 Hn)). }
  assert (MGR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; apply (apresent_grows _ _ _ a HG0); apply (apresent_grows _ _ _ a HG); exact Hp).
  destruct (stp_keep cx (S i) F FL fpos ly1 S1 Hp1 W1 m1 md1 (ms_mem ms0) qd c2 O2 cap2 out2 spent HB HAR1 HF4096 HFceil
    HFapp HSP' MEQ MGR HROM HAPK HFR HLK HLS HGO) as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18]%bv HS HAE ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  prreg HS (21%bv : bv 5) N21.
  apply KU.
  lazymatch goal with |- RGU _ _ _ _ _ _ _ _ _ (mkCfg (mkst _ _ _ _) ?mdx) =>
    exists (ms_regs ms0), ly1, S1, (ms_mem ms0), mdx, k1, F, FL, qd, c2, O2, cap2, out2, spent end.
  split; [reflexivity|].
  split.
  { unfold gregs_base. unfold spZ. rewrite !HK by (cbv; tauto).
    split; [exact Rsp|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9 | exact R18]. }
  split; [rewrite N21, E33; reflexivity|].
  split; [exists fpos, Hp1; split; [|exact (conj K1 (conj K2 (conj K3 K4)))]|].
  { eapply ajournal_gx_pack_x; [exact HSTK0 | exact HXO | exact HJi | exact Hag | intros a Ha; lia]. }
  rewrite <- Hend. exact K6.
Qed.

(* ---- OUTER: the outer loop by induction on |es| - i (RGO carries i < |es|, so the bound 0 is refuted); one round is
   TOP, then the inner loop (KEYS, fed KEY) from RGI i 0 r or straight to RGE i, then STEP back to RGO (S i) or out
   to RGU. ---- *)
Lemma stp_rgo_lt : forall cx i W1 c1, RGO B PST ARx MT RP MMAX RG cx i W1 c1 -> (i < length (gxes cx))%nat.
Proof.
intros cx i W1 c1 HO.
destruct HO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent &
  _ & _ & _ & _ & _ & _ & Hi & _).
exact Hi.
Qed.

Theorem rig_outer_proof : rig_outer_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
intros TOP KEY KEYS STEP.
assert (MAIN : forall n cx i W1 c1, (length (gxes cx) - i <= n)%nat ->
  GBASE B ARx MT RP MMAX RG cx -> GCTX CTX_AFREE cx -> RGO B PST ARx MT RP MMAX RG cx i W1 c1 ->
  (forall W2 c2, RGU B PST ARx MT RP MMAX RG cx W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
  SRr SEGS W1 c1 (gPOST B PST ARx MT RP RG cx)).
{ induction n as [|n IH]; intros cx i W1 c1 N HB HC HO HU.
  - pose proof (stp_rgo_lt cx i W1 c1 HO). lia.
  - pose proof (stp_rgo_lt cx i W1 c1 HO) as Hi.
    assert (NXT : forall W3 c3, RGE B PST ARx MT RP MMAX RG cx i W3 c3 -> SRr SEGS W3 c3 (gPOST B PST ARx MT RP RG cx)).
    { intros W3 c3 HE. apply (STEP cx i W3 c3 HB HE); [|exact HU].
      intros W4 c4 HO4. apply (IH cx (S i) W4 c4); [lia | exact HB | exact HC | exact HO4 | exact HU]. }
    apply (TOP cx i W1 c1 HB HO); [|exact NXT].
    intros r W2 c2 HI. exact (KEYS KEY cx i 0%nat r W2 c2 HB HC HI NXT). }
intros cx i W1 c1 HB HC HO HU. exact (MAIN _ cx i W1 c1 (le_n _) HB HC HO HU).
Qed.

(* ---- route R (G8 rig, A): STEP and OUTER over a world relation R, concluding W_relay_instance_gone_cx.v Section
   wR's texts.  STEP makes no call: its runs go through W_frame_x.v's G twins at R (RUNPR / RUNTOPR, BRR), and the
   journal is packed again at R. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNTOPR := SRrG_run_to_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* W_rig_step.v:484 rig_step_proof at R *)
Theorem rig_step_proof_xR : rig_step_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx i W1 c1 HB HE KO KU.
destruct HE as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & R20 & V88 &
  Hi & HL & HLS & HGO).
destruct HL as (fpos & Hp1 & HJX & HROM & HAPK & HFR & HLK).
pose proof HFR as (EF & EFL & VFL & V16 & V24 & V80 & HSV).
pose proof HRB as (Rsp & R3 & R4 & R8 & R9 & R18).
pose proof HLS as (V40 & V48 & V56 & V64 & V72).
destruct HJX as (HSTK0 & HXO & (memS & HJi & Hag) & Hout).
pose proof HGO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof G4 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
pose proof HJi as (HAR1 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _ & _).
destruct HSTK as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFapp).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, HFpres, HFSpres. change (128 / 8) with 16 in HFSpres.
rewrite EF in HF4096, HFceil, HFapp, HFal, HFpres, HFSpres.
assert (WS : RIG_STK_x = 17200) by reflexivity.
assert (HG1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (HLEN : length (map fst qd ++ skipn (S i) (gxes cx)) = length (gxes cx)).
{ rewrite length_app, length_map, length_skipn. lia. }
set (nsrc := Z.of_nat (length (gxes cx))).
rewrite HLEN in A3, A7.
set (E := Eimg (Ereg regs1 (stp_extra F (Z.of_nat i) nsrc))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (stp_extra F (Z.of_nat i) nsrc)) E)
by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (stp_extra F (Z.of_nat i) nsrc) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E9 : ew E 9 = Z_to_bv 64 (gsp1 cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 (rg_src RG + RIG_HI_SRC)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr F)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (rg_nsrc RG + RIG_HI_NSRC)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat i)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 nsrc) by exact (EX 4%nat ltac:(lia)).
assert (Hnb : (length (gxes cx) <= 16)%nat) by exact A7.
assert (HSPb : alloc_ceiling + 17200 <= gsp0 cx <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HNS : 0 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= kLowMemEnd /\ 0 <= rg_src RG /\ rg_src RG + 8 <= kLowMemEnd).
{ pose proof HB as (_ & _ & _ & HRGP0 & _). destruct HRGP0 as (_ & _ & _ & _ & _ & _ & RGIMG & _).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG + 3) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; lia)))).
  pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; lia)))). lia. }
assert (HSFb : kLowMemEnd <= shadow_addr F /\ shadow_addr F + 16 <= kHighMemBeg).
{ unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. pose proof (Z.div_pos F 8 ltac:(lia)).
  assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (U9 : bv_unsigned (ew E 9) = gsp1 cx) by (rewrite E9; apply unsigned_lit_small; rewrite HG1; lia).
assert (U33 : bv_unsigned (ew E 33) = shadow_addr F)
by (rewrite E33; apply unsigned_lit_small; unfold kHighMemBeg in *; lia).
assert (U34 : bv_unsigned (ew E 34) = rg_nsrc RG + RIG_HI_NSRC)
by (rewrite E34; apply unsigned_lit_small; unfold RIG_HI_NSRC, kLowMemEnd in *; lia).
assert (U35 : bv_unsigned (ew E 35) = Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = nsrc) by (rewrite E36; apply unsigned_lit_small; unfold nsrc; lia).
assert (HS : st_ok_pi SEGS VAL E ss_stp
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rig_step)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_stp. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stp_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; [rewrite U9 | rewrite U33 | rewrite U34].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold RIG_HI_SRC, RIG_HI_NSRC, kLowMemEnd, kHighMemBeg in *.
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 40 8 (SOff 32 0) (rg_src RG + 1460));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V40].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 48 8 (SOff 33 0) (shadow_addr F));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V48].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 72 8 (SOff 34 0) (rg_nsrc RG + 1464));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V72].
      * apply (chunk_ok_val SEGS E _ (gsp1 cx) 88 8 (SOff 35 0) (Z.of_nat i));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | lia | exact V88].
    + split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + unfold RIG_HI_NSRC in *. split; [lia|]. split; [unfold kLowMemEnd in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG + RIG_HI_NSRC) (-1464) 4 (SOff 36 0) nsrc);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold nsrc; zside | lia |].
      replace (rg_nsrc RG + RIG_HI_NSRC + -1464) with (rg_nsrc RG) by (unfold RIG_HI_NSRC; lia). exact A3.
  - cbn [stp_regions pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U34.
    unfold RIG_HI_NSRC, kLowMemEnd, kHighMemBeg in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [stp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U35, U36, !Z.pow_0_r, !Z.mod_1_r. unfold nsrc. repeat split; lia. }
assert (HSP' : alloc_ceiling + RIG_FRAME <= gsp0 cx <= 2 ^ 47) by (unfold RIG_FRAME; lia).
unfold cfg_at, w64.
(* 0x82f44 .. 0x82f78: s5 = F's shadow, its bytes 4 .. 9 := 0xf8, a0 = g_nsrc, a4 = i + 1, s6 = g_src's image *)
paj_run_sh_x RUNPR HS HJi.
{ stp_awr U33 EF fpos. }
cbn [ms_mem mkst] in HF, HFr, HG.
psrr_branch_pi_x RUNPR BRR HS.
- (* i + 1 < g_nsrc: on to entry i + 1 *)
  assert (Hlt : (S i < length (gxes cx))%nat).
  { cbn [branch_taken sv_denot] in Hc.
    rewrite U35, U36, Z.add_0_r, bv_lts_signed in Hc.
    rewrite !bv_signed_small, !unsigned_lit_small in Hc
      by (rewrite ?unsigned_lit_small by (unfold nsrc in *; lia); unfold nsrc in *; lia). apply Z.ltb_lt in Hc. unfold nsrc in Hc. lia. }
  paj_run_to_sh_x RUNTOPR HS HJi A_rig_outer.
  { stp_awr U33 EF fpos. }
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha Hn. rewrite (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(stp_nowr U33 Hn)).
    exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha ltac:(stp_nowr U33 Hn)). }
  assert (MGR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; apply (apresent_grows _ _ _ a HG0); apply (apresent_grows _ _ _ a HG); exact Hp).
  destruct (stp_keep cx (S i) F FL fpos ly1 S1 Hp1 W1 m1 md1 (ms_mem ms0) qd c2 O2 cap2 out2 spent HB HAR1 HF4096 HFceil
    HFapp HSP' MEQ MGR HROM HAPK HFR HLK HLS HGO) as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20]%bv HS HAE ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (14%bv : bv 5) N14.
  apply KO.
  lazymatch goal with |- RGO_xR _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst _ _ _ _) ?mdx) =>
    exists (ms_regs ms0), ly1, S1, (ms_mem ms0), mdx, k1, F, FL, qd, c2, O2, cap2, out2, spent end.
  split; [reflexivity|].
  split.
  { unfold gregs_base. unfold spZ. rewrite !HK by (cbv; tauto).
    split; [exact Rsp|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9 | exact R18]. }
  split; [rewrite HK by (cbv; tauto); exact R20|].
  split; [rewrite N21, E33; reflexivity|].
  split; [rewrite N22, E32; reflexivity|].
  split; [rewrite N14, U35; unfold w64; f_equal; lia|].
  split; [exact Hlt|].
  split; [exists fpos, Hp1; split; [|exact (conj K1 (conj K2 (conj K3 K4)))]|].
  { eapply ajournal_gx_pack_xR; [exact HSTK0 | exact HXO | exact HJi | exact Hag | intros a Ha; lia]. }
  exact (conj K5 K6).
- (* i + 1 >= g_nsrc: every entry done, the unlock *)
  assert (Hend : S i = length (gxes cx)).
  { cbn [branch_taken sv_denot] in Hc. rewrite U35, U36, Z.add_0_r, bv_lts_signed in Hc.
    rewrite !bv_signed_small, !unsigned_lit_small in Hc
      by (rewrite ?unsigned_lit_small by (unfold nsrc in *; lia); unfold nsrc in *; lia). apply Z.ltb_ge in Hc. unfold nsrc in Hc. lia. }
  paj_run_to_sh_x RUNTOPR HS HJi A_rig_unlock.
  { stp_awr U33 EF fpos. }
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 10) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha Hn. rewrite (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr0 a Ha ltac:(stp_nowr U33 Hn)).
    exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha ltac:(stp_nowr U33 Hn)). }
  assert (MGR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; apply (apresent_grows _ _ _ a HG0); apply (apresent_grows _ _ _ a HG); exact Hp).
  destruct (stp_keep cx (S i) F FL fpos ly1 S1 Hp1 W1 m1 md1 (ms_mem ms0) qd c2 O2 cap2 out2 spent HB HAR1 HF4096 HFceil
    HFapp HSP' MEQ MGR HROM HAPK HFR HLK HLS HGO) as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18]%bv HS HAE ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  prreg HS (21%bv : bv 5) N21.
  apply KU.
  lazymatch goal with |- RGU_xR _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst _ _ _ _) ?mdx) =>
    exists (ms_regs ms0), ly1, S1, (ms_mem ms0), mdx, k1, F, FL, qd, c2, O2, cap2, out2, spent end.
  split; [reflexivity|].
  split.
  { unfold gregs_base. unfold spZ. rewrite !HK by (cbv; tauto).
    split; [exact Rsp|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9 | exact R18]. }
  split; [rewrite N21, E33; reflexivity|].
  split; [exists fpos, Hp1; split; [|exact (conj K1 (conj K2 (conj K3 K4)))]|].
  { eapply ajournal_gx_pack_xR; [exact HSTK0 | exact HXO | exact HJi | exact Hag | intros a Ha; lia]. }
  rewrite <- Hend. exact K6.
Qed.

(* W_rig_step.v:655 stp_rgo_lt at R *)
Lemma stp_rgo_lt_xR : forall cx i W1 c1, RGO_xR B PST ARx MT RP MMAX RG R cx i W1 c1 -> (i < length (gxes cx))%nat.
Proof.
intros cx i W1 c1 HO.
destruct HO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent &
  _ & _ & _ & _ & _ & _ & Hi & _).
exact Hi.
Qed.

(* W_rig_step.v:663 rig_outer_proof at R *)
Theorem rig_outer_proof_xR : rig_outer_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
intros TOP KEY KEYS STEP.
assert (MAIN : forall n cx i W1 c1, (length (gxes cx) - i <= n)%nat ->
  GBASE B ARx MT RP MMAX RG cx -> GCTX CTX_AFREE cx -> RGO_xR B PST ARx MT RP MMAX RG R cx i W1 c1 ->
  (forall W2 c2, RGU_xR B PST ARx MT RP MMAX RG R cx W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
  YA0nH.SRrG SEGS R W1 c1 (gPOST_xR B PST ARx MT RP RG R cx)).
{ induction n as [|n IH]; intros cx i W1 c1 N HB HC HO HU.
  - pose proof (stp_rgo_lt_xR cx i W1 c1 HO). lia.
  - pose proof (stp_rgo_lt_xR cx i W1 c1 HO) as Hi.
    assert (NXT : forall W3 c3, RGE_xR B PST ARx MT RP MMAX RG R cx i W3 c3 ->
      YA0nH.SRrG SEGS R W3 c3 (gPOST_xR B PST ARx MT RP RG R cx)).
    { intros W3 c3 HE. apply (STEP cx i W3 c3 HB HE); [|exact HU].
      intros W4 c4 HO4. apply (IH cx (S i) W4 c4); [lia | exact HB | exact HC | exact HO4 | exact HU]. }
    apply (TOP cx i W1 c1 HB HO); [|exact NXT].
    intros r W2 c2 HI. exact (KEYS KEY cx i 0%nat r W2 c2 HB HC HI NXT). }
intros cx i W1 c1 HB HC HO HU. exact (MAIN _ cx i W1 c1 (le_n _) HB HC HO HU).
Qed.
End wR.

End c.
End b.
End a.
