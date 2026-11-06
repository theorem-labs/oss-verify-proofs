(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the MATCH segment of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_relay_remove_cx.v rr_match_stmt, RRM i 0x83f48 -> RRU (Some i) 0x83fc4), cut into four hops at three
   inner cut points, in the CPS form of the cx file.  The hops are proved in their own files (W_rr_m_drain.v,
   W_rr_m_ge.v, W_rr_m_free.v, W_rr_m_cpy.v); rr_match_of_hops composes them.

   Where it comes from (the retired lane form, commit 2ad36763b22, lib/A/Prog/relay_remove_p_c.v): the hop chain
   DRAIN rrA_at_found -> rrA_at_ge, GE -> rrA_at_free, FREE -> rrA_at_cpy, TAIL -> rrA_unlockT, WEAKEN ->
   rrA_at_unlock (Some i) and rrA_stage_c_of_hops.  Ported: the cut points and the order of the hops, and the
   composition by plain application.  New: the cuts over concrete machine states (W6: journal from the entry, the
   relay's bytes as garr8, blocks as one Permutation with the entry's `rest`, the meter as spent-so-far); the lane's
   touched sets T and the WEAKEN hop are not needed (W6's journal carries the footprint), so TAIL ends in RRU itself.

   INNER CUT POINTS (AF_fr_relay_remove = 0x1af8)
     RRG i  0x83f68  +0x184  after drain (eof = 0) or the eof test (eof <> 0): a0 := g_src + s8; jal gestures_end
     RRF i  0x83f74  +0x190  after gestures_end: the buf field's shadow check, ld a0,16(a1); jal free
     RRC i  0x83f98  +0x1b4  after free (s->buf): g_nsrc -= 1 (sw a2,-1864(s7)); __asan_memcpy (slot i, slot n-1, 56)

   HOPS
     hop_drain_stmt  RRM i -> RRG i   eof shadow check 0x83f4c-58 (0x84098-a8 not taken); eof = 0: drain (DRAIN)
     hop_ge_stmt     RRG i -> RRF i   gestures_end (GSE)
     hop_free_stmt   RRF i -> RRC i   buf shadow check 0x83f80-8c (0x840ac not taken); free (s->buf) (AFREE / AFREEN,
                     the _c rules: RCTX gives the free's caller context in CTX_AFREE)
     hop_cpy_stmt    RRC i -> RRU (Some i)   g_nsrc -= 1; __asan_memcpy (AMEMCPY, i < n-1; AMEMCPYS, i = n-1)

   Every inner cut carries RLIVE (the journal from the entry owning the fake frame), the registers MATCH reads
   (RMHD), and the relay / output / blocks as changed so far, in rr_found's own terms (rmdrel, rmc1 / rmO1 / rmcap1
   are rr_found's let-bindings, named), so that hop_cpy builds RDONE from RRC alone:
     RDONE's RLIVE                  every hop carries it; CPY re-establishes it after the g_nsrc store and memcpy
     i < |es|, re_fd (es[i]) = FD   RMHD, from RRM, unchanged
     mo_le S0 S (tr_cost (rtr cx))  FREE (RRC's meter, after the last free); CPY charges nothing
     g_s kept outside slot j        DRAIN (rmgs: dr_post's g_s clause after RHELD's); GE / FREE / CPY keep it
     rr_found:
       drain relation, asrc_at h1   DRAIN (rmdrel); GE / FREE / CPY move asrc_at
       sl_sends .. = (c2, O2, cap2) GE (gse_run as sl_sends); FREE / CPY carry it
       arelay_at .. (remove_at i es)  CPY, from RRC's rmtbl (g_src, g_capsrc, the table block, the bytes with
                                    slot i = X, the other entries' aentry_ok), the g_nsrc store and the copy;
                                    NoDup / length from RBASE by rm_remove_perm
       aout_at c2 O2 ..             GE; FREE / CPY move it
       entry Permutation            RBASE with rm_drains (no hop)
       final Permutation            FREE (RRC's Permutation, buf block gone); CPY keeps ablocks
   and RRU's registers (rregs_base, 0 <= FD) are RMHD's.  The meter at RRG is W_drain_cx.v's dbud form (spent so
   far, the rest of the trace fits), in C3's peak form for the rest (rr_spec's tr_max / tr_peak premises restated
   for it; C3 removed rr_spec's capacity premises, so rmbud no longer carries g_capout); RRF / RRC carry only what
   free and the end need. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (a Theorem Labs lane, lane RR_x): the hop interface
   over ANY allocator relation ARx (Section c is W_relay_remove_cx.v's generic block, verbatim).  The inner cuts'
   journal is RLIVE's ajournal_gx_x with the head set Hp1, and they carry the room budget: RRG rmbud's
   rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + kr) for the rest tl and gestures_end's count premise
   cnt_ok_pk RP gse_pk; RRF rp_RM RP S1 (1 + kr) (the buf free's 1) and the free's cnt_ok; RRC rp_RM RP S1 kr. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ list facts (statement-independent) *)
(* the first entry of fd is entry i when the fds are distinct (the lane's rrA_find_nth, relay_remove_p_bc.v:163) *)
Lemma rm_find : forall (es : list rentry) (i : nat) (FD : Z), List.NoDup (map re_fd es) -> (i < length es)%nat ->
  re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
  find (fun e => re_fd e =? FD) es = Some (nth i es relay_remove_b_c.no_entry).
Proof.
induction es as [|e es IH]; intros i FD HND Hi Hfd; cbn [length] in Hi; [lia|].
cbn [map] in HND. apply List.NoDup_cons_iff in HND as [Hn HND].
destruct i as [|i]; cbn [find nth] in *.
- rewrite Hfd, Z.eqb_refl. reflexivity.
- assert (He : re_fd e <> FD).
  { intros E. apply Hn. rewrite E, <- Hfd. apply in_map. apply nth_In. lia. }
  apply Z.eqb_neq in He. rewrite He. apply IH; [exact HND | lia | exact Hfd].
Qed.
Lemma rm_skipn_nth : forall {X : Type} (l : list X) (i : nat) (d : X), (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros X l. induction l as [|x l IH]; intros i d Hi; cbn [length] in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
(* remove_at i l is l without its entry i (the last entry moved into slot i) *)
Lemma rm_remove_perm : forall {X : Type} (l : list X) (i : nat) (d : X), (i < length l)%nat ->
  Permutation l (nth i l d :: relay_remove_b_c.remove_at i l).
Proof.
intros X l i d Hi. unfold relay_remove_b_c.remove_at.
destruct (rev l) as [|x r] eqn:Hr.
- apply (f_equal (@length X)) in Hr. rewrite length_rev in Hr. cbn [length] in Hr. lia.
- assert (Hl : l = rev r ++ [x]) by (rewrite <- (rev_involutive l), Hr; reflexivity).
  cbv zeta. rewrite Hl in Hi |- *. clear Hl Hr. revert Hi. generalize (rev r) as p. intros p Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.eqb_spec i (length p)) as [E|E].
  + rewrite app_nth2 by lia. rewrite E, Nat.sub_diag. cbn [nth].
    apply Permutation_sym, Permutation_cons_append.
  + assert (Hi' : (i < length p)%nat) by lia.
    rewrite app_nth1 by exact Hi'.
    assert (Hp : p = firstn i p ++ nth i p d :: skipn (S i) p).
    { rewrite <- (rm_skipn_nth p i d Hi'). symmetry. apply firstn_skipn. }
    transitivity ((firstn i p ++ nth i p d :: skipn (S i) p) ++ [x]); [rewrite <- Hp; reflexivity|].
    rewrite <- app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
    apply perm_skip. apply Permutation_app_head. apply Permutation_sym, Permutation_cons_append.
Qed.
Lemma rm_remove_length : forall {X : Type} (l : list X) (i : nat), (i < length l)%nat ->
  length (relay_remove_b_c.remove_at i l) = (length l - 1)%nat.
Proof.
intros X l i Hi. destruct l as [|d l']; [cbn in Hi; lia|].
pose proof (Permutation_length (rm_remove_perm (d :: l') i d Hi)) as HL. cbn [length] in HL |- *. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The inner cut points (W6 offsets from AF_fr_relay_remove = 0x1af8). ---- *)
Definition A_rr_ge : Z := AF_fr_relay_remove + 0x184.     (* 0x83f68, after drain / the eof test *)
Definition A_rr_free : Z := AF_fr_relay_remove + 0x190.   (* 0x83f74, after gestures_end *)
Definition A_rr_cpy : Z := AF_fr_relay_remove + 0x1b4.    (* 0x83f98, after free (s->buf) *)

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
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
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
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
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ---- The matched entry and what drain leaves of it: rr_found's let-bindings (W_contract.v), named. ---- *)
Definition rmSA (cx : rcx) (i : nat) : Z := rxG0 cx + AENT * Z.of_nat i.          (* &g_src[i] *)
Definition rmHA (cx : rcx) : Z := rg_s RG + ASRC * Z.of_nat (rxj cx).             (* &g_s[j] *)
Definition rmno (cx : rcx) : Z := Z.of_nat (length (rxO cx)).
Definition rmopen (cx : rcx) (i : nat) : bool := re_eof (rnth cx i) =? 0.
Definition rmlive (cx : rcx) (i : nat) : bool := rmopen cx i && dr_live (rxc cx) (rxh cx).
Definition rmc1 (cx : rcx) (i : nat) (ev : Z) : ctl := if rmopen cx i then dr_ctl (rxc cx) (rxh cx) ev else rxc cx.
Definition rmO1 (cx : rcx) (i : nat) (LB : list byte) : list byte := if rmlive cx i then rxO cx ++ LB else rxO cx.
Definition rmcap1 (cx : rcx) (i : nat) : Z :=
if rmlive cx i then drain_b_c.ds_ocap (dr_fin (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
else rxcap cx.
(* rr_found's first conjunct, at the current state: drain's relation and the harness source after (open), or the
   entry unchanged (eof <> 0) *)
Definition rmdrel (cx : rcx) (i : nat) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(e1 : rentry) (h1 : hsrc) (LB : list byte) : Prop :=
if rmopen cx i then
  dr_rel (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx) e1 h1 LB /\ asrc_at B ly1 S1 W1 m1 (rmHA cx) h1
else e1 = rnth cx i.

(* ---- rr_tr at the matched entry, in its three parts (W_contract.v rr_tr's Some branch, verbatim). ---- *)
Definition rms (cx : rcx) (i : nat) : drain_b_c.dstate :=
if rmopen cx i then dr_fin (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)
else drain_b_c.drain_init (rmno cx) (rxcap cx) (rnth cx i) (rxh cx).
(* drain's own trace (dr_spec's dr_tr), when open *)
Definition rmtrD (cx : rcx) (i : nat) : list (RelayRunT.rev YO0i.sptr) :=
if rmopen cx i then dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx) else [].
(* gestures_end's key run *)
Definition rmtrK (cx : rcx) (i : nat) : list (RelayRunT.rev YO0i.sptr) :=
fst (keys_end_run (sl_live (rxc cx) 1) (rxmx cx) (drain_b_c.ds_no (rms cx i)) (drain_b_c.ds_ocap (rms cx i))
       (map (fun x => (Z.of_nat (length x), drain_b_c.da_out drain_b_c.dadr0)) (drain_b_c.ds_H (rms cx i))) 0%nat
       (drain_b_c.da_out drain_b_c.dadr0)).
(* the free of the held array, then of s->buf (both always: the callees charge free (NULL)) *)
Definition rmtrF (cx : rcx) (i : nat) : list (RelayRunT.rev YO0i.sptr) :=
[RelayRunT.RFree (drain_b_c.ds_ka (rms cx i)) (drain_b_c.da_out drain_b_c.dadr0);
 RelayRunT.RFree (drain_b_c.ds_cap (rms cx i)) (drain_b_c.da_out drain_b_c.dadr0)].

(* ---- The relay's table with slot i holding the 56 bytes X; the other entries as at the entry. ---- *)
Definition rmTpre (cx : rcx) (i : nat) : list byte := concat (map entry_bytes (firstn i (rxes cx))).
Definition rmTpost (cx : rcx) (i : nat) : list byte := concat (map entry_bytes (skipn (S i) (rxes cx))).
Definition rmtbl (cx : rcx) (i : nat) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(X : list byte) : Prop :=
val_mem SEGS (arm W1 m1) (rg_src RG) 8 (rxG0 cx) /\ awr W1 m1 (rg_src RG) 8 /\
val_mem SEGS (arm W1 m1) (rg_nsrc RG) 4 (rN cx) /\ awr W1 m1 (rg_nsrc RG) 4 /\
val_mem SEGS (arm W1 m1) (rg_capsrc RG) 4 16 /\ awr W1 m1 (rg_capsrc RG) 4 /\
In (rxG0 cx, ATABLE) (ablocks B ly1 S1) /\
Z.of_nat (length X) = AENT /\
(exists tail, Z.of_nat (length tail) = ATABLE - AENT * rN cx /\
   garr8 SEGS (arm W1 m1) (rxG0 cx) (bzs (rmTpre cx i ++ X ++ rmTpost cx i ++ tail))) /\
awr W1 m1 (rmSA cx i) AENT /\
Forall (aentry_ok B ly1 S1 W1 m1) (relay_remove_b_c.remove_at i (rxes cx)).

(* ---- The live blocks: the other entries', the harness source's (open), g_out's, the entry's rest. ---- *)
Definition rmOB (cx : rcx) (i : nat) : list (Z * Z) := concat (map aentry_blks (relay_remove_b_c.remove_at i (rxes cx))).
Definition rmsrc (cx : rcx) (i : nat) (h1 : hsrc) : list (Z * Z) := if rmopen cx i then asrc_blks h1 else [].
Definition rmbuf (e : rentry) : list (Z * Z) := if re_cap e =? 0 then [] else [(re_buf e, re_cap e)].

(* ---- g_s as at the entry outside drain's slot j (RDONE's clause, verbatim). ---- *)
Definition rmgs (cx : rcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
  (rr_drains (rxFD cx) (rxes cx) = true -> ~ (rmHA cx <= a < rmHA cx + ASRC)) ->
  abyte_kept (rxW cx) (rxmem cx) W1 m1 a.

(* ---- The meter after drain (W_drain_cx.v dbud, with rr_spec's room premises in C3's peak form for the rest tl):
   `spent` charged so far, the rest of the trace fits; the room round: the room the rest charges at the counting
   meter, then rr_post_x's kr. ---- *)
Definition rmbud (cx : rcx) (S1 : astate) (spent : Z) (tl : list (RelayRunT.rev YO0i.sptr)) : Prop :=
mo_le MT (rxS cx) S1 spent /\ 0 <= spent /\
spent + tr_cost MT tl <= tr_cost MT (rtr cx) /\
tr_max tl < MMAX /\
blocks_bytes S1 + tr_peak tl <= LIVE_MAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + rxkr cx).

(* ---- The registers MATCH reads (RRM's): the held set, s9 = g_src's register image, s8 = 56 i; and entry i. ---- *)
Definition RMHD (cx : rcx) (i : nat) (regs1 : bvmap 5 word) (F : Z) : Prop :=
rregs_held RG cx regs1 F /\
getr regs1 25 = w64 (rg_src RG + RR_HI_SRC) /\ getr regs1 24 = w64 (AENT * Z.of_nat i) /\
0 <= rxFD cx /\ (i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx.

(* ---- The inner cut predicates. ---- *)

(* RRG i (0x83f68): entry i drained when open (e1, h1, the lines LB, errno ev), not yet ended.  Slot i holds e1
   (aentry_ok, writable), the stream is drain's (rr_found's c1 / O1 / cap1) at g_out = out1, the blocks are e1's,
   the others', h1's (open), out1's and the entry's rest; spent = what drain charged.  The room round: rmbud's budget
   and gestures_end's count premise (gse_pk) at the current blocks. *)
Definition RRG (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (out1 spent : Z),
c1 = cfg_at SEGS (BASE + A_rr_ge) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
aentry_ok B ly1 S1 W1 m1 e1 /\
rmtbl cx i ly1 S1 W1 m1 (entry_bytes e1) /\
aout_at B RG ly1 S1 W1 m1 (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) out1 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks (rmcap1 cx i) out1 ++ rxrest cx) /\
rmgs cx W1 m1 /\
rmbud cx S1 spent (rmtrK cx i ++ rmtrF cx i) /\
cnt_ok_pk RP gse_pk (ablocks B ly1 S1).

(* RRF i (0x83f74): e1's keys ended (gestures_end): slot i holds entry_cleared e1, the stream is rr_found's
   (c2, O2, cap2) at g_out = out2, the blocks lost gse_blks e1 (e1's buffer block, if any, is left); what is left
   to charge is the buf free (the room round: its 1, then kr; the free's count premise at the current blocks). *)
Definition RRF (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte)
  (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z),
c1 = cfg_at SEGS (BASE + A_rr_free) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
length (re_pad1 e1) = 4%nat /\ length (re_pad2 e1) = 4%nat /\
((re_cap e1 = 0 /\ re_buf e1 = 0) \/ 0 < re_cap e1) /\
rmtbl cx i ly1 S1 W1 m1 (entry_bytes (entry_cleared e1)) /\
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) /\
rmgs cx W1 m1 /\
mo_le MT (rxS cx) S1 spent /\ spent + mo_free MT <= tr_cost MT (rtr cx) /\
rp_RM RP S1 (1 + rxkr cx) /\ cnt_ok RP (ablocks B ly1 S1).

(* RRC i (0x83f98): s->buf freed: slot i holds some 56 bytes X, the blocks are rr_found's final ones, the whole
   trace charged (the room round: kr left).  Everything rr_found / RDONE needs except the table count and the copy. *)
Definition RRC (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte)
  (c2 : ctl) (O2 : list byte) (cap2 out2 : Z) (X : list byte),
c1 = cfg_at SEGS (BASE + A_rr_cpy) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
rmtbl cx i ly1 S1 W1 m1 X /\
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) /\
rmgs cx W1 m1 /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
rp_RM RP S1 (rxkr cx).

(* ---- The hop statements (rr_match_stmt's CPS form). ---- *)

(* DRAIN: RRM i 0x83f48 -> the eof field's shadow check 0x83f4c-0x83f58 (0x84098-0x840a8 not taken), lw eof
   0x83f5c; eof <> 0: bnez to 0x83f68; eof = 0: jal drain 0x83f64 (DRAIN at BASE + AF_fr_drain, ra 0x83f68)
   -> RRG i. *)
Definition hop_drain_stmt : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRM B PST ARx MT RP RG cx i W1 c1 ->
(forall W2 c2, RRG cx i W2 c2 -> SRr SEGS W2 c2 (rPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (rPOST B PST ARx MT RP RG cx).

(* GE: RRG i 0x83f68 -> ld a0, g_src; add a0,a0,s8; jal gestures_end 0x83f70 (GSE, ra 0x83f74) -> RRF i. *)
Definition hop_ge_stmt : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRG cx i W1 c1 ->
(forall W2 c2, RRF cx i W2 c2 -> SRr SEGS W2 c2 (rPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (rPOST B PST ARx MT RP RG cx).

(* FREE: RRF i 0x83f74 -> ld a1, g_src; add a1,a1,s8; the buf field's shadow check 0x83f80-0x83f8c (0x840ac not
   taken); ld a0,16(a1); jal free 0x83f94 (AFREE, cap > 0; AFREEN, s->buf = NULL; ra 0x83f98) -> RRC i.  The _c free
   rules ask the call's context (ra 0x83f98, then relay_remove's return and chain) in CTX_AFREE: rr_spec's RCTX. *)
Definition hop_free_stmt : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RCTX CTX_AFREE cx -> RRF cx i W1 c1 ->
(forall W2 c2, RRC cx i W2 c2 -> SRr SEGS W2 c2 (rPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (rPOST B PST ARx MT RP RG cx).

(* CPY: RRC i 0x83f98 -> g_src, g_nsrc; g_nsrc -= 1 (sw a2,-1864(s7), HH59); a0 = &g_src[i], a1 = &g_src[n-1],
   a2 = 56; jal __asan_memcpy 0x83fc0 (AMEMCPY, i < n-1; AMEMCPYS, i = n-1; ra 0x83fc4) -> RRU (Some i). *)
Definition hop_cpy_stmt : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRC cx i W1 c1 ->
(forall W2 c2, RRU B PST ARx MT RP RG cx (Some i) W2 c2 -> SRr SEGS W2 c2 (rPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (rPOST B PST ARx MT RP RG cx).

(* ---- MATCH from its hops (the lane's rrA_stage_c_of_hops, relay_remove_p_c.v:211). ---- *)
Theorem rr_match_of_hops :
hop_drain_stmt -> hop_ge_stmt -> hop_free_stmt -> hop_cpy_stmt -> rr_match_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
intros HD HGE HF HC cx i W1 c1 HB HCT HM KU.
apply (HD cx i W1 c1 HB HM). intros W2 c2 H2.
apply (HGE cx i W2 c2 HB H2). intros W3 c3 H3.
apply (HF cx i W3 c3 HB HCT H3). intros W4 c4 H4.
exact (HC cx i W4 c4 HB H4 KU).
Qed.

(* ---- Entry facts every hop may use (statement-independent of the hops). ---- *)
Lemma rm_base_nodup : forall cx, RBASE B ARx MT RP MMAX RG cx -> List.NoDup (map re_fd (rxes cx)).
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND & _). exact (proj1 (stdpp.base.NoDup_ListNoDup _) HND).
Qed.
(* arelay_at's twelfth conjunct for the table after the move (W8's 42f5184c7ab): the entries of remove_at i es are
   entries of es, so none of their blocks is the table *)
Lemma rm_base_notab : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  Forall (fun e => forall b, In b (aentry_blks e) -> b <> (rxG0 cx, ATABLE)) (relay_remove_b_c.remove_at i (rxes cx)).
Proof.
intros cx i HB Hi. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNT).
pose proof (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi) as HP.
apply List.Forall_forall. intros e He. apply (proj1 (List.Forall_forall _ _) HNT).
eapply Permutation_in; [exact (Permutation_sym HP) | right; exact He].
Qed.
(* the entry's drain test is entry i's eof test *)
Lemma rm_drains : forall cx i, List.NoDup (map re_fd (rxes cx)) -> 0 <= rxFD cx -> (i < length (rxes cx))%nat ->
  re_fd (rnth cx i) = rxFD cx -> rr_drains (rxFD cx) (rxes cx) = rmopen cx i.
Proof.
intros cx i HND HFD Hi Hfd. unfold rr_drains. rewrite (rm_find (rxes cx) i (rxFD cx) HND Hi Hfd).
replace (0 <=? rxFD cx) with true by (symmetry; apply Z.leb_le; exact HFD). reflexivity.
Qed.
(* the request trace is drain's, then the key run, then the two frees *)
Lemma rm_tr_split : forall cx i, List.NoDup (map re_fd (rxes cx)) -> 0 <= rxFD cx -> (i < length (rxes cx))%nat ->
  re_fd (rnth cx i) = rxFD cx -> rtr cx = rmtrD cx i ++ rmtrK cx i ++ rmtrF cx i.
Proof.
intros cx i HND HFD Hi Hfd. unfold rtr, rr_tr.
rewrite (rm_find (rxes cx) i (rxFD cx) HND Hi Hfd).
replace (rxFD cx <? 0) with false by (symmetry; apply Z.ltb_ge; exact HFD).
reflexivity.
Qed.
(* the trace measures over a concatenation *)
Lemma rm_tr_cost_app : forall {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof. intros P t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.
(* ... at any meter (the room round's counting meter MT_rk) *)
Lemma rm_tr_cost_app_m : forall (M : ameter_ops) {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_cost M (t1 ++ t2) = tr_cost M t1 + tr_cost M t2.
Proof. intros M P t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.
Lemma rm_tr_max_nonneg : forall {P : Type} (t : list (RelayRunT.rev P)), 0 <= tr_max t.
Proof. intros P t. unfold tr_max. induction t as [|ev t IH]; cbn [fold_right]; [lia|]. destruct ev; cbv beta iota; lia. Qed.
Lemma rm_tr_max_app : forall {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros P t1 t2. pose proof (rm_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; cbn [app fold_right]; [lia|].
destruct ev; cbv beta iota; rewrite IH; lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the inner cut predicates and the hop statements at a world relation R, over
   the same generic ARx.  W_relay_remove_cx.v's journal predicates and post become their _xR twins (RLIVE_xR, RRM_xR,
   RRU_xR, rPOST_xR: R after RG), SRr SEGS -> YA0nH.SRrG SEGS R; rmSA .. RMHD and the rm_* lemmas carry no journal and
   no step relation, so they are shared.  Names: X -> X_xR.  At R := wle each is the strict text above (X_wle). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :316 RRG *)
Definition RRG_xR (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (out1 spent : Z),
c1 = cfg_at SEGS (BASE + A_rr_ge) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
aentry_ok B ly1 S1 W1 m1 e1 /\
rmtbl cx i ly1 S1 W1 m1 (entry_bytes e1) /\
aout_at B RG ly1 S1 W1 m1 (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) out1 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks (rmcap1 cx i) out1 ++ rxrest cx) /\
rmgs cx W1 m1 /\
rmbud cx S1 spent (rmtrK cx i ++ rmtrF cx i) /\
cnt_ok_pk RP gse_pk (ablocks B ly1 S1).
(* :334 RRF *)
Definition RRF_xR (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte)
  (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z),
c1 = cfg_at SEGS (BASE + A_rr_free) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
length (re_pad1 e1) = 4%nat /\ length (re_pad2 e1) = 4%nat /\
((re_cap e1 = 0 /\ re_buf e1 = 0) \/ 0 < re_cap e1) /\
rmtbl cx i ly1 S1 W1 m1 (entry_bytes (entry_cleared e1)) /\
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) /\
rmgs cx W1 m1 /\
mo_le MT (rxS cx) S1 spent /\ spent + mo_free MT <= tr_cost MT (rtr cx) /\
rp_RM RP S1 (1 + rxkr cx) /\ cnt_ok RP (ablocks B ly1 S1).
(* :354 RRC *)
Definition RRC_xR (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte)
  (c2 : ctl) (O2 : list byte) (cap2 out2 : Z) (X : list byte),
c1 = cfg_at SEGS (BASE + A_rr_cpy) regs1 m1 md1 /\
RMHD cx i regs1 F /\
RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
rmdrel cx i ly1 S1 W1 m1 e1 h1 LB /\
rmtbl cx i ly1 S1 W1 m1 X /\
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) /\
rmgs cx W1 m1 /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
rp_RM RP S1 (rxkr cx).
(* :375 hop_drain_stmt *)
Definition hop_drain_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRM_xR B PST ARx MT RP RG R cx i W1 c1 ->
(forall W2 c2, RRG_xR cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR B PST ARx MT RP RG R cx).
(* :382 hop_ge_stmt *)
Definition hop_ge_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRG_xR cx i W1 c1 ->
(forall W2 c2, RRF_xR cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR B PST ARx MT RP RG R cx).
(* :391 hop_free_stmt *)
Definition hop_free_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RCTX CTX_AFREE cx -> RRF_xR cx i W1 c1 ->
(forall W2 c2, RRC_xR cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR B PST ARx MT RP RG R cx).
(* :399 hop_cpy_stmt *)
Definition hop_cpy_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE B ARx MT RP MMAX RG cx -> RRC_xR cx i W1 c1 ->
(forall W2 c2, RRU_xR B PST ARx MT RP RG R cx (Some i) W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR B PST ARx MT RP RG R cx).
(* :406 rr_match_of_hops *)
Theorem rr_match_of_hops_xR :
hop_drain_stmt_xR -> hop_ge_stmt_xR -> hop_free_stmt_xR -> hop_cpy_stmt_xR -> rr_match_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
intros HD HGE HF HC cx i W1 c1 HB HCT HM KU.
apply (HD cx i W1 c1 HB HM). intros W2 c2 H2.
apply (HGE cx i W2 c2 HB H2). intros W3 c3 H3.
apply (HF cx i W3 c3 HB HCT H3). intros W4 c4 H4.
exact (HC cx i W4 c4 HB H4 KU).
Qed.
End wR.
(* the strict texts are the R texts at R := wle (by conversion) *)
Lemma RRG_wle : RRG = RRG_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RRF_wle : RRF = RRF_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RRC_wle : RRC = RRC_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma hop_drain_stmt_wle : hop_drain_stmt = hop_drain_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma hop_ge_stmt_wle : hop_ge_stmt = hop_ge_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma hop_free_stmt_wle : hop_free_stmt = hop_free_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma hop_cpy_stmt_wle : hop_cpy_stmt = hop_cpy_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.
