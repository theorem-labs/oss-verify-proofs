(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* relay_finish at 0x82344 (image B; 0x822ec in A), 80 instructions, frame 48 (ra, s0-s4 saved), NO ASan fake frame
   (B never calls __asan_stack_malloc here, so A's ASMERR / ASMX question does not arise):
     0x82344  prologue; s0 = the shadow base SB (GOT slot A_OBJ 0 -> cell A_OBJ 30); lbu g_thread_up; beqz -> 0x8239c
              (rf_spec gives the byte 0: the wake / pthread_join arm 0x82378..0x82398 is never run)
     0x8239c  pthread_mutex_lock (&g_lock)                       (Section hypothesis ALOCK, aj_gx_entry_at)
     0x823a8  lw g_nsrc; blez -> the tail X (0x8243c), else s2 = 0, s3 = 0 and the loop L (0x823c0)
     0x823c0  L: g_src, p = g_src + 56 i and B's UBSan checks of p, the load8 check of &s->buf, free (s->buf)
              (AFREE / AFREE0), g_src again, the checks again, gestures_end (s) (GSE), lw g_nsrc, i++, blt -> L
     0x8243c  X: g_client = -1, g_listen = -1, g_nsrc = 0, the epilogue, and the TAIL CALL `j pthread_mutex_unlock`
              (AUNLOCK, aj_gx_entry_at at the caller's sp: the unlock returns to relay_finish's caller).
   The seven UBSan trap edges (all to `unimp` at 0x8247c; TRAPS-ALL.md (sha256 c90982171c9b; internal record) rows 81-87): 0x823c8 `bltu a1,a0`
   (p <u g_src) is refuted by W_traps.v trap_ptr_wrap_atom; the runner decides the other six from the loop seat's
   facts (W_traps.v recipe R1/R2: atom 32 = g_src and atom 33 = p, pointer facts, both sums s2 + g_src aliased to
   atom 33) and from the condition 0x823c8 adds (0x82414).  The one __asan_report_load8 exit (0x82480) is decided
   by the shadow entry rfl_SH. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
(* the room round's count names: acnt / acnt_app / acnt_perm from lib/B/ReplyCnt.v, Required and named qualified;
   acnt_nil / acnt_cons are W_journal_x.v's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YC80xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma zseps_from_In : forall b l c, zseps_from b l -> In c l -> fst b + snd b <= fst c \/ fst c + snd c <= fst b.
Proof.
intros b l c. induction l as [|x l IH]; cbn; [tauto|]. intros [Hx Hl] [<- | Hc]; [exact Hx | exact (IH Hl Hc)].
Qed.
Lemma zseps_nth : forall l i j a b, zseps l -> (i < j)%nat -> nth_error l i = Some a -> nth_error l j = Some b ->
fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Proof.
induction l as [|x l IH]; intros i j a b Hs Hij Ha Hb; [destruct i; discriminate|].
destruct Hs as [Hx Hl]. destruct i as [|i].
- cbn in Ha. injection Ha as <-. destruct j as [|j]; [lia|]. cbn in Hb.
  exact (zseps_from_In x l b Hx (nth_error_In l j Hb)).
- destruct j as [|j]; [lia|]. cbn in Ha, Hb. exact (IH i j a b Hl ltac:(lia) Ha Hb).
Qed.
Ltac zsep_pick H i j D := pose proof (zseps_nth _ i j _ _ H ltac:(lia) eq_refl eq_refl) as D; cbn [fst snd] in D.
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* ---- LX0, the laws at ARi0 (W_journal_x.v), from AR_laws.  The AR theorem pb_relay_finish keeps its Section
   hypothesis LAWS : AR_laws, and pb_relay_finish_fr its premise AR_laws SEGS TB; Section cAR derives LX0 from it here.
   The text is lib/B/YLX0.v's (a working branch 77dce911cd1, the B twin of lib/A/W_laws_x.v AR_laws_x_ARi0_of),
   which this kit does not carry: Reusable/YCbqG.v AR_laws_x_of_AR takes three facts of cgif's AR beyond AR_laws - the
   8-aligned stack bounds (layout_ok's lo_top), a live block's tail granule viewable, and the const cells (am_const). *)
Section rf_lx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0s.
Lemma rf_lx_in_zseq : forall lo n a, lo <= a < lo + n -> In a (YG0n.zseq lo n).
Proof.
intros lo n a H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split.
- rewrite Z2Nat.id by lia. lia.
- apply in_seq. lia.
Qed.
Lemma rf_lx_cls8 : forall c, 1 <= c <= 30 -> class_size c mod 8 = 0.
Proof.
intros c Hc.
assert (A : forallb (fun c => class_size c mod 8 =? 0) (YG0n.zseq 1 30) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply rf_lx_in_zseq. lia.
Qed.
Lemma rf_lx_ext8 : forall (B : asyms) ly S k, cfacts B ly S k -> ck_extent k mod 8 = 0.
Proof.
intros B ly S k (_ & _ & _ & _ & _ & _ & _ & _ & G9).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct G9].
- cbv beta iota zeta in G9. destruct G9 as (Hc & _ & _ & He & _). rewrite He. apply rf_lx_cls8. exact Hc.
- cbv beta iota in G9. destruct G9 as (_ & _ & _ & He & _). rewrite He. unfold sec_map_size, round_up, kPage.
  assert (E : forall q, (q * 4096 + 4096 - 4096) mod 8 = 0)
    by (intros q; replace (q * 4096 + 4096 - 4096) with (q * 512 * 8) by lia; apply Z.mod_mul; lia).
  apply E.
Qed.
Lemma rf_lx_alloc_tail : forall (segs : list Segment) (B : asyms) ly S (W : world segs) mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S W mem md p n a HAR Hin Ha.
destruct HAR as (HM & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (chunk_facts B ly S _ k HM Hk) as CF.
pose proof (rf_lx_ext8 B ly S k CF) as E8.
destruct CF as (_ & _ & G3 & G4 & _ & _ & _ & G8 & _).
assert (HJ : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
{ unfold ajunk. right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_junk.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ HM) _ HJ) as V.
unfold range_vis in V. cbn [fst snd] in V.
rewrite aeval_aoff in V by (intros e' Ee; destruct (ck_beg k); cbn in Ee; discriminate Ee).
change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
unfold ck_n in V. rewrite <- Hu, G4, <- Hr in Ha.
pose proof (Z.div_mod (ck_base B ly k) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (ck_extent k) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D4.
specialize (V (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k))))).
replace (ck_base B ly k + (ck_rz k + req_size (ck_req k)) + (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k)))))
  with a in V by lia.
apply V. lia.
Qed.
Lemma rf_lx_stk8 : forall segs B ly S W mem md, AR segs B ly S W mem md -> ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0.
Proof.
intros segs B ly S W mem md (HM & _).
pose proof (lo_top _ (am_layout _ _ _ _ HM)) as (_ & _ & _ & _ & H1 & H2 & _).
unfold page_aligned in H1, H2. try unfold page_size in H1, H2.
assert (D : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->].
  replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
split; apply D; assumption.
Qed.
Lemma rf_lx_tail : forall segs B ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < (p + req_size n + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S W mem md p n a HAR Hin Ha.
apply (rf_lx_alloc_tail segs B ly S W mem md p n a HAR Hin).
assert (E : (p + req_size n + 7) / 8 * 8 = p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8).
{ replace (p + req_size n + 7) with (p + req_size n - 1 + 1 * 8) by lia.
  rewrite Z.div_add by lia. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma rf_lx_const : forall segs B ly S W mem md, AR segs B ly S W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Proof. intros segs B ly S W mem md (HM & _). exact (am_const _ _ _ _ HM). Qed.
Lemma rf_lx_AR_laws_x_ARi0_of : forall segs B, AR_laws segs B ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbqG.AR_laws_x segs B (W_journal_x.ARi0 segs B) 0.
Proof.
intros segs B L.
exact (W_journal_x.AR_laws_x_ARi0 segs B
  (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbqG.AR_laws_x_of_AR segs B L
     (rf_lx_stk8 segs B) (rf_lx_tail segs B) (rf_lx_const segs B))).
Qed.
End rf_lx.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_relay_finish : Z := AF_fr_relay_finish.
Definition A_relay_finishP : Z := BASE + A_relay_finish.
Section c.
(* ---- THE GENERIC WALK: relay_finish over any allocator relation ARx with its laws, stated as W_contract_x.v
   rf_spec_x with the room round's roomp RP after MT.  The Section hypotheses beyond the AR walk's: PST / ARx / hl /
   LAWS (the generic relation); HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: W_journal_x.v Section hp0,
   for range_addressable_of_block_hp0_x); BLKN; and two facts on the program statics PST (PSTR / PSTC below). ---- *)
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
(* the allocator rules' caller-context table (W_journal_x.v Section hc), rf_spec_x's last Section variable *)
Variable CTX : list (list Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* a live block's size is non-negative (W_kit_x.v's BLKN: AR_blocks_law's last conjunct, which AR_laws_x's
   alx_blocks does not state) *)
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
(* the allocator's free rules in their caller-context `_c` forms with the room round's RP (W_journal_x.v Section hc,
   afree_cf_rule_c_x / afree_null_cf_rule_c_x): the free at 0x82408 returns to 0x8240c = relay_finish + 200, and B
   keeps no frame pointer, so its context is the one-entry trace [pc + 200] rf_spec_x's premise puts in CTX *)
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREE0 : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* the internal callee, W4's published statement (W_contract_x.v's twin) *)
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* ---- the placement of the globals relay_finish reads and writes: by the object the listing names (PLdHi / PAddHi),
   and - for a store through an auipc register - by the hi slot and the store's immediate:
   HV1: the g_thread_up test 0x8236c; HV3: a0 = &g_lock at 0x823a0 and 0x82454; HV4: the g_nsrc loads 0x823ac and
   0x8242c; HV5: the g_src loads 0x823c0 and 0x8240c; HH5: the g_nsrc store 0x82458 through the kept s1; HH7, HH8:
   the g_client store 0x82444 and the g_listen store 0x8244c.  The rest are A's (lib/A/W_relay_finish_h.v), with
   image B's band [0x10000, 0x5fc000) and B's own runtime cells (GOT slot A_OBJ 0 and shadow cell A_OBJ 30) in HSEPG:
   HIG / HSEPG (region_ok, pairwise_disjoint, the carries), HPLAIN (the image clause of every call's frame),
   HWSEG / RGAL (alock_at's awr, the stores' windows, musl's mutex alignment), HIGO / HSEPO / HPLAINO (aout_at's cells
   across the stores and the free), HROMG / HE5R / HROMO (rom_view across the stores, the free and gestures_end),
   HWSEGE (errno writable after a free).  NO gx_rt: rf_spec puts G_SL, which holds errno, inside G. ---- *)
Hypothesis HV1 : VAL (A_OBJ 1) = GTU.
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HH5 : VAL (A_HI 5) + (-1672) = rg_nsrc RG.
Hypothesis HH7 : VAL (A_HI 7) + 292 = rg_client RG.
Hypothesis HH8 : VAL (A_HI 8) + 248 = GL.
Hypothesis HIG : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 30), 8);
 (GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (as_errno B, 4)].
Definition rf_cells : list (Z * Z) :=
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HPLAIN : forall a, inG rf_cells a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HWSEG : forall a, inG rf_cells a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis RGAL : rg_lock RG mod 4 = 0.
Hypothesis HIGO : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1)].
Hypothesis HSEPO : zseps
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1); (as_errno B, 4);
 (rg_src RG, 8); (rg_capsrc RG, 4)].
Hypothesis HPLAINO : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HROMG : forall a,
inG (RF_G RG GL) a \/ inG (G_SL B RG) a \/
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ in_rom SEGS a.
Hypothesis HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + Z.of_nat (length END5) -> in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HWSEGE : forall a, as_errno B <= a < as_errno B + 4 ->
wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (Reusable/YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x after gestures_end) and no byte of
   rf_cells (the prologue's and gestures_end's image clauses).  At PST := [] both hold trivially. *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTC : forall a, inG rf_cells a -> ~ Exists (in_zr a) PST.
Lemma rf_writable_of_seg : forall (H : word -> bool) (m : word -> option byte) a,
H (Z_to_bv 64 a) = false -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a Hh Hw. unfold writable_at, mrestrict, wview in *. rewrite Hh.
destruct (m (Z_to_bv 64 a)) as [b|]; [cbv iota; discriminate | exact Hw].
Qed.
Lemma in_rf_cell : forall i lo n x, nth_error rf_cells i = Some (lo, n) -> lo <= x < lo + n -> inG rf_cells x.
Proof.
intros i lo n x Hn Hx. unfold inG. apply Exists_exists. exists (lo, n).
split; [exact (nth_error_In _ i Hn) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the plain token runner on the donor journal ajournal_x (W_kit.v paj_run's text over Reusable/YC80x.v) *)
Let RUN0 := SRr_run_pi_tok_AJx (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr).
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 ([] : list (Z * Z)).
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 ([] : list (Z * Z)).
Let BR := paj_branch (PI := PI).
Definition Bx : sv := SOff 32 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gtu_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 1)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rf_regions0 : smem := [ stack_region RF_FRAME; got_regionP; bcell_regionP 32; gtu_region ].
Definition rf_facts0 : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rf0 : sstate := mkSS A_relay_finish sr_atoms rf_regions0 None rf_facts0.
Definition rf_SH0 : list shent := [].
Definition rf_extra : list word := map (Z_to_bv 64) [SB].
(* the six callee-saved words the prologue wrote into the frame, by rising address: s4 at sp0 - 48, s3, s2, s1, s0,
   ra at sp0 - 8 *)
Definition RF_SAVED : list (bv 5) := [20; 19; 18; 9; 8; 1]%bv.
Definition rf_saved (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regsE : bvmap 5 word) : Prop :=
forall i, (i < 6)%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 48 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i RF_SAVED 0%bv))).
(* a frame word written from register r reads back as r's entry value *)
Lemma rf_saved_word : forall E m sp0 lo hi wlo whi cs (r : bv 5) (n : nat) od regs extra,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs -> Z.of_nat n = bv_unsigned r -> env_agree 32 (Ereg regs extra) E ->
(n < 32)%nat ->
val_mem SEGS m (sp0 + od) 8 (bv_unsigned (getr regs r)).
Proof.
intros E m sp0 lo hi wlo whi cs r n od regs extra HR Hsp Hin Hn [HA _] Hn32.
apply (field_of_region E m 2 sp0 cs lo hi wlo whi od 8%N (SOff n 0) _ HR Hsp Hin).
- cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. rewrite (HA n Hn32). apply ew_Ereg_nat. exact Hn.
- exact (bv_unsigned_in_range 64 _).
- lia.
Qed.
Lemma rf_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch ->
val_mem SEGS (arm W mem) GTU 1 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs rf_extra)) ss_rf0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_finishP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx rf_SH0 (Eimg (Ereg regs rf_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE HGTU0.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16672) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
zsep_pick HSEPG 0%nat 2%nat D1. zsep_pick HSEPG 1%nat 2%nat D2.
pose proof (proj1 (Forall_forall _ _) HIG (GTU, 1) ltac:(left; reflexivity)) as HGTUb. cbn [fst snd] in HGTUb.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs rf_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 31)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pal_got_cell B TL) as HgcD.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 31)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_rf0, A_relay_finishP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rf_regions0, stack_region, got_regionP, bcell_regionP, gtu_region, RF_FRAME;
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite (EO 30%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VBO 30%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VBO 1%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, HV1. exact HGTU0.
  + apply pairwise_disjoint_of_extents.
    unfold rf_regions0, stack_region, got_regionP, bcell_regionP, gtu_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VBO 0%nat ltac:(lia)), (VBO 1%nat ltac:(lia)), (VBO 30%nat ltac:(lia)). cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HV1.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HgcD HGTUb D1 D2. clear.
    unfold RF_FRAME, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rf_SH0. constructor.
Qed.
(* ---- The two cut points: the loop head L (0x823c0 = relay_finish + 0x7c) and the tail X (0x8243c = + 0xf8). ---- *)
Definition A_rf_loop : Z := AF_fr_relay_finish + 0x7c.
Definition A_rf_tail : Z := AF_fr_relay_finish + 0xf8.
(* a default entry, for nth *)
Definition rf_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
(* the registers both cut points keep from the entry: sp (the frame below it), gp, tp, the seven callee-saved
   registers relay_finish never touches, and the kept auipc register s1 of g_nsrc (the tail's store goes through it) *)
Definition rf_kept (regs regsX : bvmap 5 word) (sp0 : Z) : Prop :=
spZ regsX = sp0 - 48 /\
getr regsX 3 = getr regs 3 /\ getr regsX 4 = getr regs 4 /\
getr regsX 21 = getr regs 21 /\ getr regsX 22 = getr regs 22 /\ getr regsX 23 = getr regs 23 /\
getr regsX 24 = getr regs 24 /\ getr regsX 25 = getr regs 25 /\ getr regsX 26 = getr regs 26 /\
getr regsX 27 = getr regs 27 /\ getr regsX 9 = w64 (VAL (A_HI 5)).
(* The relay's cells when the loop is done: g_src and g_capsrc are as relay_finish found them (it writes
   neither), the table block is still live, and g_nsrc - the only one of them the tail writes - is writable. *)
Definition rf_done (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (T : Z) : Prop :=
awr W mem (rg_nsrc RG) 4 /\
((T = 0 /\ val_mem SEGS (arm W mem) (rg_src RG) 8 0 /\ awr W mem (rg_src RG) 8 /\
  val_mem SEGS (arm W mem) (rg_capsrc RG) 4 0 /\ awr W mem (rg_capsrc RG) 4) \/
 (T <> 0 /\ val_mem SEGS (arm W mem) (rg_src RG) 8 T /\ awr W mem (rg_src RG) 8 /\
  val_mem SEGS (arm W mem) (rg_capsrc RG) 4 16 /\ awr W mem (rg_capsrc RG) 4 /\
  In (T, ATABLE) (ablocks B ly S))).
(* What both segments need from relay_finish's own entry state: its whole afn_pre, the blocks it started from, and
   the three inclusions rf_spec gives about the globals. *)
Definition rf_entry_facts (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
(md : Model) (regs : bvmap 5 word) (T : Z) (es : list rentry) (cap out : Z) (rest : list (Z * Z)) : Prop :=
(exists ch, afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch) /\
Permutation (ablocks B ly S) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest) /\
(forall a, inG (RF_G RG GL) a -> inG G a) /\ (forall a, inG (G_SL B RG) a -> inG G a) /\
(forall a, inG (RF_G RG GL) a -> ~ (as_errno B <= a < as_errno B + 4)).
(* ---- X, the state at the tail 0x8243c. ---- *)
Definition RFX (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (lyX : alayout) (SX : astate) (HpX : list Z) (WX : world SEGS) (regsX : bvmap 5 word)
(memX : word -> option byte) (mdX : Model) (kr : nat) : Prop :=
exists kX outX,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []
  lyX SX HpX WX memX mdX kX /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsX (spZ regs) /\
rf_saved WX memX (spZ regs) regs /\
rf_done lyX SX WX memX T /\
alock_at RG WX memX true /\
aout_at B RG lyX SX WX memX
  (gse_c (rf_run c O mx no cap es)) (gse_O (rf_run c O mx no cap es)) mx
  (gse_no (rf_run c O mx no cap es)) (gse_cap (rf_run c O mx no cap es)) outX /\
Permutation (ablocks B lyX SX) (rf_tblk T ++ aout_blks (gse_cap (rf_run c O mx no cap es)) outX ++ rest) /\
(exists lst, val_mem SEGS (arm WX memX) GL 4 lst) /\ awr WX memX GL 4 /\
apres_kept B W mem WX memX /\
mo_le MT S SX (rf_cost MT c O mx no cap es) /\
(* the room round: the room left after every round, which rf_post_x passes on *)
rp_RM RP SX kr.
Definition rf_tail_stmt : Prop :=
forall regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr,
RFX regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS)) mdX)
(rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* ---- The tail X (0x8243c = relay_finish + 0xf8): g_client = -1, g_listen = -1, a0 = &g_lock, g_nsrc = 0, the
   epilogue, and the TAIL CALL `j pthread_mutex_unlock` (B; A calls the unlock and returns itself): the unlock
   returns to relay_finish's caller, so the post comes out of aj_gx_entry_at at the caller's sp (o = 0). ----
   The cut state is a fresh symbolic state: the frame (atom 2 = sp0 - 48; the six saved words of rf_saved at
   0 .. 40, read-only) and the three globals the tail stores to, based on the auipc atoms (s1 pinned to A_HI 5;
   the tail's own auipc's give A_HI 7 and A_HI 8). *)
Definition rfx_extra (regsE : bvmap 5 word) : list word := map (getr regsE) RF_SAVED.
Lemma nth_rfx_extra : forall regsE i, (i < 6)%nat ->
nth i (rfx_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i RF_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold rfx_extra.
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
(* every byte of a val_mem is visible *)
Lemma rfx_av_ne : forall (W : world SEGS) (m : word -> option byte) a (n : nat) v x,
val_mem SEGS (mrestrict (w_H W) m) a n v -> a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m x <> None.
Proof.
intros W m a n v x Hv Hx. unfold aview.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
specialize (Hv (Z.to_nat (x - a)) Hk). rewrite Z2Nat.id in Hv by lia.
replace (a + (x - a)) with x in Hv by lia. rewrite Hv. discriminate.
Qed.
(* a 4-byte store of -1 leaves the 32-bit value 2^32 - 1 *)
Lemma rfx_m1_val : forall E m base off,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 4 (SLit 18446744073709551615))) ->
val_mem SEGS m (base + off) 4 (2 ^ 32 - 1).
Proof.
intros E m base off Hc k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off] in Hm. rewrite Hm. cbn [YP09.cbyte YP09.c_val sv_denot] in Hb. injection Hb as Hb. subst b.
f_equal. apply bv_eq.
destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | lia].
Qed.
Definition rfx_sr : list sv := sr_set sr_atoms 9 (SOff (A_HI 5) 0).
Definition rfx_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 48 0 0
  (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 6));
  YP09.mkRegion (Some (A_HI 5)) (-1672) (-1668) (-1672) (-1668) [];
  YP09.mkRegion (Some (A_HI 7)) 292 296 292 296 [];
  YP09.mkRegion (Some (A_HI 8)) 248 252 248 252 [] ].
Definition rfx_facts : facts :=
mkFacts [ (A_HI 5, mkAF 0xf000 0x600000 0); (A_HI 7, mkAF 0xf000 0x600000 0); (A_HI 8, mkAF 0xf000 0x600000 0) ] [] [].
Definition ss_rfx : sstate := mkSS A_rf_tail rfx_sr rfx_regions None rfx_facts.
Definition BxX : sv := SOff 8 0.
Lemma rfx_entry : forall (W : world SEGS) regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + 48 <= 2 ^ 47 ->
getr regsX 9 = w64 (VAL (A_HI 5)) ->
rf_saved W memX (spZ regsX + 48) regsE ->
awr W memX (rg_nsrc RG) 4 -> awr W memX (rg_client RG) 4 -> awr W memX GL 4 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (rfx_extra regsE))) ss_rfx
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop HR9 HSV HW1 HW2 HW3.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (rfx_extra regsE))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
pose proof (UH 5%nat ltac:(lia)) as U5. pose proof (UH 7%nat ltac:(lia)) as U7. pose proof (UH 8%nat ltac:(lia)) as U8.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as Bn.
pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as Bg.
cbn [fst snd] in Bn, Bc, Bg.
unfold ss_rfx. apply pa_entry_st_ok_full.
- unfold rfx_sr.
  apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite U5, HR9, Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold rfx_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
    apply (chunk_ok_val SEGS E _ (spZ regsX) (8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i RF_SAVED 0%bv)))).
    * cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite ew_Ereg_extra, nth_rfx_extra by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (getr regsE (nth i RF_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
    * zside.
    * replace (spZ regsX + 8 * Z.of_nat i) with (spZ regsX + 48 - 48 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
  + rewrite U5. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 5) + o) with (rg_nsrc RG + (o + 1672)) by lia. exact (HW1 (o + 1672) ltac:(lia)).
  + rewrite U7. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 7) + o) with (rg_client RG + (o - 292)) by lia. exact (HW2 (o - 292) ltac:(lia)).
  + rewrite U8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 8) + o) with (GL + (o - 248)) by lia. exact (HW3 (o - 248) ltac:(lia)).
- unfold rfx_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U5, U7, U8.
  zsep_pick HSEPO 1%nat 2%nat D12. zsep_pick HSEPO 1%nat 3%nat D13. zsep_pick HSEPO 2%nat 3%nat D23.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rfx_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U5, U7, U8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Ltac rfx_infp := repeat (first [left; reflexivity | right]).
(* one cell of aout_at, HSEPO index i (4 .. 11), apart from the four cells the tail writes (0 .. 3) *)
Ltac rfx_cell K H i :=
  let S0 := fresh "S" in let S1 := fresh "S" in let S2 := fresh "S" in let S3 := fresh "S" in
  zsep_pick H 0%nat i S0; zsep_pick H 1%nat i S1; zsep_pick H 2%nat i S2; zsep_pick H 3%nat i S3;
  apply K; lia.
(* aout_at's cells but g_client, and the g_out block: what the tail keeps of the controller's side *)
Definition rfx_aout_fp (cap out : Z) : list (Z * Z) :=
(rg_send_max RG, rg_send_max RG + 8) :: (rg_nout RG, rg_nout RG + 8) :: (rg_capout RG, rg_capout RG + 8) ::
(rg_out RG, rg_out RG + 8) :: (rg_client_broken RG, rg_client_broken RG + 1) ::
(rg_send_dead RG, rg_send_dead RG + 1) :: (rg_send_eintr RG, rg_send_eintr RG + 1) ::
(as_errno B, as_errno B + 4) :: (if cap =? 0 then [] else [(out, out + cap)]).
(* the stream after g_client = -1 (W_rep.v aout_at_kept, with the client cell rewritten) *)
Lemma rfx_aout_m1 : forall ly S (W : world SEGS) mem ly' S' (W' : world SEGS) mem' c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out ->
akept W mem W' mem' (rfx_aout_fp cap out) ->
(forall x, writable_at SEGS (arm W mem) x -> writable_at SEGS (arm W' mem') x) ->
val_mem SEGS (arm W' mem') (rg_client RG) 4 (2 ^ 32 - 1) ->
(forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
aout_at B RG ly' S' W' mem' (rf_ctl c) O mx no cap out.
Proof.
intros ly S W mem ly' S' W' mem' c O mx no cap out
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HW HCL HB.
assert (KC : forall a n, In (a, a + n) (rfx_aout_fp cap out) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
  by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
unfold rf_ctl, aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_max RG) 8); [rfx_infp | cbn in Hx; lia] | exact H1]|].
split; [apply (akept_awr W mem); [apply (KC (rg_send_max RG) 8); rfx_infp | exact H2]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nout RG) 8); [rfx_infp | cbn in Hx; lia] | exact H3]|].
split; [apply (akept_awr W mem); [apply (KC (rg_nout RG) 8); rfx_infp | exact H4]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capout RG) 8); [rfx_infp | cbn in Hx; lia] | exact H5]|].
split; [apply (akept_awr W mem); [apply (KC (rg_capout RG) 8); rfx_infp | exact H6]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_out RG) 8); [rfx_infp | cbn in Hx; lia] | exact H7]|].
split; [apply (akept_awr W mem); [apply (KC (rg_out RG) 8); rfx_infp | exact H8]|].
split; [exact HCL|].
split; [intros i Hi; exact (HW _ (H10 i Hi))|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client_broken RG) 1); [rfx_infp | cbn in Hx; lia] | exact H11]|].
split; [apply (akept_awr W mem); [apply (KC (rg_client_broken RG) 1); rfx_infp | exact H12]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_dead RG) 1); [rfx_infp | cbn in Hx; lia] | exact H13]|].
split; [apply (akept_awr W mem); [apply (KC (rg_send_dead RG) 1); rfx_infp | exact H14]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [rfx_infp | cbn in Hx; lia] | exact H15]|].
split; [apply (akept_awr W mem); [apply (KC (rg_send_eintr RG) 1); rfx_infp | exact H16]|].
split; [apply (akept_vm W mem); [intros x Hx; apply (KC (as_errno B) 4); [rfx_infp | cbn in Hx; lia] | exact H17]|].
split; [apply (akept_awr W mem); [apply (KC (as_errno B) 4); rfx_infp | exact H18]|].
split; [exact H19|]. split; [right; reflexivity|].
do 5 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|].
split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W mem); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold rfx_aout_fp; rewrite Ec; rfx_infp | lia].
Qed.
(* the bytes the walker reads off a present range, as a list of bytes *)
Lemma rfx_bzs_map : forall l, Forall (fun b => 0 <= b < 256) l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
intros l Hok. unfold bzs. rewrite map_map. transitivity (map (fun x => x) l); [|apply map_id].
apply map_ext_in. intros x Hx. pose proof (proj1 (Forall_forall _ _) Hok x Hx) as Rx. cbv beta in Rx. unfold bz.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma rf_tail : rf_tail_stmt.
Proof.
unfold rf_tail_stmt.
intros regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16672) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HX as (kX & outX & HJX & ((ch & HPRE0) & HPERM0 & HG1 & HG2 & HG3) & HKP & HSV & HDONE & HLK
  & HAO & HPERM & HGLv & HGLw & HPRES & HMO & HRMX).
pose proof HPRE0 as (_ & Hra & _ & Hgp & Htp & _). clear HPERM0.
destruct HKP as (KSP & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K9).
pose proof HJX as (HSTK & HXO & (memS & HJi & HAG) & HOUT).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARx & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (rfx_entry WX regsX memX regs
  ltac:(rewrite KSP; rewrite WS in Hslo; lia) ltac:(rewrite KSP; lia) K9
  ltac:(replace (spZ regsX + 48) with (spZ regs) by lia; exact HSV)
  (proj1 HDONE) ltac:(pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _); exact Hw) HGLw) as HS.
remember (Eimg (Ereg regsX (rfx_extra regs))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 6)%nat -> ew E (32 + i) = getr regs (nth i RF_SAVED 0%bv))
by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact (nth_rfx_extra regs i Hi)).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
assert (U5 : bv_unsigned (ew E 285%nat) = VAL (A_HI 5)) by exact (UH 5%nat ltac:(lia)).
assert (U7 : bv_unsigned (ew E 287%nat) = VAL (A_HI 7)) by exact (UH 7%nat ltac:(lia)).
assert (U8 : bv_unsigned (ew E 288%nat) = VAL (A_HI 8)) by exact (UH 8%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
clear HE.
assert (SHOK : sh_ok SEGS BxX [] E (mrestrict (w_H WX) memX)) by constructor.
(* the globals relay_finish writes are bytes of G *)
assert (INL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (INS : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (INC : forall a, rg_client RG <= a < rg_client RG + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ING : forall a, GL <= a < GL + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
paj_run_tok_x RUN HS HJX SHOK Bspan.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U5, ?U7, ?U8 in Hr;
    first [ lia | right; left; apply INS; lia | right; left; apply INC; lia | right; left; apply ING; lia ] | ]).
  destruct Hin. }
(* ---- what the stores left: g_nsrc = 0, g_client = g_listen = 2^32 - 1, every other byte as at the cut ---- *)
lazymatch goal with Hx : mem_grows _ _ |- _ => rename Hx into MG1 end.
rename HFr into HFr1. clear HF.
assert (NWA : forall a, ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> ~ in_wrange E (ss_mem ss_rfx) a).
{ intros a N1 N2 N3 (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U5, ?U7, ?U8 in Hr; lia | ]).
  destruct Hin. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E _ (w_H WX) memX (ms_mem ms) HFr1 a Ha (NWA a N1 N2 N3))).
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HRn.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HRc.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HRg.
cbn [ms_mem restrict] in HRn, HRc, HRg.
pose proof (field_of_region E _ 285%nat _ _ _ _ _ _ (-1672) 4%N (SLit 0) 0 HRn U5 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as VNS1.
rewrite HH5 in VNS1. change (N.to_nat 4) with 4%nat in VNS1.
pose proof HRc as (_ & _ & _ & HCc). cbn [YP09.r_chunks YP09.r_base base_val] in HCc. apply Forall_inv in HCc.
pose proof (rfx_m1_val E _ _ _ HCc) as VCL1. rewrite U7, HH7 in VCL1.
pose proof HRg as (_ & _ & _ & HCg). cbn [YP09.r_chunks YP09.r_base base_val] in HCg. apply Forall_inv in HCg.
pose proof (rfx_m1_val E _ _ _ HCg) as VGL1. rewrite U8, HH8 in VGL1.
clear HRn HRc HRg HCc HCg.
(* ---- the tail call to pthread_mutex_unlock (a0 = &g_lock = VAL (A_OBJ 3)), at the caller's sp ---- *)
rewrite WS in Hslo.
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as Bl.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as Bn.
pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as Bg.
cbn [fst snd] in Bl, Bn, Bc, Bg.
assert (KLK1 : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a).
{ intros a Ha. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  apply KA; lia. }
assert (LK0m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG) 4 0)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 0); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK0]).
assert (LK4m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + 4) 4 16)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 16); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK4]).
assert (LK8m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + 8) 4 0)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 0); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK8]).
assert (LKW1 : forall i, 0 <= i < 12 -> writable_at SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + i))
by (intros i Hi; exact (writable_at_grows SEGS _ _ _ MG1 (LKW i Hi))).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (HSPc : spZ (ms_regs ms) = spZ regs + 0).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). unfold spZ in *. lia. }
assert (QA0 : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 244%nat with (A_OBJ 3).
  rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), HV3. reflexivity. }
assert (QRA : getr (ms_regs ms) 1 = getr regs 1) by (rewrite Q1; exact (EX 5%nat ltac:(lia))).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR1.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B lyX SX a).
{ intros a Ha Ho. destruct (HG a (INL a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho). }
eapply SRr_mono.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H WX) mem') (rg_lock RG + 4) 4 0)
    WX (ms_regs ms) (ms_mem ms) RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ 0 (getr regs 1) HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), K3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), K4. exact Htp.
  - exact QRA.
  - exact Hra.
  - intros a. lia.
  - intros a Ha _. exact (rfx_av_ne WX (ms_mem ms) (rg_lock RG + 4) 4%nat 16 a LK4m ltac:(cbn; lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply INL. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0.
    + lia.
    + exact RGAL.
    + lia.
    + exact LK0m.
    + exact LK4m.
    + exact LK8m.
    + intros a Ha. split.
      * destruct (Z_lt_le_dec a (rg_lock RG + 4)) as [h1 | h1]; [exact (rfx_av_ne WX _ _ 4%nat 0 a LK0m ltac:(cbn; lia))|].
        destruct (Z_lt_le_dec a (rg_lock RG + 8)) as [h2 | h2]; [exact (rfx_av_ne WX _ _ 4%nat 16 a LK4m ltac:(cbn; lia))|].
        exact (rfx_av_ne WX _ _ 4%nat 0 a LK8m ltac:(cbn; lia)).
      * rewrite HSPc. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. exact (LKW1 (a - rg_lock RG) ltac:(lia)).
      * apply HNOWN. lia.
      * rewrite HSPc. unfold spZ in *. lia.
    + intros a Ha HK. exact (proj2 (proj2 (HG a (INL a ltac:(lia)))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK43) & Hfr3 & Hpres3).
(* ---- from the cut to the return: presence, writability and the bytes ---- *)
pose proof pa_img_range as Himg.
assert (PR2 : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) mem3 a)
by (intros a Ha; apply Hpres3; exact (apresent_grows (w_H WX) memX (ms_mem ms) a MG1 Ha)).
assert (WKf : forall x, writable_at SEGS (arm WX memX) x -> writable_at SEGS (arm WX mem3) x)
by (intros x Hx; exact (writable_kept (w_H WX) memX mem3 x (PR2 x) Hx)).
(* an image-band byte off the lock word keeps its view from after the stores to the return *)
assert (KIMG : forall x, 0x10000 <= x < 0x5fc000 -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) (ms_mem ms) x).
{ intros x Hx Nl. apply Hfr3; [lia | exact Nl | unfold spZ in *; lia]. }
(* ... and from the cut, when it is none of the three stored cells *)
assert (KALL : forall x, 0x10000 <= x < 0x5fc000 -> ~ (rg_nsrc RG <= x < rg_nsrc RG + 4) ->
  ~ (rg_client RG <= x < rg_client RG + 4) -> ~ (GL <= x < GL + 4) -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x)
by (intros x Hx N1 N2 N3 N4; rewrite (KIMG x Hx N4); apply KA; [lia | exact N1 | exact N2 | exact N3]).
(* a byte of a live block keeps its view from the cut to the return *)
assert (KBLK : forall p n x, In (p, n) (ablocks B lyX SX) -> p <= x < p + req_size n ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros p n x Hin Hx.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARx Hin) as (_ & Hp4096 & Hpceil & _).
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n x HARx Hin Hx) as Hxn.
  assert (Nc : forall i lo m, nth_error rf_cells i = Some (lo, m) -> ~ (lo <= x < lo + m)).
  { intros i lo m Hn Hr. exact (Hxn (proj1 (HPLAIN x (in_rf_cell i lo m x Hn Hr)))). }
  rewrite (Hfr3 x ltac:(unfold ASAN_CEIL in *; lia) ltac:(intros Hl; apply (Nc 1%nat (rg_lock RG) 12); [reflexivity | lia])
    ltac:(unfold ASAN_CEIL, spZ in *; lia)).
  apply KA; [unfold ASAN_CEIL in *; lia | apply (Nc 2%nat); reflexivity | apply (Nc 5%nat); reflexivity | apply (Nc 6%nat); reflexivity]. }
(* the values the tail stored, at the return *)
assert (VNSf : val_mem SEGS (arm WX mem3) (rg_nsrc RG) 4 0).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 0); [|exact VNS1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 1%nat S01. apply KIMG; lia. }
assert (VCLf : val_mem SEGS (arm WX mem3) (rg_client RG) 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VCL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 2%nat S02. apply KIMG; lia. }
assert (VGLf : val_mem SEGS (arm WX mem3) GL 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VGL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 3%nat S03. apply KIMG; lia. }
(* the lock: released (word 4 by the unlock), type and waiter words kept *)
assert (LKF : alock_at RG WX mem3 false).
{ unfold alock_at, arm. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK0]. intros k Hk. cbn in Hk. apply KALL; lia.
  - exact HLK43.
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK8]. intros k Hk. cbn in Hk. apply KALL; lia.
  - intros i Hi. apply WKf. exact (LKW i Hi). }
(* the controller's cells (all but g_client) and the g_out block, from the cut *)
assert (AK : akept WX memX WX mem3 (rfx_aout_fp (gse_cap (rf_run c O mx no cap es)) outX)).
{ intros r Hr a Ha. split; [|apply WKf].
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_max RG, 8) ltac:(left; reflexivity)) as B4.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_nout RG, 8) ltac:(do 1 right; left; reflexivity)) as B5.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_capout RG, 8) ltac:(do 2 right; left; reflexivity)) as B6.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_out RG, 8) ltac:(do 3 right; left; reflexivity)) as B7.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_client_broken RG, 1) ltac:(do 4 right; left; reflexivity)) as B8.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_dead RG, 1) ltac:(do 5 right; left; reflexivity)) as B9.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_eintr RG, 1) ltac:(do 6 right; left; reflexivity)) as B10.
  cbn [fst snd] in B4, B5, B6, B7, B8, B9, B10.
  unfold rfx_aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]; cbn [fst snd] in Ha.
  - rfx_cell KALL HSEPO 4%nat.
  - rfx_cell KALL HSEPO 5%nat.
  - rfx_cell KALL HSEPO 6%nat.
  - rfx_cell KALL HSEPO 7%nat.
  - rfx_cell KALL HSEPO 8%nat.
  - rfx_cell KALL HSEPO 9%nat.
  - rfx_cell KALL HSEPO 10%nat.
  - assert (Hb : 0x10000 <= a < 0x5fc000).
    { apply Himg. apply (proj1 (HG a (HG2 a ltac:(unfold G_SL, inG; do 5 apply Exists_cons_tl; apply Exists_cons_hd;
        unfold in_zr; cbn [fst snd]; lia)))). }
    rfx_cell KALL HSEPO 11%nat.
  - pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAOB).
    destruct (Z.eq_dec (gse_cap (rf_run c O mx no cap es)) 0) as [Hc0 | Hc0].
    { rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hr. destruct Hr. }
    rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [lia|].
    apply (KBLK _ _ a HoIn). unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). exact Ha. }
(* g_src and g_capsrc as the cut found them *)
assert (KSRC : forall x, rg_src RG <= x < rg_src RG + 8 -> aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 3%nat 5%nat T1. zsep_pick HSEPG 4%nat 5%nat T2. zsep_pick HSEPG 5%nat 7%nat T3. zsep_pick HSEPG 5%nat 8%nat T4.
  apply KALL; lia. }
assert (KCAP : forall x, rg_capsrc RG <= x < rg_capsrc RG + 4 -> aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 3%nat 6%nat T1. zsep_pick HSEPG 4%nat 6%nat T2. zsep_pick HSEPG 6%nat 7%nat T3. zsep_pick HSEPG 6%nat 8%nat T4.
  apply KALL; lia. }
pose proof HJX3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HARf & _ & _ & _ & _ & Hfrf & _).
(* ---- the post ---- *)
unfold rf_post_x.
exists lyX, SX, HpX, regs3, mem3, md3, kX, outX.
split; [reflexivity|].
split; [exact HJX3|].
split.
{ intros r Hr. rewrite (HP3 r Hr). unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2, Usp, KSP.
    replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (EE 3%nat 3%bv eq_refl). exact K3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (EE 4%nat 4%bv eq_refl). exact K4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (EX 0%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21, (EE 21%nat 21%bv eq_refl). exact K21.
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22, (EE 22%nat 22%bv eq_refl). exact K22.
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23, (EE 23%nat 23%bv eq_refl). exact K23.
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (EE 24%nat 24%bv eq_refl). exact K24.
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (EE 25%nat 25%bv eq_refl). exact K25.
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (EE 26%nat 26%bv eq_refl). exact K26.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (EE 27%nat 27%bv eq_refl). exact K27. }
split. { intros a Hi Ho He Hpr. exact (PR2 a (HPRES a Hi Ho He Hpr)). }
split. { cbn [app] in Hfrf. exact Hfrf. }
split. { exact HMO. }
(* the room round: the unlock keeps the allocator state, so RFX's room is rf_post_x's *)
split. { exact HRMX. }
split. { exact HPERM. }
split.
{ apply (rfx_aout_m1 lyX SX WX memX _ _ WX _ _ _ mx _ _ outX HAO AK WKf VCLf).
  intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  apply in_or_app. right. apply in_or_app. left. exact Hb. }
split. { exact LKF. }
split.
{ destruct HDONE as (HNSW & [(HT0 & VS0 & WS0 & VC0 & WC0) | (HT & VST & WST & VCT & WCT & HTin)]).
  - left. split; [exact HT0|]. split; [reflexivity|]. unfold arelay_empty.
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 8 0); [intros k Hk; cbn in Hk; apply KSRC; lia | exact VS0]|].
    split; [intros i Hi; apply WKf; exact (WS0 i Hi)|].
    split; [exact VNSf|].
    split; [intros i Hi; apply WKf; exact (HNSW i Hi)|].
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [intros k Hk; cbn in Hk; apply KCAP; lia | exact VC0]|].
    intros i Hi; apply WKf; exact (WC0 i Hi).
  - right. unfold arelay_at.
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 8 T); [intros k Hk; cbn in Hk; apply KSRC; lia | exact VST]|].
    split; [intros i Hi; apply WKf; exact (WST i Hi)|].
    split; [exact VNSf|].
    split; [intros i Hi; apply WKf; exact (HNSW i Hi)|].
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 16); [intros k Hk; cbn in Hk; apply KCAP; lia | exact VCT]|].
    split; [intros i Hi; apply WKf; exact (WCT i Hi)|].
    split; [cbn; lia|].
    split; [exact HTin|].
    split; [|split; [constructor | split; constructor]].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HARf HTin) as (_ & _ & _ & _ & HTp & _).
    destruct (garr8_of_present SEGS (arm WX mem3) T 896) as (l & Hl & Hg).
    { intros a Ha. destruct (HTp a ltac:(unfold req_size, ATABLE; cbn in Ha |- *; lia)) as ((Hh & b & Hb) & _).
      exists b. unfold arm, mrestrict. rewrite Hh. exact Hb. }
    exists (map (Z_to_bv 8) l). unfold atable_at. cbn [length map concat app].
    rewrite (rfx_bzs_map l (garr8_bytes_ok SEGS _ _ _ Hg)), length_map, Hl.
    unfold ATABLE, AENT. split; [cbn; lia|]. split; [cbn; lia|]. exact Hg. }
split; [exact VGLf|].
intros i Hi. apply WKf. exact (HGLw i Hi).
Qed.
(* ---- L, the state at the loop head 0x823c0, round i: entries 0 .. i-1 are done, i .. n-1 untouched.  s0 = SB
   (the shadow base), s2 = 56 i, s3 = i, s4 = the auipc of g_src (the PLdHi slot 6 the head's load tests). ---- *)
Definition RFI (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (i : nat) (lyL : alayout) (SL : astate) (HpL : list Z) (WL : world SEGS)
(regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (kr : nat) : Prop :=
exists kL outL spent,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []
  lyL SL HpL WL memL mdL kL /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsL (spZ regs) /\
getr regsL 8 = w64 SB /\ getr regsL 20 = w64 (VAL (A_HI 6)) /\
getr regsL 19 = w64 (Z.of_nat i) /\ getr regsL 18 = w64 (56 * Z.of_nat i) /\
rf_saved WL memL (spZ regs) regs /\
(i < length es)%nat /\ (length es <= 16)%nat /\ T <> 0 /\
val_mem SEGS (arm WL memL) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr WL memL (rg_nsrc RG) 4 /\
val_mem SEGS (arm WL memL) (rg_src RG) 8 T /\ awr WL memL (rg_src RG) 8 /\
val_mem SEGS (arm WL memL) (rg_capsrc RG) 4 16 /\ awr WL memL (rg_capsrc RG) 4 /\
In (T, ATABLE) (ablocks B lyL SL) /\
(forall j, (i <= j < length es)%nat ->
   garr8 SEGS (arm WL memL) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
   awr WL memL (T + AENT * Z.of_nat j) AENT /\
   aheld_ok B lyL SL WL memL (nth j es rf_e0) /\
   ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
    (0 < re_cap (nth j es rf_e0) /\
     In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B lyL SL)))) /\
alock_at RG WL memL true /\
aout_at B RG lyL SL WL memL
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es))) outL /\
Permutation (ablocks B lyL SL)
  (rf_tblk T ++ rf_eblks (skipn i es) ++
   aout_blks (gse_cap (rf_run c O mx no cap (firstn i es))) outL ++ rest) /\
(exists lst, val_mem SEGS (arm WL memL) GL 4 lst) /\ awr WL memL GL 4 /\
garr8 SEGS (arm WL memL) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS WL memL /\
apres_kept B W mem WL memL /\
rf_room MMAX (blocks_bytes SL)
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es) /\
mo_le MT S SL spent /\
spent + rf_cost MT
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es) <= rf_cost MT c O mx no cap es /\
mo_ok MT S (rf_cost MT c O mx no cap es) /\
(* the room round: the room the remaining rounds charge (each a free and a gestures_end), then rf_post_x's kr *)
rp_RM RP SL (Z.to_nat (rf_cost MT_rk
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es)) + kr).
(* the free's caller context (rf_spec_x's premise), which the loop passes to the `_c` free rules; and (the room round)
   rf_spec_x's count premise at the entry state (rf_pk = 5: each round's g_out block may be one more request of a
   class than the entry held, and gestures_end's own premise constant is gse_pk = 4) - each round's free and
   gestures_end read their own count premise off it and the round's block equation *)
Definition rf_loop_stmt : Prop :=
In [BASE + AF_fr_relay_finish + 200] CTX ->
forall (k : nat) regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr,
(length es - i <= k)%nat ->
cnt_ok_pk RP rf_pk (ablocks B ly S) ->
RFI regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)) mdL)
(rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* ---- THE LOOP L at 0x823c0 (offset 0x7c), by induction on the entries left (W_check_bounded.v cb_loopX's form,
   the round of lib/A/W_relay_finish_h.v rf_loop).  One round: g_src, the entry pointer p = g_src + 56 i and B's
   UBSan checks of it, the shadow check of &s->buf and the load of s->buf; free (s->buf) (afree_cf_rule_c_x /
   afree_null_cf_rule_c_x on the inner journal); the reload of g_src, the checks again and the internal call
   gestures_end (s) (gse_spec_x, composed with ajournal_gx_G_mono_x and ajournal_gx_sub_x); the reload of g_nsrc, i++,
   56 i += 56 and the blt.  The UBSan trap edges (all to `unimp` at 0x8247c): the runner decides every one from the
   seat's facts (W_traps.v R1/R2: atom 32 = T and atom 33 = p, both pointers, p aliased to both sums s2 + T) but the
   first pointer-overflow `bltu a1,a0` (0x823c8), which W_traps.v trap_ptr_wrap_atom refutes; its condition stays in
   the state's facts across free, so the second copy (0x82414) is decided too. ---- *)
Lemma rfl_firstn_S : forall (es : list rentry) i, (i < length es)%nat ->
firstn (S i) es = firstn i es ++ [nth i es rf_e0].
Proof.
induction es as [|e es IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
cbn [firstn nth app]. rewrite IH by lia. reflexivity.
Qed.
Lemma rfl_skipn_S : forall (es : list rentry) i, (i < length es)%nat ->
skipn i es = nth i es rf_e0 :: skipn (S i) es.
Proof.
induction es as [|e es IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.
Lemma rfl_run_app : forall l1 l2 c O mx no cap,
rf_run c O mx no cap (l1 ++ l2) =
rf_run (gse_c (rf_run c O mx no cap l1)) (gse_O (rf_run c O mx no cap l1)) mx
  (gse_no (rf_run c O mx no cap l1)) (gse_cap (rf_run c O mx no cap l1)) l2.
Proof. induction l1 as [|e l1 IH]; intros l2 c O mx no cap; [reflexivity|]. cbn [app rf_run]. apply IH. Qed.
(* the room of the remaining entries shrinks with the live bytes *)
Lemma rfl_gse_room_mono : forall xs bb bb' c mx no cap, bb' <= bb ->
gse_room MMAX bb c mx no cap xs -> gse_room MMAX bb' c mx no cap xs.
Proof.
induction xs as [|x xs IH]; intros bb bb' c mx no cap Hb H; cbn [gse_room] in *; [exact I|].
destruct H as ((H1 & H2) & H4). split; [unfold ge_room; split; lia|].
eapply IH; [|exact H4]. lia.
Qed.
Lemma rfl_room_mono : forall es bb bb' c O mx no cap, bb' <= bb ->
rf_room MMAX bb c O mx no cap es -> rf_room MMAX bb' c O mx no cap es.
Proof.
induction es as [|e es IH]; intros bb bb' c O mx no cap Hb H; cbn [rf_room] in *; [exact I|].
destruct H as [H1 H2]. split; [exact (rfl_gse_room_mono _ _ _ _ _ _ _ Hb H1)|].
eapply IH; [|exact H2]. lia.
Qed.
(* the costs below are nonnegative at any lawful meter: the walk's MT, and (room round) the counting meter MT_rk *)
Lemma rfl_sl_cost_run_nonneg : forall M, ameter_laws M ->
forall fuel mx no cap rem, 0 <= cap -> 0 <= sl_cost_run M fuel mx no cap rem.
Proof.
intros M HM. induction fuel as [|f IH]; intros mx no cap rem Hc; cbn [sl_cost_run]; [lia|].
destruct (rem <=? 0); [lia|].
set (q := if negb (mx =? 0) && (mx <? rem) then mx else rem).
destruct (cap <? no + q) eqn:E; [apply Z.ltb_lt in E|apply IH; exact Hc].
pose proof (mo_malloc_nonneg M HM ((no + q) * 2) ltac:(lia)).
pose proof (mo_free_nonneg M HM). pose proof (IH mx (no + q) ((no + q) * 2) (rem - q) ltac:(lia)). lia.
Qed.
Lemma rfl_sl_cap_nonneg : forall c mx no cap len, 0 <= cap -> 0 <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. destruct (sl_live c len); [|exact Hc].
pose proof (sl_fin_ge (Z.to_nat len) mx no cap len Hc). lia.
Qed.
Lemma rfl_ge_cost_nonneg : forall M, ameter_laws M -> forall c mx no cap xl, 0 <= cap -> 0 <= ge_cost M c mx no cap xl.
Proof.
intros M HM c mx no cap xl Hc. unfold ge_cost, sl_cost.
pose proof (rfl_sl_cost_run_nonneg M HM (Z.to_nat xl) mx no cap xl Hc).
pose proof (rfl_sl_cost_run_nonneg M HM (Z.to_nat 5) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5 (rfl_sl_cap_nonneg c mx no cap xl Hc)).
destruct (sl_live c xl); destruct (sl_live (sl_ctl c xl) 5); lia.
Qed.
Lemma rfl_ge_cap_nonneg : forall c mx no cap xl, 0 <= cap -> 0 <= ge_cap c mx no cap xl.
Proof. intros c mx no cap xl Hc. unfold ge_cap. apply rfl_sl_cap_nonneg, rfl_sl_cap_nonneg, Hc. Qed.
Lemma rfl_gse_nonneg : forall M, ameter_laws M -> forall xs c O mx no cap, 0 <= cap ->
0 <= gse_cost M c mx no cap xs /\ 0 <= gse_cap (gse_run c O mx no cap xs).
Proof.
intros M HM. induction xs as [|x xs IH]; intros c O mx no cap Hc; cbn [gse_cost gse_run].
- split; [exact (mo_free_nonneg M HM) | exact Hc].
- pose proof (rfl_ge_cost_nonneg M HM c mx no cap (Z.of_nat (length x)) Hc). pose proof (mo_free_nonneg M HM).
  destruct (IH (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
    (ge_cap c mx no cap (Z.of_nat (length x))) (rfl_ge_cap_nonneg c mx no cap _ Hc)) as [H1 H2].
  split; [lia | exact H2].
Qed.
Lemma rfl_cost_nonneg : forall M, ameter_laws M -> forall es c O mx no cap, 0 <= cap -> 0 <= rf_cost M c O mx no cap es.
Proof.
intros M HM. induction es as [|e es IH]; intros c O mx no cap Hc; cbn [rf_cost]; [lia|].
destruct (rfl_gse_nonneg M HM (gse_keys e) c O mx no cap Hc) as [H1 H2]. pose proof (mo_free_nonneg M HM).
pose proof (IH (gse_c (gse_run c O mx no cap (gse_keys e))) (gse_O (gse_run c O mx no cap (gse_keys e))) mx
  (gse_no (gse_run c O mx no cap (gse_keys e))) (gse_cap (gse_run c O mx no cap (gse_keys e))) H2). lia.
Qed.
(* the room round: the counting meter MT_rk (W_contract_x.v) is lawful, so its costs are nonnegative too and the
   room a round charges splits exactly (Z.to_nat of a sum of nonnegatives) *)
Lemma rfl_rk_laws : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.
(* the room round: the live count of any class at a round's loop head is at most one above the entry's - the
   entries' blocks only go, and the g_out block (at most one, aout_blks) is the only one that may be new *)
Lemma rfl_acnt_round : forall P T es i capi outi cap out rest,
(ReplyCnt.acnt P (rf_tblk T ++ rf_eblks (skipn i es) ++ aout_blks capi outi ++ rest) <=
 ReplyCnt.acnt P (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest) + 1)%nat.
Proof.
intros P T es i capi outi cap out rest.
assert (E : rf_eblks es = rf_eblks (firstn i es) ++ rf_eblks (skipn i es))
by (unfold rf_eblks; rewrite <- concat_app, <- map_app, firstn_skipn; reflexivity).
rewrite E, !ReplyCnt.acnt_app.
assert (A1 : (ReplyCnt.acnt P (aout_blks capi outi) <= 1)%nat).
{ unfold aout_blks. destruct (capi =? 0); [rewrite acnt_nil; lia|].
  rewrite acnt_cons, acnt_nil. match goal with |- context [if ?b then _ else _] => destruct b end; lia. }
lia.
Qed.
(* a live-block list has no duplicate (its ranges are pairwise apart and each has at least one byte) *)
Lemma rfl_nodup_rng : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l ->
YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hp; [constructor|].
inversion Hpos as [|x' l' Hx Hl]; subst. cbn [map YG0f.pairwise] in Hp. destruct Hp as [Hf Hp].
constructor; [|exact (IH Hl Hp)].
intros Hin. rewrite Forall_forall in Hf.
specialize (Hf (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)).
pose proof (req_size_pos (snd x) Hx). unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma rfl_ablocks_nodup : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp0 W mem md HAR.
destruct (alx_sep _ _ _ LAWS ly S Hp0 W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply rfl_nodup_rng; [|exact Hp].
apply Forall_forall. intros [p n] Hin. cbn [snd].
exact (BLKN ly S Hp0 W mem md p n HAR Hin).
Qed.
(* the 8-byte little-endian field s->buf, read off the entry's bytes *)
Lemma rfl_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rfl_vm8_of_garr8 : forall m a z, 0 <= z < 2 ^ 64 ->
garr8 SEGS m a (bzs (Z_to_le_bytes 8 z)) -> val_mem SEGS m a 8 z.
Proof.
intros m a z Hz Hg k Hk.
assert (Hl : length (Z_to_le_bytes 8 z) = 8%nat) by reflexivity.
rewrite (garr8_mbyte SEGS m a _ k Hg) by (unfold bzs; rewrite length_map, Hl; exact Hk).
assert (E : nth k (bzs (Z_to_le_bytes 8 z)) 0 = bv_unsigned (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)))).
{ unfold bzs. rewrite <- (rfl_nth_le_bytes 8 z k Hk).
  rewrite (nth_indep (map bz (Z_to_le_bytes 8 z)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, Hl; exact Hk).
  exact (List.map_nth bz (Z_to_le_bytes 8 z) (Z_to_bv 8 0) k). }
rewrite E, Z_to_bv_bv_unsigned. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small z) by lia. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rfl_buf_field : forall m a e, length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS m a (bzs (entry_bytes e)) -> val_mem SEGS m (a + 16) 8 (re_buf e).
Proof.
intros m a e Hp Hb Hg. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [_ Hg].
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
lazymatch type of Hg with garr8 _ _ ?base _ =>
  replace base with (a + 16) in Hg by (rewrite !length_map, Hp; simpl length; lia) end.
pose proof (rfl_vm8_of_garr8 m (a + 16) (bv_unsigned (Z_to_bv 64 (re_buf e))) (bv_unsigned_in_range 64 _) Hg) as H.
rewrite unsigned_lit_small in H by lia. exact H.
Qed.
(* the symbolic state at the loop head: s0 = SB (atom 8), s2 = 56 i (atom 18), s3 = i (atom 19); atom 32 = T
   (g_src), 33 = p = T + 56 i (the entry; both sums s2 + T alias it), 34 = s->buf, 35 = |es| (g_nsrc); s1 and s4
   pinned to the two auipc atoms the PLdHi slots test *)
Definition rfl_Bx : sv := SOff 8 0.
Definition rfl_sr : list sv := sr_set (sr_set sr_atoms 9 (SOff (A_HI 5) 0)) 20 (SOff (A_HI 6) 0).
Definition rfl_regions : smem :=
[ YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 34 0))] ].
Definition rfl_facts : facts :=
mkFacts [ (8%nat, mkAF SB SB 0); (18%nat, mkAF 0 840 3); (19%nat, mkAF 0 15 0); (32%nat, HPTR 4); (33%nat, HPTR 3);
  (34%nat, mkAF 0 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 16 0) ] []
  [(SAlu ALU_ADD (SOff 18 0) (SOff 32 0), SOff 33 0); (SAlu ALU_ADD (SOff 32 0) (SOff 18 0), SOff 33 0)].
Definition ss_rfl : sstate := mkSS A_rf_loop rfl_sr rfl_regions None rfl_facts.
Definition rfl_SH : list shent := [ mkSHE 33 16 24 ].
Definition rfl_extra (T p b n : Z) : list word := map (Z_to_bv 64) [T; p; b; n].
(* two ranges are apart when no byte is in both *)
Lemma rfl_apart : forall a n b m, 0 < n -> 0 < m -> (forall x, a <= x < a + n -> b <= x < b + m -> False) ->
a + n <= b \/ b + m <= a.
Proof.
intros a n b m Hn Hm H. destruct (Z_le_gt_dec (a + n) b) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (b + m) a) as [H2|H2]; [right; exact H2|]. exfalso. apply (H (Z.max a b)); lia.
Qed.
(* the receive buffer's block (none when cap = 0) and the bytes free (s->buf) may change *)
Definition rfl_bblk (e : rentry) : list (Z * Z) := if re_cap e =? 0 then [] else [(re_buf e, re_cap e)].
Definition rfl_bex (e : rentry) (a : Z) : Prop := re_cap e <> 0 /\ re_buf e <= a < re_buf e + req_size (re_cap e).
(* the buffer clause of RFI, as one proposition (kept folded so that lia does not case-split on it) *)
Definition rfl_bufok (ly : alayout) (S : astate) (e : rentry) : Prop :=
(re_cap e = 0 /\ re_buf e = 0) \/ (0 < re_cap e /\ In (re_buf e, re_cap e) (ablocks B ly S)).
Lemma rfl_not_owned : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown). Qed.
Lemma rfl_acall_kept_mono : forall lyc Sc (W : world SEGS) memc W2 mem2 slo shi (E1 E2 : Z -> Prop),
(forall a, E1 a -> E2 a) -> acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi E1 ->
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi E2.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E1 E2 HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [intros b m j Hb Hj Hn; exact (K2 b m j Hb Hj (fun H => Hn (HE _ H)))|].
split; [exact K3|]. split; [intros cid pos a Hc Hr Hn; exact (K4 cid pos a Hc Hr (fun H => Hn (HE _ H)))|].
split; [exact K5 | exact K6].
Qed.
(* a byte that stays present stays writable *)
Lemma rfl_wr_pres2 : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hw.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)) as [b'|] eqn:E'.
- apply (apresent_writable SEGS). unfold mrestrict in E'.
  destruct (w_H W' (Z_to_bv 64 a)) eqn:Hh'; [discriminate|]. split; [exact Hh' | exists b'; exact E'].
- destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:E.
  + exfalso. unfold mrestrict in E. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [discriminate|].
    destruct (Hp (conj Hh (ex_intro _ b E))) as [Hh2 [b2 Hb2]].
    unfold mrestrict in E'. rewrite Hh2, Hb2 in E'. discriminate.
  + unfold writable_at, wview in *. rewrite E'. rewrite E in Hw. exact Hw.
Qed.
Lemma rfl_nodup_app_r : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x Hn H1 H2; [destruct H1|].
inversion Hn as [|y' l' Hy Hl]; subst. destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2|].
exact (IH l2 x Hl H1 H2).
Qed.
Lemma rfl_len_key_ptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma rfl_len_entry : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. unfold bzs, entry_bytes. rewrite length_map, !length_app, H1, H2,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. reflexivity.
Qed.
(* the held part of a table entry survives a step that keeps its blocks and their bytes *)
Lemma rfl_aheld_ok_kept : forall ly S (W : world SEGS) mem ly' S' (W' : world SEGS) mem' e,
aheld_ok B ly S W mem e ->
(forall b, In b (gse_blks e) -> In b (ablocks B ly' S')) ->
(forall b n x, In (b, n) (gse_blks e) -> b <= x < b + n -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
aheld_ok B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e (H1 & H2 & H3 & H4 & H5 & H6 & H7) HB HK.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split.
{ destruct H4 as [H4 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H4|right].
  assert (Hb : In (re_hp e, re_kh e) (gse_blks e))
  by (unfold gse_blks; rewrite (proj2 (Z.eqb_neq (re_hp e) 0) Hz); left; reflexivity).
  split; [exact Hz|]. split; [exact (HB _ Hb)|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (garr8_frame SEGS (arm W mem) (arm W' mem')); [exact Hg|].
  intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). apply (HK _ _ x Hb).
  unfold bzs in Hx. rewrite length_map, rfl_len_key_ptrs in Hx. unfold re_nheld in Hk1. lia. }
split; [exact H5|]. split; [exact H6|].
rewrite Forall_forall in H7 |- *. intros k Hk. destruct (H7 k Hk) as (K1 & K2 & K3).
assert (Hb : In (key_addr k, Z.of_nat (length (key_text k)) + 1) (gse_blks e))
by (unfold gse_blks; apply in_or_app; right; apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk).
split; [exact (HB _ Hb)|]. split; [|exact K3].
apply (garr8_frame SEGS (arm W mem) (arm W' mem')); [exact K2|].
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). apply (HK _ _ x Hb).
unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.
(* the same layout and state, a memory with the same ASan view *)
Lemma rfl_aheld_ok_mem : forall ly S (W : world SEGS) mem (W' : world SEGS) mem' e,
aheld_ok B ly S W mem e -> (forall x, aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) -> aheld_ok B ly S W' mem' e.
Proof.
intros ly S W mem W' mem' e H HK. apply (rfl_aheld_ok_kept ly S W mem ly S W' mem' e H); [|intros b n x _ _; apply HK].
intros b Hb. pose proof H as (_ & _ & _ & H4 & _ & _ & H7). unfold gse_blks in Hb. apply in_app_or in Hb.
destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (re_hp e) 0) as [Ez | Ez]; [destruct Hb|]. destruct Hb as [<- | []].
  destruct H4 as [(Hz & _) | (_ & Hin & _)]; [contradiction | exact Hin].
- apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H7. exact (proj1 (H7 k Hk)).
Qed.
Lemma rfl_in_skipn : forall (es : list rentry) k j d, (k <= j < length es)%nat -> In (nth j es d) (skipn k es).
Proof.
induction es as [|x es IH]; intros k j d Hk; [cbn [length] in Hk; lia|].
destruct k as [|k]; [cbn [skipn]; apply nth_In; exact (proj2 Hk)|].
destruct j as [|j]; [lia|]. cbn [skipn nth]. apply IH. cbn [length] in Hk. lia.
Qed.
Lemma rfl_nodup_tl : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. inversion H as [|y l Hy Hl]; subst. exact (IH l2 Hl). Qed.
Lemma rfl_bsum_nonneg : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
induction l as [|x l IH]; intros H; [unfold bsum; cbn; lia|]. rewrite bsum_cons.
pose proof (H x (or_introl eq_refl)). pose proof (IH (fun b Hb => H b (or_intror Hb))). lia.
Qed.
Lemma rfl_bsum_aout : forall cap out, 0 <= cap -> bsum (aout_blks cap out) <= cap.
Proof. intros cap out Hc. unfold aout_blks. destruct (cap =? 0); unfold bsum; cbn [fold_right fst snd]; lia. Qed.
(* the g_out block's bytes are exactly its capacity (aout_blks is [] at cap 0): rf_room's `- cap` threading charges
   the round only the growth gse_cap r - cap, because the old g_out block is freed *)
Lemma rfl_bsum_aout_eq : forall cap out, bsum (aout_blks cap out) = cap.
Proof. intros cap out. unfold aout_blks. destruct (Z.eqb_spec cap 0) as [-> | _]; unfold bsum; cbn [fold_right fst snd]; lia. Qed.
(* a cell apart from each of G_SL's six cells is not a byte of G_SL; one separation per case *)
Lemma rfl_not_gsl : forall a, (forall cl, In cl (G_SL B RG) -> fst cl + snd cl <= a \/ a < fst cl) -> ~ inG (G_SL B RG) a.
Proof. intros a H Hin. unfold inG in Hin. apply Exists_exists in Hin as (cl & Hc & Hz). destruct (H cl Hc); unfold in_zr in Hz; lia. Qed.
Ltac rfl_ng_lo H k :=
  let a := fresh "a" in let Ha := fresh "Ha" in let cl := fresh "cl" in let Hc := fresh "Hc" in let D := fresh "D" in
  intros a Ha; apply rfl_not_gsl; intros cl Hc; unfold G_SL in Hc; cbn [In] in Hc;
  destruct Hc as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd];
  [ zsep_pick H k 8%nat D | zsep_pick H k 10%nat D | zsep_pick H k 5%nat D
  | zsep_pick H k 6%nat D | zsep_pick H k 7%nat D | zsep_pick H k 11%nat D ];
  clear - Ha D; lia.
Ltac rfl_ng_hi H k :=
  let a := fresh "a" in let Ha := fresh "Ha" in let cl := fresh "cl" in let Hc := fresh "Hc" in let D := fresh "D" in
  intros a Ha; apply rfl_not_gsl; intros cl Hc; unfold G_SL in Hc; cbn [In] in Hc;
  destruct Hc as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd];
  [ zsep_pick H 8%nat k D | zsep_pick H 10%nat k D | zsep_pick H 5%nat k D
  | zsep_pick H 6%nat k D | zsep_pick H 7%nat k D | zsep_pick H 11%nat k D ];
  clear - Ha D; lia.
(* END5's five bytes are read-only image bytes: two memories with the read-only view agree on them *)
Lemma rfl_end5_kept : forall (W W' : world SEGS) m m', rom_view SEGS W m -> rom_view SEGS W' m' ->
garr8 SEGS (arm W m) (VAL A_lit_end5) (bzs END5) -> garr8 SEGS (arm W' m') (VAL A_lit_end5) (bzs END5).
Proof.
intros W W' m m' R R' Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') _ _ Hg).
intros x Hx. unfold bzs in Hx. rewrite length_map in Hx. unfold arm. apply (mbyte_of_aview SEGS).
pose proof (HE5R x Hx) as Hr. rewrite (R' x Hr), (R x Hr). reflexivity.
Qed.
(* the regions of the loop's runs have no write window: a run keeps the memory as the walk sees it *)
Ltac rfl_nowr :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.
Ltac rfl_meq MEQ MEQ' :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict ?H ?mp) (mrestrict ?H ?mn) |- _ =>
  lazymatch type of MEQ with forall x, mrestrict _ mp x = mrestrict _ ?m0 x =>
  assert (MEQ' : forall x, mrestrict H mn x = mrestrict H m0 x)
  by (let x := fresh "x" in intros x; rewrite HFr; [apply MEQ | rfl_nowr]) end end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end; clear MEQ.
Ltac rfl_cur HS nm :=
  lazymatch type of HS with context [restrict _ ?m] => first [ constr_eq m nm | try clear nm; rename m into nm ] end.
Ltac rf_awr := apply awr_ok_x_of0; first [ awr_any | cbn [ss_mem add_cond]; awr_any ].
Lemma rf_loop : rf_tail_stmt -> rf_loop_stmt.
Proof.
intros TAIL HCTX. unfold rf_loop_stmt.
induction k as [|k IH]; intros regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr Hk HCNT0 HRFI.
{ exfalso. destruct HRFI as (kL & outL & spent & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRFI as (kL & outL & spent & HJ & HEF & HKP & H8 & H20 & H19 & H18 & HSV & Hi & Hn16 & HT0 &
  HNS & HNSw & HSRC & HSRCw & HCAP & HCAPw & HTB & HENT & HLK & HOUT & HPERM & HGLv & HGLw & HEND5 & HROM & HPK &
  HROOM & HMLE & HSP & HMOK & HRML).
set (sp0 := spZ regs) in *.
set (e := nth i es rf_e0).
destruct (HENT i ltac:(lia)) as (HG8 & HAW & HHELD & HBUF). fold e in HG8, HAW, HHELD, HBUF.
change (rfl_bufok lyL SL e) in HBUF.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARL.
destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL T ATABLE HARL HTB) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTapp, HTpres.
assert (Rb : 0 <= re_buf e < 2 ^ 64).
{ destruct HBUF as [(_ & ->) | (Hc & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL _ _ HARL Hin) as (_ & Hb4096 & Hbceil & _). pose proof (req_size_pos (re_cap e) ltac:(lia)). lia. }
set (p := T + 56 * Z.of_nat i).
set (n := Z.of_nat (length es)).
assert (HVB : val_mem SEGS (mrestrict (w_H WL) memL) (p + 16) 8 (re_buf e)).
{ pose proof HHELD as (Hp1 & _). pose proof (rfl_buf_field _ _ e Hp1 Rb HG8) as H. unfold p, AENT in *. exact H. }
remember (Eimg (Ereg regsL (rfl_extra T p (re_buf e) n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regsL rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 T) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
pose proof HKP as (Ksp & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K9).
assert (E8 : ew E 8 = Z_to_bv 64 SB) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 (56 * Z.of_nat i)) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (EO : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j)) by (intros j Hj; subst E; apply Eimg_img; exact Hj).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsrc : forall x, rg_src RG <= x < rg_src RG + 8 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 3%nat _ 8 x eq_refl Hx)).
assert (Hnsrc : forall x, rg_nsrc RG <= x < rg_nsrc RG + 4 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 2%nat _ 4 x eq_refl Hx)).
assert (HTni : forall x, T <= x < T + 896 -> ~ in_img SEGS x)
by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL memL mdL T ATABLE x HARL HTB ltac:(change (req_size ATABLE) with 896; lia))).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb. cbn [fst snd] in HNSb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as HSRb. cbn [fst snd] in HSRb.
assert (H56 : (56 * Z.of_nat i) mod 8 = 0) by (replace (56 * Z.of_nat i) with (Z.of_nat i * 7 * 8) by ring; apply Z_mod_mult).
assert (Hp8 : p mod 8 = 0).
{ unfold p. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 56 * Z.of_nat i) with ((2 * (T / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
assert (HS : st_ok_pi SEGS VAL E ss_rfl (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rfl. apply pa_entry_st_ok_full.
  - unfold rfl_sr. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    + cbn [sv_denot]. rewrite (EO (A_HI 5) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact K9.
    + cbn [sv_denot]. rewrite (EO (A_HI 6) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact H20.
  - vm_compute. reflexivity.
  - unfold rfl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 5) _ (EO (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 5))), HV5.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) T);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HSRC.
    + rewrite (VB (A_OBJ 4) _ (EO (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 4))), HV4.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold n; zside | zside |].
      rewrite Z.add_0_r. exact HNS.
    + rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
      split; [unfold p; lia|]. split; [unfold p; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 16 8 (SOff 34 0) (re_buf e));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact HVB.
  - apply pairwise_disjoint_of_extents. unfold rfl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 5) _ (EO (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 5))), HV5.
    rewrite (VB (A_OBJ 4) _ (EO (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 4))), HV4.
    rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    zsep_pick HSEPG 4%nat 5%nat D45.
    assert (DS : rg_src RG + 8 <= p + 16 \/ p + 16 + 8 <= rg_src RG).
    { apply rfl_apart; [lia | lia |]. intros x Hx1 Hx2. apply (HTni x ltac:(unfold p in Hx2; lia)).
      exact (proj1 (HPLAIN x (Hsrc x ltac:(lia)))). }
    assert (DN : rg_nsrc RG + 4 <= p + 16 \/ p + 16 + 8 <= rg_nsrc RG).
    { apply rfl_apart; [lia | lia |]. intros x Hx1 Hx2. apply (HTni x ltac:(unfold p in Hx2; lia)).
      exact (proj1 (HPLAIN x (Hnsrc x ltac:(lia)))). }
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [rfl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E8, E18, E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, p, n; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold n. revert HT16 HT4096 HTceil Hp8 H56 Rb Hn16 Hi C1. clear. unfold p, SB. intros.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    + cbn [rfl_facts f_alias alias_ok]. split; [|split; [|exact I]].
      * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 18 _ E18), (U_atom E 32 T E32), (U_atom E 33 p E33) by (unfold p; lia).
        unfold p. replace (56 * Z.of_nat i + T) with (T + 56 * Z.of_nat i) by lia. apply zcanon_id. unfold M64. lia.
      * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 18 _ E18), (U_atom E 32 T E32), (U_atom E 33 p E33) by (unfold p; lia).
        unfold p. apply zcanon_id. unfold M64. lia. }
clear HE.
assert (HBx : U E rfl_Bx = SHADOW_OFF) by (unfold rfl_Bx; rewrite (U_atom E 8 SB E8) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS rfl_Bx rfl_SH E (mrestrict (w_H WL) memL)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H WL) memL E rfl_Bx 33 (p + 16) 8 p 16 24
    (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyL SL HpL WL memL mdL T ATABLE (p + 16) 8 HARL HTB
      ltac:(unfold p; change (req_size ATABLE) with 896; lia) ltac:(unfold p; change (req_size ATABLE) with 896; lia)) HBx);
  [rewrite (U_atom E 33 p E33) by (unfold p; lia); reflexivity | lia | lia |].
  intros x Hx. unfold p, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold A_rf_loop.
paj_run_tok_x RUN HS HJ SHOK Bspan.
{ apply awr_ok_x_of0. awr_any. }
(* 0x823c8 bltu a1,a0: B's UBSan pointer-overflow trap on p = T + 56 i, never taken (W_traps.v trap_ptr_wrap_atom) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 33 32 T (56 * Z.of_nat i) E33 E32 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
  discriminate. }
assert (MEQ0 : forall x, mrestrict (w_H WL) memL x = mrestrict (w_H WL) memL x) by reflexivity.
rfl_meq MEQ0 MEQ1.
paj_run_tok_x RUN HS HJ SHOK Bspan. { rf_awr. }
rfl_meq MEQ1 MEQ2.
rfl_cur HS msF. clear Hc.
(* ---- free (s->buf).  The runs wrote nothing: the memory at the call is memL as the walk sees it. ---- *)
assert (AV1 : forall a, aview SEGS (w_H WL) (ms_mem msF) a = aview SEGS (w_H WL) memL a)
by (intros a; apply aview_eq_of; apply MEQ2).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
pose proof HEF as ((che & HARe & Hrae & Hra4e & HGP0 & HTP0 & HstkE & HpresE & HchE & HQTE) & HPERM0 & HRFG & HSLG & HRFGe).
(* the room round: every class's live count at this round's loop head is at most the entry's plus one *)
assert (HCL : forall P, (ReplyCnt.acnt P (ablocks B lyL SL) <= ReplyCnt.acnt P (ablocks B ly S) + 1)%nat).
{ intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPERM0). apply rfl_acnt_round. }
change (spZ regs) with sp0 in HstkE, HpresE, HchE.
pose proof HstkE as (HalE & HstkE0 & HceilE & HsloE & HshiE & H47E & HbotE & HtopE & Htop2E).
assert (RSTK0 : 48 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (RSTKG : 48 + GSE_STK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_l GSE_STK ASTACK); lia).
assert (HceilS : alloc_ceiling + RF_STK <= sp0) by lia.
assert (Usp1 : spZ (ms_regs msF) = sp0 + -48) by (unfold spZ in Ksp |- *; rewrite Q2, (EE 2%nat 2%bv eq_refl); lia).
assert (Q3' : getr (ms_regs msF) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), K3; exact HGP0).
assert (Q4' : getr (ms_regs msF) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), K4; exact HTP0).
assert (Q10' : getr (ms_regs msF) 10 = w64 (re_buf e)) by (rewrite Q10, E34; reflexivity).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the free returns to 0x8240c = relay_finish + 200: its caller context is rf_spec's one-entry trace *)
assert (HCF : In (raZ (ms_regs msF) :: spine []) CTX).
{ assert (HRAF : raZ (ms_regs msF) = BASE + AF_fr_relay_finish + 200)
  by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; unfold AF_fr_relay_finish, A_relay_finish in *; lia).
  rewrite HRAF. exact HCTX. }
(* B keeps no frame pointer (s0 is the shadow base SB, below alloc_ceiling): the callee's chain is empty *)
assert (HCH : chain_pre lyL (aview SEGS (w_H WL) (ms_mem msF)) (ms_regs msF) []).
{ apply (achain_chain_pre lyL _ (spZ (ms_regs msF)) SB [] (ms_regs msF)).
  - apply achain_low. unfold SB. lia.
  - rewrite Usp1. unfold ASTACK in RSTK0. lia.
  - unfold s0Z. rewrite Q8, E8. apply unsigned_lit_small. unfold SB. lia.
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
set (r0 := rf_run c O mx no cap (firstn i es)) in *.
assert (Hcap0 : 0 <= gse_cap r0).
{ destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  destruct H26 as [(Hq & _) | (Hq & _)]; lia. }
rewrite (rfl_skipn_S es i Hi) in HSP, HROOM, HPERM, HRML. cbn [rf_cost rf_room rf_eblks concat map] in HSP, HROOM, HPERM, HRML.
fold e in HSP, HROOM, HPERM, HRML.
set (r1 := gse_run (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) in *.
destruct (rfl_gse_nonneg MT MLAW (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0) as [Hgc0 Hgk0].
fold r1 in Hgk0.
pose proof (rfl_cost_nonneg MT MLAW (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0) as Hrc0.
(* the room round: the room this round charges - the free's 1, then gestures_end's - and what the rounds after it
   and rf_post_x are owed (kr5), split exactly: MT_rk's costs are nonnegative *)
pose proof (proj1 (rfl_gse_nonneg MT_rk rfl_rk_laws (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0))
  as Hgrk0.
pose proof (rfl_cost_nonneg MT_rk rfl_rk_laws (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0)
  as Hrrk0.
set (kr5 := (Z.to_nat (rf_cost MT_rk (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) (skipn (Datatypes.S i) es)) + kr)%nat).
set (kr4 := (Z.to_nat (gse_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) + kr5)%nat).
assert (HRMf : rp_RM RP SL (1 + kr4)).
{ refine (@eq_ind _ _ (rp_RM RP SL) HRML _ _). unfold kr4, kr5. try change (mo_free MT_rk) with 1. lia. }
(* the room round: the free's count premise, the live counts at its pre state SL (peak 0) *)
assert (HCNTf : cnt_ok RP (ablocks B lyL SL)).
{ unfold cnt_ok. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P). unfold rf_pk. cbv beta. lia. }
pose proof (mo_free_nonneg MT MLAW) as Hmf0.
assert (HMOf : mo_ok MT SL (mo_free MT))
by (exact (mok_station MT S SL (rf_cost MT c O mx no cap es) spent (mo_free MT) MLAW HMOK HMLE Hmf0 ltac:(lia))).
assert (HFPof : 0 < re_cap e -> In (re_buf e, re_cap e) (ablocks B ly S) -> forall j, 0 <= j < req_size (re_cap e) ->
  inFP (rf_FP T es cap out) (re_buf e + j)).
{ intros Hc0 _ j Hj. unfold rf_FP. apply (inFP_ablocks_fp _ (re_buf e) (re_cap e) j); [|exact Hj]. apply in_or_app; right; apply in_or_app; left.
  unfold rf_eblks. apply in_concat. exists (aentry_blks e). split; [apply in_map; apply nth_In; lia|].
  unfold aentry_blks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left; reflexivity. }
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
rewrite (pal_free B TL).
assert (HRFS : ASTACK - -48 <= RF_STK) by lia.
(* the room round: the free's stack room, from the round's inner journal (W_journal_x.v aj_stack_room_x) *)
assert (HSR : ly_bot lyL + ACALL_PREFIX < spZ (ms_regs msF))
by (eapply aj_stack_room_x; [exact HJi | exact Usp1 | exact HRFS]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply SRr_bind with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_x (SK := SK) SEGS B PST ARx RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md []
    ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  Permutation (ablocks B lyL SL) (rfl_bblk e ++ ablocks B ly4 S4) /\
  acall_kept SEGS B lyL SL WL mm W4 mem4 (sp0 + -48 - ASTACK) (sp0 + -48) (rfl_bex e) /\
  mo_le MT SL S4 (mo_free MT) /\
  rp_RM RP S4 kr4 /\
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + j) = aview SEGS (w_H WL) mm (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H WL) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct HBUF as [(Hc0 & Hb0) | (Hc0 & Hin0)].
  - eapply SRr_mono.
    { exact (AFREE0 WL (ms_regs msF) (ms_mem msF) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [] lyL SL HpL _ _
        (-48) (getr (ms_regs msF) 1) [] kr4 HJi ltac:(rewrite Q10', Hb0; reflexivity) Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCF HRMf HCNTf HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_eq _ 0) Hc0); exact (Permutation_sym HPm)|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a []|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He Hpr).
  - eapply SRr_mono.
    { exact (AFREE WL (ms_regs msF) (ms_mem msF) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [] lyL SL HpL _ _
        (re_buf e) (re_cap e) (-48) (getr (ms_regs msF) 1) [] kr4 HJi Hin0 Q10' Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCF HRMf HCNTf
        (HFPof Hc0) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)), Eb1, Eb2; cbn [app];
      exact (Permutation_sym (Permutation_middle l1 l2 _))|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a Ha; unfold rfl_bex; split; [lia | exact Ha]|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He); [|exact Hpr].
    intros Hblk. exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL (ms_mem msF) _ (re_buf e) (re_cap e) a HARc Hin0 Hblk Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HK4 & HML4 & HRM4 & HERR4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK sp0 (rf_FP T es cap out) ly S Hp W mem md []
  ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] RF_STK sp0 _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4 memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | intros a Ha _; lia]. }
(* ---- back from free: g_src and g_nsrc are image cells outside the freed block, so free kept them ---- *)
destruct HK4 as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
assert (KFI : forall a, inG rf_cells a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H WL) memL a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & Ho1 & He1). rewrite (KF3 a Hi1 Ho1 He1). apply AV1. }
assert (VS4 : val_mem SEGS (mrestrict (w_H W4) mem4) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W4) memL mem4); [intros q Hq; apply KFI, Hsrc; lia | exact HSRC]. }
assert (VN4 : val_mem SEGS (mrestrict (w_H W4) mem4) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W4) memL mem4); [intros q Hq; apply KFI, Hnsrc; lia | exact HNS]. }
jafter_call_keep_pi HS 36%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - apply (region_kept_val_at E _ _ 246%nat (rg_src RG) 8 T);
    [change 246%nat with (A_OBJ 5); rewrite <- HV5; exact (HEI (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem msF)); [intros q _; apply AV1 | exact HSRC]
    | exact VS4 | lia].
  - apply (region_kept_val_at E _ _ 245%nat (rg_nsrc RG) 4 n);
    [change 245%nat with (A_OBJ 4); rewrite <- HV4; exact (HEI (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem msF)); [intros q _; apply AV1 | exact HNS]
    | exact VN4 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 36 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOK4 : sh_ok SEGS rfl_Bx [] Ea (mrestrict (w_H W4) mem4)) by constructor.
paj_run_to_tok_x RUNTO HS HJ4 SHOK4 Bspan AF_fr_gestures_end. { rf_awr. }
rfl_cur HS msG.
assert (MEQb : forall x, mrestrict (w_H W4) mem4 x = mrestrict (w_H W4) mem4 x) by reflexivity.
rfl_meq MEQb MEQ3.
assert (AV2 : forall a, aview SEGS (w_H W4) (ms_mem msG) a = aview SEGS (w_H W4) mem4 a) by (intros a; apply aview_eq_of; apply MEQ3).
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
(* ---- the call gestures_end (s), s = T + 56 i = p.  The run wrote nothing. ---- *)
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR5.
(* the start-of-round block list, entry i's buffer block split off, and it is apart from every other block *)
assert (HPERM' : Permutation (ablocks B lyL SL) ((T, ATABLE) :: rfl_bblk e ++
  (gse_blks e ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r0) outL ++ rest))).
{ eapply Permutation_trans; [exact HPERM|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0).
  change (aentry_blks e) with (rfl_bblk e ++ gse_blks e). fold (rf_eblks (skipn (Datatypes.S i) es)).
  rewrite <- !app_assoc. apply Permutation_refl. }
set (X := gse_blks e ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r0) outL ++ rest) in *.
pose proof (Permutation_NoDup HPERM' (rfl_ablocks_nodup _ _ _ _ _ _ HARL)) as HND.
assert (BUFNOT : re_cap e <> 0 -> ~ In (re_buf e, re_cap e) ((T, ATABLE) :: X)).
{ intros Hc Hin. unfold rfl_bblk in HND. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) Hc) in HND. cbn [app] in HND.
  inversion HND as [|y l Hy Hl]; subst. inversion Hl as [|y' l' Hy' Hl']; subst.
  destruct Hin as [Hin | Hin]; [apply Hy; rewrite Hin; left; reflexivity | exact (Hy' Hin)]. }
assert (HPERM4 : Permutation (ablocks B ly4 S4) ((T, ATABLE) :: X)).
{ apply (Permutation_app_inv_l (rfl_bblk e)). eapply Permutation_trans; [apply Permutation_sym; exact HPM4|].
  eapply Permutation_trans; [exact HPERM'|]. apply Permutation_middle. }
assert (KB : forall b m x, In (b, m) ((T, ATABLE) :: X) -> b <= x < b + req_size m ->
  aview SEGS (w_H W4) (ms_mem msG) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hx. rewrite AV2.
  assert (Hin1 : In (b, m) (ablocks B lyL SL)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM'|];
    destruct Hin as [<- | Hin]; [left; reflexivity | right; apply in_or_app; right; exact Hin]).
  replace x with (b + (x - b)) by lia. rewrite (KF2 b m (x - b) Hin1 ltac:(lia)); [apply AV1|].
  intros (Hc & Hx2). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
  assert (Hne : (b, m) <> (re_buf e, re_cap e)) by (intros Heq; apply (BUFNOT Hc); rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x SEGS B ARx LAWS lyL SL _ WL memL mdL b m _ _ HARL Hin1 Hin0 Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (PR2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H WL) memL a -> apresent (w_H W4) (ms_mem msG) a).
{ intros a Ha Ho He [Hh [b Hb]].
  assert (HP4a : apresent (w_H W4) mem4 a).
  { apply (HPR4 a Ha Ho He). split; [exact Hh|]. exists b. pose proof (MEQ2 (Z_to_bv 64 a)) as E1. unfold mrestrict in E1.
    rewrite Hh in E1. rewrite E1. exact Hb. }
  destruct HP4a as [Hh4 [b4 Hb4]]. split; [exact Hh4|]. exists b4. pose proof (MEQ3 (Z_to_bv 64 a)) as E1.
  unfold mrestrict in E1. rewrite Hh4 in E1. rewrite E1. exact Hb4. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept WL memL W4 (ms_mem msG) a).
{ intros a Ha Ho He. split; [rewrite AV2, (KF3 a Ha Ho He); apply AV1|].
  apply rfl_wr_pres2. exact (PR2 a Ha Ho He). }
assert (HTB4 : In (T, ATABLE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | left; reflexivity]).
assert (HX4 : forall b, In b X -> In b (ablocks B ly4 S4)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | right; exact Hb]).
assert (T10' : getr (ms_regs msG) 10 = w64 p).
{ rewrite T10, OLDa, E33 by lia. reflexivity. }
pose proof HHELD as (Hpd1 & Hpd2 & _).
assert (HrqG : forall m, m <= req_size m) by (intros m; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (GX : forall b, In b (gse_blks e) -> In b X) by (intros b Hb; unfold X; apply in_or_app; left; exact Hb).
assert (OX : forall b, In b (aout_blks (gse_cap r0) outL) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (GA5 : garr8 SEGS (arm W4 (ms_mem msG)) p (bzs (entry_bytes e))).
{ apply (garr8_frame SEGS (arm WL memL) (arm W4 (ms_mem msG)) p _); [unfold p; unfold AENT in HG8; exact HG8|].
  intros x Hx. rewrite (rfl_len_entry e Hpd1 Hpd2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
  apply (KB T ATABLE x (or_introl eq_refl)). change (req_size ATABLE) with 896. unfold p in Hx. lia. }
assert (AW5 : awr W4 (ms_mem msG) p AENT).
{ intros j Hj. apply (apresent_writable SEGS).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ T ATABLE HAR5 HTB4) as (_ & _ & _ & _ & HP & _).
  change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (p + j) ltac:(unfold p, AENT in *; lia))). }
assert (HELD5 : aheld_ok B ly4 S4 W4 (ms_mem msG) e).
{ apply (rfl_aheld_ok_kept lyL SL WL memL ly4 S4 W4 (ms_mem msG) e HHELD).
  - intros b Hb. exact (HX4 b (GX b Hb)).
  - intros b m x Hb Hx. apply (KB b m x (or_intror (GX _ Hb))). pose proof (HrqG m). lia. }
assert (AK5 : akept WL memL W4 (ms_mem msG) (aout_fp B RG (gse_cap r0) outL)).
{ assert (GSL : forall a, inG (G_SL B RG) a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (intros a Ha; destruct (HG a (HSLG a Ha)) as (Gi & Gn & _); exact (conj Gi Gn)).
  intros r Hr a Har. unfold aout_fp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Har.
  - destruct (HPLAINO a (or_introl Har)) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_nout RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 5%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_capout RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 6%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_out RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 7%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (HPLAIN a (in_rf_cell 5%nat _ 4 a eq_refl ltac:(clear - Har; lia))) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_client_broken RG, 1);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 8%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (HPLAINO a (or_intror Har)) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_send_eintr RG, 1);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 10%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - split; [rewrite AV2; replace a with (as_errno B + (a - as_errno B)) by lia; rewrite (HERR4 (a - as_errno B) ltac:(lia)); apply AV1|].
    intros _. destruct (HG a (HSLG a ltac:(unfold G_SL, inG; apply Exists_exists; exists (as_errno B, 4);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia]))) as (Hi1 & _ & _).
    unfold arm. apply rf_writable_of_seg; [|exact (HWSEGE a Har)].
    apply (hidden_not_img SEGS W4). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia.
  - destruct (Z.eqb_spec (gse_cap r0) 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Har.
    assert (HobX : In (outL, gse_cap r0) X)
    by (apply OX; unfold aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); left; reflexivity).
    assert (Hrq : req_size (gse_cap r0) = gse_cap r0) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); reflexivity).
    split; [apply (KB outL (gse_cap r0) a (or_intror HobX)); lia|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ outL (gse_cap r0) HAR5 (HX4 _ HobX)) as (_ & _ & _ & _ & HP & _).
    exact (proj1 (HP a ltac:(lia))). }
assert (AOUT5 : aout_at B RG ly4 S4 W4 (ms_mem msG) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL)
by (exact (aout_at_kept B RG lyL SL WL memL ly4 S4 W4 (ms_mem msG) _ _ mx _ _ outL HOUT AK5 (fun b Hb => HX4 b (OX b Hb)))).
assert (HPG5 : Permutation (ablocks B ly4 S4)
  ((T, ATABLE) :: gse_blks e ++ aout_blks (gse_cap r0) outL ++ (rf_eblks (skipn (Datatypes.S i) es) ++ rest))).
{ eapply Permutation_trans; [exact HPERM4|]. unfold X. apply perm_skip. apply Permutation_app_head.
  apply Permutation_app_swap_app. }
destruct HROOM as [HR1 HR2].
assert (HBB4 : blocks_bytes S4 <= blocks_bytes SL).
{ rewrite (blocks_bytes_bsum B lyL SL), (blocks_bytes_bsum B ly4 S4). rewrite (bsum_perm _ _ HPM4), bsum_app.
  assert (0 <= bsum (rfl_bblk e)); [|lia].
  unfold rfl_bblk, bsum. destruct (re_cap e =? 0); cbn [fold_right fst snd]; [lia|].
  destruct HBUF as [(Hc0 & _) | (Hc0 & _)]; lia. }
assert (ROOM5 : gse_room MMAX (blocks_bytes S4) (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e))
by (exact (rfl_gse_room_mono _ _ _ _ _ _ _ HBB4 HR1)).
assert (MO5 : mo_ok MT S4 (gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e))).
{ exact (mok_station MT S S4 (rf_cost MT c O mx no cap es) (spent + mo_free MT) _ MLAW HMOK
    (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) Hgc0 ltac:(lia)). }
pose proof (ajournal_gx_inner_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (memS5 & HJin5 & HagS5).
assert (Usp5 : spZ (ms_regs msG) = sp0 + -48) by (unfold spZ in Ksp |- *; rewrite T2, OLDa, (EE 2%nat 2%bv eq_refl) by lia; lia).
assert (T3' : getr (ms_regs msG) 3 = w64 (as_gp B)) by (rewrite T3, OLDa, (EE 3%nat 3%bv eq_refl), K3 by lia; exact HGP0).
assert (T4' : getr (ms_regs msG) 4 = w64 (as_tp B)) by (rewrite T4, OLDa, (EE 4%nat 4%bv eq_refl), K4 by lia; exact HTP0).
assert (HCH5 : achain ly4 (aview SEGS (w_H W4) (ms_mem msG)) (spZ (ms_regs msG)) (s0Z (ms_regs msG)) []).
{ apply achain_low. unfold s0Z. rewrite T8, OLDa, E8 by lia. rewrite unsigned_lit_small by (unfold SB; lia). unfold SB. lia. }
eassert (HPRE5 : afn_pre_x SEGS B ARx GSE_STK ly4 S4 Hp4 W4 (ms_regs msG) (ms_mem msG) _ []).
{ eapply (afn_pre_x_at SEGS B PST ARx (RF_STK + 0) (sp0 + 0) (rf_FP T es cap out) ly S Hp W memS5 md []
    ly4 S4 Hp4 W4 (ms_mem msG) _ _ (ms_regs msG) GSE_STK (-48) [] HJin5).
  - rewrite Usp5. lia.
  - reflexivity.
  - lia.
  - unfold GSE_STK, GSE_FRAME. pose proof (Z.le_max_r GE_STK ASTACK). unfold ASTACK in *. lia.
  - lia.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1, unsigned_lit_small by lia. lia.
  - exact T3'.
  - exact T4'.
  - exact HCH5. }
assert (ROM4 : rom_view SEGS W4 mem4).
{ apply (acall_kept_rom_view_x SEGS B ARx LAWS lyL SL WL (ms_mem msF) W4 mem4 _ _ (rfl_bex e) ly4 S4 Hp4 md4
    (proj1 HJi4) (conj KF1 (conj KF2 (conj KF3 (conj KF4 (conj KF5 KF6)))))).
  - intros a Ha. destruct (HROMO a Ha) as (_ & H2 & H3 & _). split; [exact H3 | exact H2].
  - intros a Ha. rewrite AV1. exact (HROM a Ha). }
assert (ROM5 : rom_view SEGS W4 (ms_mem msG)) by (intros a Ha; rewrite AV2; exact (ROM4 a Ha)).
assert (END5' : garr8 SEGS (arm W4 (ms_mem msG)) (VAL A_lit_end5) (bzs END5))
by (exact (rfl_end5_kept WL W4 memL (ms_mem msG) HROM ROM5 HEND5)).
(* the room round: at S4 the free only removed a block and the loop head is at most one above the entry (HCL), so
   every callee peak up to 4 fits under the entry's rf_pk = 5 (HCNT5g); gestures_end's gse_pk = 4 is the tight
   instance *)
assert (HCNT5g : forall pk : (Z -> bool) -> nat, (forall P, (pk P <= 4)%nat) -> cnt_ok_pk RP pk (ablocks B ly4 S4)).
{ intros pk Hpk. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P) as H1. pose proof (ReplyCnt.acnt_perm P _ _ HPM4) as H2. rewrite ReplyCnt.acnt_app in H2.
  pose proof (Hpk P) as H3. unfold rf_pk. cbv beta. lia. }
assert (HCNT5 : cnt_ok_pk RP gse_pk (ablocks B ly4 S4)) by (apply HCNT5g; intros P; unfold gse_pk; lia).
eapply SRr_bind.
{ exact (GSE W4 ly4 S4 Hp4 (ms_regs msG) (ms_mem msG) _ [] p T e (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL
    (rf_eblks (skipn (Datatypes.S i) es) ++ rest) HPRE5 T10' HTB4 ltac:(unfold p; lia) ltac:(unfold p, AENT, ATABLE; lia) Hp8
    GA5 AW5 HELD5 AOUT5 HPG5 END5' ROM5 ROOM5 MO5 kr5 HRM4 HCNT5). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & out5 & -> & HJsl & HPsl & HPKsl & HMOsl & HRMsl & HPERMsl & HAOsl & HGAsl & HAWsl).
rewrite T1. fold r1 in HPERMsl, HAOsl.
(* ---- back from gestures_end: its journal (at G_SL) lifted to G and composed into the round's ---- *)
pose proof (ajournal_gx_G_mono_x SEGS B PST ARx (G_SL B RG) G 0 [] GSE_STK (spZ (ms_regs msG)) _ ly4 S4 Hp4 W4 (ms_mem msG) _ []
  ly5 S5 Hp5 W5 mem5 md5 k5 HSLG HJsl) as HJslG.
assert (FPC : forall a, inFP ((p + 40, p + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL)) a ->
  (inFP (rf_FP T es cap out) a /\ exists b n, In (b, n) (ablocks B ly4 S4) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly4 S4) a).
{ intros a Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
  - left. split.
    + replace a with (T + (a - T)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ T ATABLE (a - T));
      [apply in_or_app; left; unfold rf_tblk; rewrite (proj2 (Z.eqb_neq T 0) HT0); left; reflexivity
      | change (req_size ATABLE) with 896; unfold p in Hf; lia].
    + exists T, ATABLE. split; [exact HTB4 | change (req_size ATABLE) with 896; unfold p in Hf; lia].
  - destruct (inFP_ablocks_fp_inv _ a Hf) as (b & m & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. split.
      * replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [|lia].
        apply in_or_app; right; apply in_or_app; left. unfold rf_eblks. apply in_concat. exists (aentry_blks e).
        split; [apply in_map, nth_In; lia|]. change (aentry_blks e) with (rfl_bblk e ++ gse_blks e).
        apply in_or_app; right; exact Hin.
      * exists b, m. split; [exact (HX4 _ (GX _ Hin)) | exact Hr].
    + destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly S)) as [Hin0 | Hnin0].
      * left. split; [|exists b, m; split; [exact (HX4 _ (OX _ Hin)) | exact Hr]].
        assert (Hin1 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest))
        by (eapply Permutation_in; [exact HPERM0 | exact Hin0]).
        assert (Hin2 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
        { rewrite !app_assoc in Hin1. rewrite !app_assoc. apply in_app_or in Hin1. destruct Hin1 as [H1 | H1]; [exact H1|].
          exfalso. pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HNf.
          inversion HNf as [|y0 l0 _ HNXf]; subst y0 l0.
          exact (rfl_nodup_app_r _ _ (b, m) (rfl_nodup_tl _ _ (rfl_nodup_tl _ _ HNXf)) Hin H1). }
        replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [exact Hin2 | lia].
      * right. exists b, m. split; [exact (HX4 _ (OX _ Hin)) | split; [exact Hnin0 | exact Hr]]. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G RF_STK sp0 0 [] (rf_FP T es cap out) ly S Hp W mem md []
  ly4 S4 Hp4 W4 (ms_mem msG) _ _ GSE_STK (spZ (ms_regs msG)) 0 [] _ [] ly5 S5 Hp5 W5 mem5 md5 k5 HJ4 HJslG
  ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia)
  ltac:(intros a Hf; exfalso; exact (inFP_nil a Hf)) HG FPC) as HJ6.
cbn [app] in HJ6.
(* what gestures_end kept: every image byte outside G_SL, and live blocks' bytes outside its footprint *)
pose proof (ajournal_gx_inner_x SEGS B PST ARx (G_SL B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS6 & HJin6 & HagS6).
pose proof HJin6 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (HFPC1 : ~ YI16.sink_open_fp ((p + 40, p + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL))).
{ apply sink_closed_pos. constructor; [cbn [fst]; unfold p; lia|]. unfold ablocks_fp. apply Forall_map.
  apply Forall_forall. intros [b m] Hb. cbn [fst].
  assert (Hb4 : In (b, m) (ablocks B ly4 S4))
  by (apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [exact (HX4 _ (GX _ Hb)) | exact (HX4 _ (OX _ Hb))]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ b m HAR5 Hb4) as (_ & H4096 & _). lia. }
assert (KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msG) a).
{ intros a Ha Ho He Hps Hg. rewrite (G3 a Ha Ho He Hps (fp_spares_closed _ a HFPC1)).
  apply HagS6. rewrite unsigned_lit_small; [exact Hg|]. pose proof (Hsegs a Ha). unfold kLowMemEnd in *. lia. }
assert (NGN : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 1%nat).
assert (VN5a : val_mem SEGS (mrestrict (w_H W4) (ms_mem msG)) (rg_nsrc RG) 4 n)
by (apply (val_mem_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem msG)); [intros q _; apply AV2 | exact VN4]).
assert (VN5 : val_mem SEGS (mrestrict (w_H W5) mem5) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H W4) (w_H W5) (ms_mem msG) mem5); [|exact VN5a].
  intros q Hq. destruct (HPLAIN (rg_nsrc RG + q) (Hnsrc (rg_nsrc RG + q) ltac:(lia))) as (Hq1 & Hq2 & Hq3).
  exact (KG _ Hq1 Hq2 Hq3 (PSTC _ (Hnsrc (rg_nsrc RG + q) ltac:(lia))) (NGN (rg_nsrc RG + q) ltac:(lia))). }
jafter_call_keep_pi HS 52%nat regs5 (mrestrict (w_H W5) mem5) HPsl [1]%nat HS6.
match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  apply (region_kept_val_at Ea _ _ 245%nat (rg_nsrc RG) 4 n);
  [change 245%nat with (A_OBJ 4); rewrite <- HV4; exact (HEIa (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | exact VN5a | exact VN5 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc Ea 52 (map (getr regs5) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (SHOK6 : sh_ok SEGS rfl_Bx [] Eb (mrestrict (w_H W5) mem5)) by constructor.
paj_run_tok_x RUN HS HJ6 SHOK6 Bspan. { rf_awr. }
(* ---- the round's end state N (the last run wrote nothing): what RFI at i + 1 and RFX need ---- *)
rfl_cur HS msN.
assert (MEQc : forall x, mrestrict (w_H W5) mem5 x = mrestrict (w_H W5) mem5 x) by reflexivity.
rfl_meq MEQc MEQ4.
assert (AV3 : forall a, aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H W5) mem5 a) by (intros a; apply aview_eq_of; apply MEQ4).
assert (MG3 : mem_grows (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem msN))) by (intros x Hx; rewrite MEQ4; exact Hx).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
(* the read-only view after gestures_end: its journal at G_SL keeps it (rom_out of G_SL) *)
assert (ROM6 : rom_view SEGS W5 mem5).
{ eapply (ajournal_gx_rom_view_x SEGS B PST ARx). all: first [exact LAWS | exact Hsegs | exact HJsl | exact HROMO | exact PSTR | exact ROM5]. }
assert (ROMN : rom_view SEGS W5 (ms_mem msN)) by (intros a Ha; rewrite AV3; exact (ROM6 a Ha)).
assert (KNI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H WL) memL a).
{ intros a Ha Ho He Hps Hg. rewrite AV3, (KG a Ha Ho He Hps Hg), AV2, (KF3 a Ha Ho He). apply AV1. }
assert (RFW : forall a, inG rf_cells a -> writable_at SEGS (arm W5 (ms_mem msN)) a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
  apply (hidden_not_img SEGS W5). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (KCELL : forall lo len, (forall x, lo <= x < lo + len -> inG rf_cells x /\ ~ inG (G_SL B RG) x) ->
  forall q, lo <= q < lo + len -> abyte_kept WL memL W5 (ms_mem msN) q).
{ intros lo len Hc q Hq. destruct (Hc q Hq) as [Hq1 Hq2]. destruct (HPLAIN q Hq1) as (Hi1 & Ho1 & He1).
  split; [exact (KNI q Hi1 Ho1 He1 (PSTC q Hq1) Hq2) | intros _; exact (RFW q Hq1)]. }
assert (NGL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 0%nat).
assert (NGG : forall a, GL <= a < GL + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 3%nat).
assert (NGS : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 12%nat).
assert (NGC : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 13%nat).
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 1%nat _ 12 a eq_refl Ha)).
assert (ICS : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 4%nat _ 4 a eq_refl Ha)).
assert (IGL : forall a, GL <= a < GL + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 6%nat _ 4 a eq_refl Ha)).
assert (VNN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HNS]. intros q Hq.
  exact (proj1 (KCELL (rg_nsrc RG) 4 (fun x Hx => conj (Hnsrc x Hx) (NGN x Hx)) (rg_nsrc RG + q) ltac:(lia))). }
assert (VSN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HSRC]. intros q Hq.
  exact (proj1 (KCELL (rg_src RG) 8 (fun x Hx => conj (Hsrc x Hx) (NGS x Hx)) (rg_src RG + q) ltac:(lia))). }
assert (VCN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_capsrc RG) 4 16).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HCAP]. intros q Hq.
  exact (proj1 (KCELL (rg_capsrc RG) 4 (fun x Hx => conj (ICS x Hx) (NGC x Hx)) (rg_capsrc RG + q) ltac:(lia))). }
assert (WNN : awr W5 (ms_mem msN) (rg_nsrc RG) 4) by (intros j Hj; exact (RFW _ (Hnsrc (rg_nsrc RG + j) ltac:(lia)))).
assert (WSN : awr W5 (ms_mem msN) (rg_src RG) 8) by (intros j Hj; exact (RFW _ (Hsrc (rg_src RG + j) ltac:(lia)))).
assert (WCN : awr W5 (ms_mem msN) (rg_capsrc RG) 4) by (intros j Hj; exact (RFW _ (ICS (rg_capsrc RG + j) ltac:(lia)))).
assert (LKN : alock_at RG W5 (ms_mem msN) true).
{ apply (alock_at_kept RG WL memL W5 (ms_mem msN) true HLK). intros r [<- | []] a Har. cbn [fst snd] in Har.
  exact (KCELL (rg_lock RG) 12 (fun x Hx => conj (ILK x Hx) (NGL x Hx)) a Har). }
assert (GLN : exists lst, val_mem SEGS (arm W5 (ms_mem msN)) GL 4 lst).
{ destruct HGLv as [lst Hl]. exists lst. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact Hl].
  intros q Hq. exact (proj1 (KCELL GL 4 (fun x Hx => conj (IGL x Hx) (NGG x Hx)) (GL + q) ltac:(lia))). }
assert (GLW : awr W5 (ms_mem msN) GL 4) by (intros j Hj; exact (RFW _ (IGL (GL + j) ltac:(lia)))).
assert (HTBN : In (T, ATABLE) (ablocks B ly5 S5)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | left; reflexivity]).
(* the round's own stack frame [sp0 - 48, sp0) is kept: the callees run below sp0 - 48 *)
assert (KNF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H WL) memL a).
{ intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (clear - Ha HceilS RSTK0 HshiE H47E; unfold ASTACK in *; lia).
  rewrite AV3. rewrite (G1 a Hac ltac:(rewrite Usp5; lia)).
  rewrite HagS6; [rewrite AV2, (KF1 a Hac ltac:(lia)); apply AV1|].
  rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as (Hi1 & _ & _). pose proof (Hsegs a Hi1).
  unfold kLowMemEnd in *. lia. }
assert (RSV : rf_saved W5 (ms_mem msN) sp0 regs).
{ intros k0 Hk0. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact (HSV k0 Hk0)].
  intros q Hq. apply KNF. lia. }
(* the entries the loop has not reached keep their bytes and blocks: none of them is in gestures_end's footprint *)
pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HND4.
assert (HRN : forall b, In b (rf_eblks (skipn (Datatypes.S i) es) ++ rest) -> In b (ablocks B ly5 S5))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; right; exact Hb]).
assert (EX : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (KR : forall b m x, In (b, m) ((T, ATABLE) :: X) -> In (b, m) (ablocks B ly5 S5) ->
  ~ In (b, m) (gse_blks e ++ aout_blks (gse_cap r0) outL) -> b <= x < b + req_size m -> ~ (p + 40 <= x < p + 52) ->
  aview SEGS (w_H W5) (ms_mem msN) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hin5 Hng Hx Hs. rewrite AV3.
  assert (Hin4 : In (b, m) (ablocks B ly4 S4)) by (destruct Hin as [<- | Hin]; [exact HTB4 | exact (HX4 _ Hin)]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ b m HAR5 Hin4) as (_ & Hb4096 & Hbceil & _).
  replace x with (b + (x - b)) by lia. rewrite (G2 b m (x - b) Hin4 Hin5 ltac:(lia)).
  - rewrite HagS6.
    + replace (b + (x - b)) with x by lia. exact (KB b m x Hin Hx).
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as (Hi2 & _ & _).
      exact (blk_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m (b + (x - b)) HAR5 Hin4 ltac:(lia) Hi2).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia|].
    destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
    assert (Hin4' : In (b', m') (ablocks B ly4 S4))
    by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
    assert (Hne : (b, m) <> (b', m')) by (intros Heq; apply Hng; rewrite Heq; exact Hin').
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m b' m' HAR5 Hin4 Hin4' Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ENTN : forall j, (Datatypes.S i <= j < length es)%nat ->
  garr8 SEGS (arm W5 (ms_mem msN)) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
  awr W5 (ms_mem msN) (T + AENT * Z.of_nat j) AENT /\
  aheld_ok B ly5 S5 W5 (ms_mem msN) (nth j es rf_e0) /\
  ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
   (0 < re_cap (nth j es rf_e0) /\ In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly5 S5)))).
{ intros j Hj. destruct (HENT j ltac:(lia)) as (Gj & Aj & Hj' & Bj). pose proof Hj' as (Pj1 & Pj2 & _).
  assert (Hej : In (nth j es rf_e0) (skipn (Datatypes.S i) es)) by (apply rfl_in_skipn; lia).
  assert (EBj : forall b, In b (aentry_blks (nth j es rf_e0)) -> In b (rf_eblks (skipn (Datatypes.S i) es)))
  by (intros b Hb; unfold rf_eblks; apply in_concat; exists (aentry_blks (nth j es rf_e0)); split; [apply in_map; exact Hej | exact Hb]).
  inversion HND4 as [|y0 l0 HnT HNX]; subst y0 l0.
  assert (NGj : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> ~ In b (gse_blks e ++ aout_blks (gse_cap r0) outL)).
  { intros b Hb Hb2. apply in_app_or in Hb2. destruct Hb2 as [Hb2 | Hb2].
    - exact (rfl_nodup_app_r _ _ b HNX Hb2 (in_or_app _ _ _ (or_introl Hb))).
    - pose proof (rfl_nodup_tl _ _ HNX) as HNX'.
      exact (rfl_nodup_app_r _ _ b HNX' Hb (in_or_app _ _ _ (or_introl Hb2))). }
  assert (NGT : ~ In (T, ATABLE) (gse_blks e ++ aout_blks (gse_cap r0) outL)).
  { intros Hb2. apply HnT. apply in_app_or in Hb2. destruct Hb2 as [Hb2 | Hb2]; [exact (GX _ Hb2) | exact (OX _ Hb2)]. }
  assert (NTj : forall b m x, In (b, m) (rf_eblks (skipn (Datatypes.S i) es)) -> b <= x < b + req_size m ->
    ~ (T <= x < T + 896)).
  { intros b m x Hb Hx Hx2.
    assert (Hne : (b, m) <> (T, ATABLE)) by (intros Heq; apply HnT; rewrite <- Heq; exact (EX _ Hb)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m T ATABLE HAR5 (HX4 _ (EX _ Hb)) HTB4 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D. lia. }
  split; [|split; [|split]].
  - apply (garr8_frame SEGS (arm WL memL) (arm W5 (ms_mem msN)) _ _ Gj). intros x Hx.
    rewrite (rfl_len_entry _ Pj1 Pj2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
    apply (KR T ATABLE x (or_introl eq_refl) HTBN NGT); [change (req_size ATABLE) with 896; unfold AENT in Hx; lia | unfold p, AENT in *; lia].
  - intros q Hq. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly5 S5 _ W5 (ms_mem msN) _ T ATABLE HAR6 HTBN) as (_ & _ & _ & _ & HP & _).
    change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
  - apply (rfl_aheld_ok_kept lyL SL WL memL ly5 S5 W5 (ms_mem msN) _ Hj').
    + intros b Hb. apply HRN. apply in_or_app; left. apply EBj.
      change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
      apply in_or_app; right; exact Hb.
    + intros b m x Hb Hx.
      assert (HbE : In (b, m) (rf_eblks (skipn (Datatypes.S i) es))).
      { apply EBj. change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
        apply in_or_app; right; exact Hb. }
      pose proof (HrqG m) as Hm.
      apply (KR b m x (or_intror (EX _ HbE)) (HRN _ (in_or_app _ _ _ (or_introl HbE))) (NGj _ HbE)); [lia|].
      intros Hs. apply (NTj b m x HbE ltac:(lia)). unfold p in Hs. lia.
  - destruct Bj as [Bj | (Bc & Bin)]; [left; exact Bj | right; split; [exact Bc|]].
    apply HRN. apply in_or_app; left. apply EBj. unfold aentry_blks.
    rewrite (proj2 (Z.eqb_neq (re_cap (nth j es rf_e0)) 0) ltac:(lia)). left; reflexivity. }
(* the stream, the blocks, presence, the meter and the model after round i *)
assert (AOUTN : aout_at B RG ly5 S5 W5 (ms_mem msN) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5).
{ apply (aout_at_kept B RG ly5 S5 W5 mem5 ly5 S5 W5 (ms_mem msN) _ _ mx _ _ out5 HAOsl).
  - intros r Hr a Har. split; [apply AV3 | apply (writable_at_grows SEGS _ _ a MG3)].
  - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]. }
assert (PERMN : Permutation (ablocks B ly5 S5)
  (rf_tblk T ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r1) out5 ++ rest)).
{ eapply Permutation_trans; [exact HPERMsl|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0). cbn [app].
  apply perm_skip. apply Permutation_app_swap_app. }
assert (APK : apres_kept B W mem W5 (ms_mem msN)).
{ intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) mem5 (ms_mem msN) a MG3). apply (HPKsl a Ha Ho He).
  apply (PR2 a Ha Ho He). exact (HPK a Ha Ho He Hpr). }
assert (MLE : mo_le MT S S5 (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)))
by (exact (mle_station MT S S4 S5 _ _ MLAW (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) HMOsl)).
assert (NNL : forall b, In b (ablocks B lyL SL) -> 0 <= snd b).
{ intros [bb mm] Hb. cbn [snd]. exact (BLKN lyL SL HpL WL memL mdL bb mm HARL Hb). }
assert (INL : forall b, In b ((T, ATABLE) :: rfl_bblk e ++ X) -> In b (ablocks B lyL SL))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM' | exact Hb]).
(* rf_room's `- cap` threading (W_contract.v rf_room): the round frees the OLD g_out block (outL, gse_cap r0) and
   holds the new one (out5, gse_cap r1), so the rest's room grows only by gse_cap r1 - gse_cap r0; the old block's
   bytes are exactly gse_cap r0 (rfl_bsum_aout_eq), not merely nonnegative *)
assert (HBB5 : blocks_bytes S5 <= blocks_bytes SL + gse_cap r1 - gse_cap r0).
{ rewrite (blocks_bytes_bsum B ly5 S5), (blocks_bytes_bsum B lyL SL), (bsum_perm _ _ HPERMsl), (bsum_perm _ _ HPERM').
  rewrite !bsum_cons, !bsum_app. unfold X. rewrite !bsum_app.
  pose proof (rfl_bsum_aout (gse_cap r1) out5 Hgk0).
  pose proof (rfl_bsum_nonneg (rfl_bblk e) (fun b Hb => NNL b (INL b (or_intror (in_or_app _ _ _ (or_introl Hb)))))).
  pose proof (rfl_bsum_nonneg (gse_blks e) (fun b Hb => NNL b (INL b (or_intror (in_or_app _ _ _ (or_intror (GX _ Hb))))))).
  rewrite (rfl_bsum_aout_eq (gse_cap r0) outL).
  lia. }
assert (ROOMN : rf_room MMAX (blocks_bytes S5) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) (skipn (Datatypes.S i) es))
by (exact (rfl_room_mono _ _ _ _ _ _ _ _ HBB5 HR2)).
assert (RUNS : rf_run c O mx no cap (firstn (Datatypes.S i) es) = (gse_c r1, gse_O r1, gse_no r1, gse_cap r1))
by (rewrite (rfl_firstn_S es i Hi), rfl_run_app; reflexivity).
assert (U19 : U Eb (SOff 19 1) = Z.of_nat i + 1).
{ apply (U_atom_off Eb 19 (Z.of_nat i) 1); [rewrite OLDb, OLDa, (EE 19%nat 19%bv eq_refl) by lia; exact H19 | lia | lia]. }
assert (U35 : U Eb (SOff 35 0) = n) by (apply (U_atom Eb 35 n); [rewrite OLDb, OLDa by lia; exact E35 | unfold n; lia]).
assert (RKF : forall regsF : bvmap 5 word,
  (forall r, In r [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsF r = getr regsL r) ->
  getr regsF 9 = ew Eb 285 -> getr regsF 20 = ew Eb 286 ->
  rf_kept regs regsF sp0 /\ getr regsF 8 = w64 SB /\ getr regsF 20 = w64 (VAL (A_HI 6))).
{ intros regsF HKN N9 N20. split; [|split].
  - unfold rf_kept.
    split; [unfold spZ in Ksp |- *; rewrite (HKN 2%bv ltac:(cbv; tauto)); exact Ksp|].
    split; [rewrite (HKN 3%bv ltac:(cbv; tauto)); exact K3|].
    split; [rewrite (HKN 4%bv ltac:(cbv; tauto)); exact K4|].
    split; [rewrite (HKN 21%bv ltac:(cbv; tauto)); exact K21|].
    split; [rewrite (HKN 22%bv ltac:(cbv; tauto)); exact K22|].
    split; [rewrite (HKN 23%bv ltac:(cbv; tauto)); exact K23|].
    split; [rewrite (HKN 24%bv ltac:(cbv; tauto)); exact K24|].
    split; [rewrite (HKN 25%bv ltac:(cbv; tauto)); exact K25|].
    split; [rewrite (HKN 26%bv ltac:(cbv; tauto)); exact K26|].
    split; [rewrite (HKN 27%bv ltac:(cbv; tauto)); exact K27|].
    rewrite N9. change 285%nat with (A_HI 5). exact (img_env_atomP Eb (A_HI 5) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
  - rewrite (HKN 8%bv ltac:(cbv; tauto)). exact H8.
  - rewrite N20. change 286%nat with (A_HI 6). exact (img_env_atomP Eb (A_HI 6) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)). }
(* the branch and the jump to its target write nothing: every fact above carries to the final memory *)
assert (FIN : forall m, (forall a, aview SEGS (w_H W5) m a = aview SEGS (w_H W5) (ms_mem msN) a) ->
  mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) m) ->
  rf_saved W5 m sp0 regs /\
  val_mem SEGS (arm W5 m) (rg_nsrc RG) 4 n /\ awr W5 m (rg_nsrc RG) 4 /\
  val_mem SEGS (arm W5 m) (rg_src RG) 8 T /\ awr W5 m (rg_src RG) 8 /\
  val_mem SEGS (arm W5 m) (rg_capsrc RG) 4 16 /\ awr W5 m (rg_capsrc RG) 4 /\
  (forall j, (Datatypes.S i <= j < length es)%nat ->
    garr8 SEGS (arm W5 m) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
    awr W5 m (T + AENT * Z.of_nat j) AENT /\
    aheld_ok B ly5 S5 W5 m (nth j es rf_e0) /\
    ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
     (0 < re_cap (nth j es rf_e0) /\ In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly5 S5)))) /\
  alock_at RG W5 m true /\
  aout_at B RG ly5 S5 W5 m (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5 /\
  (exists lst, val_mem SEGS (arm W5 m) GL 4 lst) /\ awr W5 m GL 4 /\
  apres_kept B W mem W5 m).
{ intros m AVF MGF.
  assert (KF : forall a, abyte_kept W5 (ms_mem msN) W5 m a)
  by (intros a; split; [apply AVF | apply (writable_at_grows SEGS _ _ a MGF)]).
  split; [intros k0 Hk0; apply (val_mem_kept SEGS (w_H W5) (w_H W5) (ms_mem msN) m); [intros q _; apply AVF | exact (RSV k0 Hk0)]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VNN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WNN]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VSN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WSN]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VCN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WCN]|].
  split.
  { intros j Hj. destruct (ENTN j Hj) as (G1' & A1' & H1' & B1'). split; [|split; [|split]].
    - apply (akept_garr8 W5 (ms_mem msN)); [intros x _; apply KF | exact G1'].
    - apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact A1'].
    - exact (rfl_aheld_ok_mem ly5 S5 W5 (ms_mem msN) W5 m _ H1' AVF).
    - exact B1'. }
  split; [apply (alock_at_kept RG W5 (ms_mem msN) W5 m true LKN); intros r _ a _; apply KF|].
  split; [apply (aout_at_kept B RG ly5 S5 W5 (ms_mem msN) ly5 S5 W5 m _ _ mx _ _ out5 AOUTN);
    [intros r _ a _; apply KF
    | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]]|].
  split; [destruct GLN as [lst Hl]; exists lst; apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact Hl]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact GLW]|].
  intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) (ms_mem msN) m a MGF). exact (APK a Ha Ho He Hpr). }
psrr_branch_tok RUN BR HS SHOK6 Bspan.
- (* i + 1 < |es|: back to the loop head, RFI at i + 1 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U19, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U19, ?U35; unfold n; lia). rewrite U19, U35 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x RUNTO HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 0x7c). { rf_awr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem msN) a)
  by (intros a; apply aview_eq_of; apply Hx; rfl_nowr) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  assert (ROMF : rom_view SEGS W5 (ms_mem msF)) by (intros a Ha; rewrite AV4; exact (ROMN a Ha));
  assert (E5F : garr8 SEGS (arm W5 (ms_mem msF)) (VAL A_lit_end5) (bzs END5))
  by (exact (rfl_end5_kept WL W5 memL (ms_mem msF) HROM ROMF HEND5));
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  pmkst HS.
  apply (IH regs ly S Hp W mem md T es c O mx no cap out rest (Datatypes.S i) ly5 S5 Hp5 W5); [lia | exact HCNT0 |].
  assert (RC : gse_c (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (RO : gse_O (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_cap r1) by (rewrite RUNS; reflexivity).
  destruct (RKF _ HKN2 N9 N20) as (RK1 & RK2 & RK3).
  refine (ex_intro _ _ (ex_intro _ out5 (ex_intro _ (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) _))).
  rewrite RC, RO, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact RK1|].
  split; [exact RK2|].
  split; [exact RK3|].
  split; [rewrite N19, OLDb, OLDa, (EE 19%nat 19%bv eq_refl), H19 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N18, OLDb, OLDa, (EE 18%nat 18%bv eq_refl), H18 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [exact RSVF|].
  split; [lia|]. split; [exact Hn16|]. split; [exact HT0|].
  split; [exact VNF|]. split; [exact WNF|]. split; [exact VSF|]. split; [exact WSF|]. split; [exact VCF|]. split; [exact WCF|].
  split; [exact HTBN|].
  split; [exact ENTF|].
  split; [exact LKF|].
  split; [exact AOUTF|].
  split; [exact PERMN|].
  split; [exact GLF|]. split; [exact GLWF|].
  split; [exact E5F|]. split; [exact ROMF|].
  split; [exact APKF|].
  split; [exact ROOMN|].
  split; [exact MLE|].
  split; [lia|].
  split; [exact HMOK|].
  (* the room round: gestures_end's post leaves what the rounds after this one are owed, then kr *)
  exact HRMsl.
- (* i + 1 = |es|: the tail, RFX *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U19, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U19, ?U35; unfold n; lia). rewrite U19, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Hlast : Datatypes.S i = length es) by (unfold n in Hc; lia).
  paj_run_to_tok_x RUNTO HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 0xf8). { rf_awr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem msN) a)
  by (intros a; apply aview_eq_of; apply Hx; rfl_nowr) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (9%bv : bv 5) N9. prreg HS (20%bv : bv 5) N20.
  pmkst HS.
  assert (SK0 : skipn (Datatypes.S i) es = []) by (rewrite Hlast; apply skipn_all).
  assert (FA : firstn (Datatypes.S i) es = es) by (rewrite Hlast; apply firstn_all).
  rewrite SK0 in HSP, PERMN. cbn [rf_cost rf_eblks concat map app] in HSP, PERMN. rewrite FA in RUNS.
  assert (RC : gse_c (rf_run c O mx no cap es) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (RO : gse_O (rf_run c O mx no cap es) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap es) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap es) = gse_cap r1) by (rewrite RUNS; reflexivity).
  destruct (RKF _ HKN2 N9 N20) as (RK1 & _ & _).
  apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest ly5 S5 Hp5 W5).
  refine (ex_intro _ _ (ex_intro _ out5 _)).
  rewrite RC, RO, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact RK1|].
  split; [exact RSVF|].
  split; [split; [exact WNF | right; split; [exact HT0 | split; [exact VSF | split; [exact WSF | split; [exact VCF | split; [exact WCF | exact HTBN]]]]]]|].
  split; [exact LKF|].
  split; [exact AOUTF|].
  split; [exact PERMN|].
  split; [exact GLF|]. split; [exact GLWF|].
  split; [exact APKF|].
  split; [apply (mle_weaken MT S S5 _ _ MLAW MLE); lia|].
  (* the room round: no round is left, so gestures_end's post leaves exactly kr *)
  refine (@eq_ind _ _ (rp_RM RP S5) HRMsl _ _). unfold kr5. rewrite SK0. reflexivity.
Qed.
(* the table's entries, one by one: the j-th 56-byte entry_bytes of the table's concatenation *)
Lemma rf_garr8_entry : forall m (es : list rentry) a tail j,
Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
garr8 SEGS m a (bzs (concat (map entry_bytes es) ++ tail)) -> (j < length es)%nat ->
garr8 SEGS m (a + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))).
Proof.
induction es as [|e es IH]; intros a tail j HP Hg Hj; [cbn in Hj; lia|].
inversion HP as [|e' es' [P1 P2] HP']; subst.
cbn [map concat] in Hg. unfold bzs in Hg. rewrite <- app_assoc, map_app in Hg.
apply garr8_app in Hg as [Hg1 Hg2].
destruct j as [|j].
- cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. exact Hg1.
- cbn [nth].
  assert (HL : Z.of_nat (length (map bz (entry_bytes e))) = AENT)
  by (pose proof (rfl_len_entry e P1 P2) as L; unfold bzs in L; rewrite L; reflexivity).
  rewrite HL in Hg2. try rewrite <- map_app in Hg2. fold (bzs (concat (map entry_bytes es) ++ tail)) in Hg2.
  replace (a + AENT * Z.of_nat (S j)) with (a + AENT + AENT * Z.of_nat j) by lia.
  exact (IH (a + AENT) tail j HP' Hg2 ltac:(cbn in Hj; lia)).
Qed.
(* ---- THE GENERIC WALK: the prologue, the g_thread_up test (not taken: rf_spec_x gives the byte 0), the lock, the
   load of g_nsrc and the blez; then the tail X directly (no source) or the loop L from i = 0.  The room round: the
   prologue, the test and the lock do not change the allocator state, so rf_spec_x's budget is the loop's at round 0
   and, with no source, rf_post_x's kr (rf_cost of [] is 0); its count premise is the loop's. ---- *)
Theorem pb_relay_finish_x : rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX (BASE + AF_fr_relay_finish).
Proof.
unfold rf_spec_x. intros W ly S Hp regs mem md ch T es c O mx no cap out rest
HPRE Hal32 HCNT HGTU0 HLOCK HREL HGLv HGLw HOUT HPERM HEND5 HROM HG1 HG2 HG3 HROOM HCTX HMOK kr HRMe HCNTe.
change (BASE + AF_fr_relay_finish) with A_relay_finishP.
pose proof (rf_loop rf_tail HCTX) as LOOP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rf_entry W ly S Hp regs mem md ch HPRE HGTU0) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16672) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RF_STK (rf_FP T es cap out) ly S Hp W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs rf_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rf_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_relay_finishP) with (Z_to_bv 64 A_relay_finishP). unfold A_relay_finishP, A_relay_finish.
paj_run_tok_x RUN0 HS HJ SHOK Bspan. { awr_any. exact Usp. }
lazymatch goal with Hx : mem_grows _ _ |- _ => rename Hx into MG0 end.
lazymatch goal with Hx : frame_of _ _ _ _ |- _ => rename Hx into HFr0 end.
(* the prologue run writes only the frame [sp0 - 48, sp0) *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr0 a Ha).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia | ]).
  destruct Hin. }
assert (P0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
by (intros a Ha; exact (apresent_grows (w_H W) mem (ms_mem ms) a MG0 Ha)).
assert (WK0 : forall a, writable_at SEGS (arm W mem) a -> writable_at SEGS (arm W (ms_mem ms)) a)
by (intros a Ha; exact (writable_at_grows SEGS _ _ a MG0 Ha)).
(* the six saved words, as the prologue stored them *)
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (SV0 : rf_saved W (ms_mem ms) (spZ regs) regs).
{ intros k Hk.
  destruct k as [|[|[|[|[|[|k]]]]]]; [ | | | | | | lia].
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 20%bv 20%nat (-48) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 0) with (spZ regs + -48) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 19%bv 19%nat (-40) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 1) with (spZ regs + -40) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 18%bv 18%nat (-32) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 2) with (spZ regs + -32) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 9%bv 9%nat (-24) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 3) with (spZ regs + -24) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 8%bv 8%nat (-16) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 4) with (spZ regs + -16) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 1%bv 1%nat (-8) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 5) with (spZ regs + -8) by lia. exact V. }
clear HR0.
(* the call to pthread_mutex_lock (&g_lock) *)
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md
  _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ | apply gagree_refl | intros a Ha Hn; lia]. }
assert (HPOS : Forall (fun b : Z * Z => 0 < fst b) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
{ apply Forall_forall. intros [p n] Hb. cbn [fst].
  assert (Hin : In (p, n) (ablocks B ly S)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
    apply in_app_iff in Hb. apply in_or_app.
    destruct Hb as [Hb | Hb]; [left; exact Hb|]. right.
    apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb | Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md p n HAR Hin) as (_ & H4096 & _). lia. }
assert (HFPC : ~ YI16.sink_open_fp (rf_FP T es cap out))
by (unfold rf_FP; exact (sink_closed_ablocks_fp _ HPOS)).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed _ a HFPC)). }
pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a)
by (intros a Ha; exact (in_rf_cell 1%nat (rg_lock RG) 12 a eq_refl Ha)).
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as HLKb. cbn [fst snd] in HLKb.
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; destruct (HPLAIN a (ILK a Ha)) as (Hi & Ho & He); exact (KIMG a Hi Ho He (PSTC a (ILK a Ha)))).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms) = spZ regs + -48).
{ unfold spZ at 1. rewrite QSP, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3). rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV3. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-48) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (LKK a ltac:(lia)). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + exact RGAL.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4m.
    + intros a Ha. split; [rewrite (LKK a ltac:(lia)); exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. destruct (HPLAIN a (ILK a ltac:(lia))) as (Hi & Ho & He). split; [|split].
      * apply rf_writable_of_seg; [exact (hidden_not_img SEGS W (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hi))
        | exact (HWSEG a (ILK a ltac:(lia)))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))).
      apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
jafter_call_keep_pi HS 33%nat regs3 (mrestrict (w_H W) mem3) HP3 ([] : list nat) HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* the saved words survive the lock (it writes only the lock word and its scratch below sp0 - 48) *)
assert (SV3 : rf_saved W mem3 (spZ regs) regs).
{ intros k Hk. apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms) mem3); [|exact (SV0 k Hk)].
  intros q Hq. apply Hfr3; [lia | lia | unfold ESTACK; lia]. }
(* the env after the call *)
remember (YN3v.havoc E 33 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 33)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rf_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
(* the relay's count, as the walk finds it: |es| in both arms of ra_rel (T = 0 forces es = []) *)
assert (NS0 : val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr W mem (rg_nsrc RG) 4).
{ destruct HREL as [(HT0 & Hes0 & (_ & _ & Hv & Hw & _)) | (_ & _ & Hv & Hw & _)];
  [rewrite Hes0; cbn [length Z.of_nat]; split; [exact Hv | exact Hw] | split; [exact Hv | exact Hw]]. }
assert (IGB : forall a, inG rf_cells a -> 0x10000 <= a /\ a < 0x5fc000).
{ intros a Ha. unfold inG, rf_cells in Ha. apply Exists_exists in Ha. destruct Ha as ((lo, sz) & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) HIG (lo, sz) Hin) as Hbb. unfold in_zr in Hr.
  cbn [fst snd] in Hbb, Hr. lia. }
assert (KC3 : forall a, inG rf_cells a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnl. destruct (HPLAIN a Ha) as (Hi & Ho & He). destruct (IGB a Ha) as (Hb1 & Hb2).
  rewrite (Hfr3 a ltac:(lia) Hnl ltac:(clear -Hb1 Hb2 Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He (PSTC a Ha)). }
zsep_pick HSEPG 3%nat 4%nat DLN.
assert (NS3 : val_mem SEGS (arm W mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 (Z.of_nat (length es)));
  [intros k Hk; apply KC3; [apply (in_rf_cell 2%nat (rg_nsrc RG) 4 (rg_nsrc RG + k) eq_refl); lia | lia]
  | exact (proj1 NS0)]. }
assert (NSB : (length es <= 16)%nat).
{ destruct HREL as [(_ & Hes0 & _) | (_ & _ & _ & _ & _ & _ & Hle & _)]; [rewrite Hes0; cbn [length]; lia | exact Hle]. }
(* the g_nsrc cell as a region: the lw at 0x823ac reads it through the object atom (HV4) *)
pose proof (st_ok_pi_havoc_hi 49 Ea _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (YN3v.havoc Ea 49 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDd : forall m, (m < 49)%nat -> ew Ed m = ew Ea m)
by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E49 : ew Ed 49 = Z_to_bv 64 (Z.of_nat (length es)))
by (rewrite HEd; exact (ew_havoc_new Ea 49 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rf_extra) Ed)
by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEd.
assert (U245d : bv_unsigned (ew Ed (A_OBJ 4)) = rg_nsrc RG)
by (rewrite <- HV4; exact (HEId (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB4 : base_val Ed (Some (A_OBJ 4)) = rg_nsrc RG) by (cbn [base_val]; exact U245d).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb.
cbn [fst snd] in HNSb.
pose proof (st_ok_pi_add_region Ed _ _
  (YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 49 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
        rewrite VB4; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        constructor; [|constructor];
        apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 49 0) (Z.of_nat (length es)));
        [cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        rewrite Z.add_0_r; exact NS3)
  ltac:(cbn [all_disjoint]; exact I)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (SHOKd : sh_ok SEGS Bx rf_SH0 Ed (mrestrict (w_H W) mem3)) by (unfold sh_ok, rf_SH0; constructor).
paj_run_tok_x RUN HS HJX3 SHOKd Bspan.
{ apply awr_ok_x_of0. intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
  destruct Hin. }
rfl_cur HS msB.
assert (MEQ0 : forall x, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem3 x) by reflexivity.
rfl_meq MEQ0 MEQ1.
(* the value the blez compares: g_nsrc is |es|, loaded as a signed 4-byte cell *)
assert (HNU : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 49 0))) = Z.of_nat (length es)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 49 0))) with (U Ed (SOff 49 0)).
  rewrite (U_atom Ed 49 (Z.of_nat (length es)) E49 ltac:(lia)). apply sx32_small. lia. }
assert (HNS : bv_signed (sv_denot Ed (SExt true 32 (SOff 49 0))) = Z.of_nat (length es))
by (rewrite bv_signed_small by (rewrite HNU; lia); exact HNU).
assert (HZ0 : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity.
(* the entry registers, read through the env at the two cut points *)
assert (RG0 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ed n = getr regs r)
by (intros n r Hn Hnr; rewrite OLDd, OLDa by lia; exact (EE n r Hnr)).
assert (UH5 : ew Ed 285 = w64 (VAL (A_HI 5)))
by (change 285%nat with (A_HI 5); exact (img_env_atomP Ed (A_HI 5) HEId ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
assert (UH6 : ew Ed 286 = w64 (VAL (A_HI 6)))
by (change 286%nat with (A_HI 6); exact (img_env_atomP Ed (A_HI 6) HEId ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
(* everything the cut points carry from the entry, at any memory the walk sees as mem3 *)
assert (CELLS : forall m, (forall x, mrestrict (w_H W) m x = mrestrict (w_H W) mem3 x) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W m a) /\
  (forall a, inG rf_cells a -> writable_at SEGS (arm W m) a) /\
  rf_saved W m (spZ regs) regs /\ alock_at RG W m true /\ aout_at B RG ly S W m c O mx no cap out /\
  (exists lst, val_mem SEGS (arm W m) GL 4 lst) /\ awr W m GL 4 /\ apres_kept B W mem W m).
{ intros m HM.
  assert (AVm : forall a, aview SEGS (w_H W) m a = aview SEGS (w_H W) mem3 a) by (intros a; apply aview_eq_of; apply HM).
  assert (HMf : mrestrict (w_H W) m = mrestrict (w_H W) mem3) by (apply functional_extensionality; exact HM).
  assert (KM : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W m a).
  { intros a Ha Hn. split.
    - rewrite AVm, (Hfr3 a ltac:(lia) Hn ltac:(unfold ESTACK; lia)). apply K0; lia.
    - intros Hw. unfold arm in *. rewrite HMf. apply (writable_kept (w_H W) (ms_mem ms) mem3 a (Hpres3 a)). exact (WK0 a Hw). }
  assert (RFWm : forall a, inG rf_cells a -> writable_at SEGS (arm W m) a).
  { intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
    apply (hidden_not_img SEGS W). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
  zsep_pick HSEPG 3%nat 8%nat DLG.
  pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as HGLb. cbn [fst snd] in HGLb.
  split; [exact KM|]. split; [exact RFWm|].
  split; [intros k Hk; rewrite HMf; exact (SV3 k Hk)|].
  split.
  { unfold alock_at. split; [|split; [|split]].
    - apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact LK0].
    - unfold arm. rewrite HMf. exact HLK3.
    - apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact LK8].
    - intros j Hj. apply RFWm. apply ILK. lia. }
  split.
  { apply (aout_at_kept B RG ly S W mem ly S W m c O mx no cap out HOUT).
    - pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_max RG, 8) ltac:(left; reflexivity)) as B4.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_nout RG, 8) ltac:(do 1 right; left; reflexivity)) as B5.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_capout RG, 8) ltac:(do 2 right; left; reflexivity)) as B6.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_out RG, 8) ltac:(do 3 right; left; reflexivity)) as B7.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_client_broken RG, 1) ltac:(do 4 right; left; reflexivity)) as B8.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_dead RG, 1) ltac:(do 5 right; left; reflexivity)) as B9.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_eintr RG, 1) ltac:(do 6 right; left; reflexivity)) as B10.
      pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
      cbn [fst snd] in B4, B5, B6, B7, B8, B9, B10, Bc.
      intros r Hr a Har. unfold aout_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Har.
      + zsep_pick HSEPO 0%nat 4%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 5%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 6%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 7%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 2%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 8%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 9%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 10%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 11%nat D.
        assert (Hb : 0x10000 <= a < 0x5fc000).
        { apply pa_img_range. apply (proj1 (HG a (HG2 a ltac:(unfold G_SL, inG; do 5 apply Exists_cons_tl; apply Exists_cons_hd;
            unfold in_zr; cbn [fst snd]; lia)))). }
        apply KM; lia.
      + destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
        pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAOB).
        destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [lia|].
        destruct (alx_blocks _ _ _ LAWS ly S _ W mem md out cap HAR HoIn) as (_ & Ho4096 & Hoceil & _).
        assert (Hrq : req_size cap = cap) by (unfold req_size; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity).
        rewrite Hrq in Hoceil.
        pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md out cap a HAR HoIn ltac:(lia)) as Hni.
        apply KM; [unfold ASAN_CEIL in Hoceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN a (ILK a ltac:(lia)))).
    - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
  split; [destruct HGLv as [lst Hl]; exists lst; apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact Hl]|].
  split; [intros j Hj; apply RFWm; eapply (in_rf_cell 6%nat _ 4); [reflexivity | lia]|].
  intros a _ _ _ Ha. destruct (Hpres3 a (P0 a Ha)) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  pose proof (HM (Z_to_bv 64 a)) as E1. unfold mrestrict in E1. rewrite Hh in E1. rewrite E1. exact Hb. }
zsep_pick HSEPG 3%nat 5%nat DLS. zsep_pick HSEPG 3%nat 6%nat DLC.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as HSRb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as HCSb.
cbn [fst snd] in HSRb, HCSb.
psrr_branch_tok RUN BR HS SHOKd Bspan.
- (* g_nsrc <= 0: no source (es = []), straight to the tail X *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
  apply Bool.negb_true_iff, Z.ltb_ge in Hc.
  assert (Hnil : es = []) by (destruct es as [|e es']; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_to_tok_x RUNTO HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0xf8).
  { apply awr_ok_x_of0. intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
    destruct Hin. }
  rfl_cur HS msX. rfl_meq MEQ1 MEQ2.
  destruct (CELLS (ms_mem msX) MEQ2) as (KX & RFWX & SVX & LKX & AOX & GLX & GLWX & APX).
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (9%bv : bv 5) N9.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
  pmkst HS.
  subst es.
  apply (rf_tail regs ly S Hp W mem md T [] c O mx no cap out rest ly S Hp W).
  eexists. exists out.
  split; [exact HJX3|].
  split; [exact (conj (ex_intro _ ch HPRE) (conj HPERM (conj HG1 (conj HG2 HG3))))|].
  split.
  { unfold rf_kept.
    split; [unfold spZ at 1; rewrite N2, (RG0 2%nat 2%bv ltac:(lia) eq_refl), unsigned_lit_small by (unfold spZ in *; lia); unfold spZ; lia|].
    split; [rewrite N3; exact (RG0 3%nat 3%bv ltac:(lia) eq_refl)|].
    split; [rewrite N4; exact (RG0 4%nat 4%bv ltac:(lia) eq_refl)|].
    split; [rewrite N21; exact (RG0 21%nat 21%bv ltac:(lia) eq_refl)|].
    split; [rewrite N22; exact (RG0 22%nat 22%bv ltac:(lia) eq_refl)|].
    split; [rewrite N23; exact (RG0 23%nat 23%bv ltac:(lia) eq_refl)|].
    split; [rewrite N24; exact (RG0 24%nat 24%bv ltac:(lia) eq_refl)|].
    split; [rewrite N25; exact (RG0 25%nat 25%bv ltac:(lia) eq_refl)|].
    split; [rewrite N26; exact (RG0 26%nat 26%bv ltac:(lia) eq_refl)|].
    split; [rewrite N27; exact (RG0 27%nat 27%bv ltac:(lia) eq_refl)|].
    rewrite N9. exact UH5. }
  split; [exact SVX|].
  split.
  { destruct HREL as [(HT0 & _ & (VS0 & WS0 & VN0 & WN0 & VC0 & WC0)) | (VST & WST & VNT & WNT & VCT & WCT & _ & HTin & _)].
    - split; [intros j Hj; apply RFWX; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
      left. split; [exact HT0|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VS0]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VC0]|].
      intros j Hj; apply RFWX; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia].
    - split; [intros j Hj; apply RFWX; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
      right. destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR HTin) as (_ & HT4096 & _).
      split; [lia|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VST]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VCT]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia]|].
      exact HTin. }
  split; [exact LKX|].
  split; [exact AOX|].
  split; [exact HPERM|].
  split; [exact GLX|]. split; [exact GLWX|].
  split; [exact APX|].
  split; [exact (mle_start MT S MLAW)|].
  (* the room round: no source, so nothing was charged: the entry's room is rf_post_x's kr *)
  exact HRMe.
- (* g_nsrc > 0: the loop L from i = 0 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
  apply Bool.negb_false_iff, Z.ltb_lt in Hc.
  destruct HREL as [(_ & Hes0 & _) | HRA]; [rewrite Hes0 in Hc; cbn [length] in Hc; lia|].
  pose proof HRA as (VST & WST & VNT & WNT & VCT & WCT & Hle & HTin & (tail & HTA) & HAOK & HNDF).
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR HTin) as (HT16 & HT4096 & HTceil & _ & _ & _).
  change (req_size ATABLE) with 896 in HTceil.
  paj_run_to_tok_x RUNTO HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x7c).
  { apply awr_ok_x_of0. intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
    destruct Hin. }
  rfl_cur HS msL. rfl_meq MEQ1 MEQ2.
  destruct (CELLS (ms_mem msL) MEQ2) as (KL & RFWL & SVL & LKL & AOL & GLL & GLWL & APL).
  pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARL.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
  pmkst HS.
  (* the table's bytes as the loop head finds them *)
  assert (KT : forall x, T <= x < T + 896 -> abyte_kept W mem W (ms_mem msL) x).
  { intros x Hx. pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md T ATABLE x HAR HTin ltac:(change (req_size ATABLE) with 896; lia)) as Hni.
    apply KL; [unfold ASAN_CEIL in HTceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN x (ILK x ltac:(lia)))). }
  assert (KBL : forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n ->
    aview SEGS (w_H W) (ms_mem msL) x = aview SEGS (w_H W) mem x).
  { intros b n x Hin Hx. destruct (alx_blocks _ _ _ LAWS ly S _ W mem md b n HAR Hin) as (_ & Hb4096 & Hbceil & _).
    pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md b n x HAR Hin Hx) as Hni.
    apply KL; [unfold ASAN_CEIL in Hbceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN x (ILK x ltac:(lia)))). }
  assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es).
  { eapply Forall_impl; [|exact HAOK]. intros e (_ & _ & P1 & P2 & _). split; [exact P1 | exact P2]. }
  pose proof HTA as (_ & _ & HTG).
  apply (LOOP (length es) regs ly S Hp W mem md T es c O mx no cap out rest 0%nat ly S Hp W); [lia | exact HCNTe |].
  eexists. exists out, 0.
  split; [exact HJX3|].
  split; [exact (conj (ex_intro _ ch HPRE) (conj HPERM (conj HG1 (conj HG2 HG3))))|].
  split.
  { unfold rf_kept.
    split; [unfold spZ at 1; rewrite N2, (RG0 2%nat 2%bv ltac:(lia) eq_refl), unsigned_lit_small by (unfold spZ in *; lia); unfold spZ; lia|].
    split; [rewrite N3; exact (RG0 3%nat 3%bv ltac:(lia) eq_refl)|].
    split; [rewrite N4; exact (RG0 4%nat 4%bv ltac:(lia) eq_refl)|].
    split; [rewrite N21; exact (RG0 21%nat 21%bv ltac:(lia) eq_refl)|].
    split; [rewrite N22; exact (RG0 22%nat 22%bv ltac:(lia) eq_refl)|].
    split; [rewrite N23; exact (RG0 23%nat 23%bv ltac:(lia) eq_refl)|].
    split; [rewrite N24; exact (RG0 24%nat 24%bv ltac:(lia) eq_refl)|].
    split; [rewrite N25; exact (RG0 25%nat 25%bv ltac:(lia) eq_refl)|].
    split; [rewrite N26; exact (RG0 26%nat 26%bv ltac:(lia) eq_refl)|].
    split; [rewrite N27; exact (RG0 27%nat 27%bv ltac:(lia) eq_refl)|].
    rewrite N9. exact UH5. }
  split; [rewrite N8, OLDd, OLDa, E32 by lia; reflexivity|].
  split; [rewrite N20; exact UH6|].
  split; [rewrite N19; reflexivity|].
  split; [rewrite N18; reflexivity|].
  split; [exact SVL|].
  split; [lia|]. split; [exact Hle|]. split; [lia|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VNT]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VST]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VCT]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia]|].
  split; [exact HTin|].
  split.
  { intros j Hj.
    assert (HOK : aentry_ok B ly S W mem (nth j es rf_e0)) by (exact (proj1 (Forall_forall _ _) HAOK _ (@nth_In _ j es rf_e0 ltac:(lia)))).
    destruct HOK as (_ & _ & P1 & P2 & _ & _ & _ & _ & _ & BUF & NH & HP & ND1 & ND2 & KS).
    assert (HHE : aheld_ok B ly S W mem (nth j es rf_e0)) by (exact (conj P1 (conj P2 (conj NH (conj HP (conj ND1 (conj ND2 KS))))))).
    pose proof (rf_garr8_entry _ es T tail j HPADS HTG ltac:(lia)) as GJ.
    split; [|split; [|split]].
    - apply (akept_garr8 W mem); [|exact GJ]. intros x Hx. apply KT.
      unfold bzs in Hx. rewrite length_map in Hx. pose proof (rfl_len_entry _ P1 P2) as L. unfold bzs in L. rewrite length_map in L.
      rewrite L in Hx. unfold AENT in Hx. lia.
    - intros q Hq. apply (apresent_writable SEGS).
      destruct (alx_blocks _ _ _ LAWS ly S _ W (ms_mem msL) _ T ATABLE HARL HTin) as (_ & _ & _ & _ & HTp & _).
      change (req_size ATABLE) with 896 in HTp. exact (proj1 (HTp (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
    - apply (rfl_aheld_ok_kept ly S W mem ly S W (ms_mem msL) _ HHE).
      + intros b Hb. unfold gse_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
        * destruct (Z.eqb_spec (re_hp (nth j es rf_e0)) 0) as [Ez | Ez]; [destruct Hb|]. destruct Hb as [<- | []].
          destruct HP as [(Hz & _) | (_ & Hin & _)]; [contradiction | exact Hin].
        * apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in KS. exact (proj1 (KS k Hk)).
      + intros b n x Hb Hx.
        assert (HbI : In (b, n) (ablocks B ly S)).
        { unfold gse_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
          - destruct (Z.eqb_spec (re_hp (nth j es rf_e0)) 0) as [Ez | Ez]; [destruct Hb|]. destruct Hb as [Hb | []].
            injection Hb as <- <-. destruct HP as [(Hz & _) | (_ & Hin & _)]; [contradiction | exact Hin].
          - apply in_map_iff in Hb as (k & Hk1 & Hk). injection Hk1 as <- <-. rewrite Forall_forall in KS. exact (proj1 (KS k Hk)). }
        apply (KBL b n x HbI). unfold req_size. destruct (Z.eqb_spec n 0); lia.
    - destruct BUF as [(Hc0 & Hb0 & _) | (Hc0 & Hin0 & _)]; [left; split; assumption | right; split; assumption]. }
  split; [exact LKL|].
  split; [exact AOL|].
  split; [exact HPERM|].
  split; [exact GLL|]. split; [exact GLWL|].
  assert (ROML : rom_view SEGS W (ms_mem msL)).
  { intros a Ha. pose proof Ha as (sg & Hsg & Hwr & Hr).
    pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hb.
    rewrite (proj1 (KL a ltac:(lia) ltac:(intros Hl; apply (HROMG a ltac:(left; unfold RF_G, inG; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia)); exact Ha))).
    exact (HROM a Ha). }
  split; [exact (rfl_end5_kept W W mem (ms_mem msL) HROM ROML HEND5)|].
  split; [exact ROML|].
  split; [exact APL|].
  split; [exact HROOM|].
  split; [exact (mle_start MT S MLAW)|].
  split; [apply Z.eq_le_incl; reflexivity|].
  split; [exact HMOK|].
  (* the room round: round 0 is owed the whole charge, and the prologue and the lock kept the allocator state *)
  cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]. exact HRMe.
Qed.
(* ---- route R (a Theorem Labs lane's rl-rfb lift): the walk at a world relation R.  The texts are Section c's, lifted:
   ajournal_gx_x -> ajournal_gx_xR R, SRr SEGS -> SRrG SEGS R, rf_spec_x / rf_post_x -> W_contract_xR.v rf_spec_xR /
   rf_post_xR, RFX / RFI / the two cut statements -> their _xR twins below, the runs and the branch -> their SRrG forms
   (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, Reusable/YC80xR.v SRrG_run_pi_tok_AJxG, W_kit.v paj_branch_xR), the
   journal lemmas -> their _xR twins, the lock and the unlock -> W_sites_x.v aj_gx_entry_at_xR (their realizes rules
   stay strict), gestures_end -> GSE_R : gse_spec_xR, and the free -> the R free rules (afree_cf_rule_c_xR /
   afree_null_cf_rule_c_xR .. RO CTX R) with RO_ARx for their call-boundary premise.  The strict texts above
   keep their proofs; each R lemma's Proof using takes every Section variable but the strict AFREE / AFREE0 / GSE. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
Let RUN0G := YC80xR.SRrG_run_pi_tok_AJxG (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr) (R := R).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 ([] : list (Z * Z)).
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 ([] : list (Z * Z)).
Let BRR := paj_branch_xR (PI := PI) (R := R).
Definition RFX_xR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (lyX : alayout) (SX : astate) (HpX : list Z) (WX : world SEGS) (regsX : bvmap 5 word)
(memX : word -> option byte) (mdX : Model) (kr : nat) : Prop :=
exists kX outX,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []
  lyX SX HpX WX memX mdX kX /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsX (spZ regs) /\
rf_saved WX memX (spZ regs) regs /\
rf_done lyX SX WX memX T /\
alock_at RG WX memX true /\
aout_at B RG lyX SX WX memX
  (gse_c (rf_run c O mx no cap es)) (gse_O (rf_run c O mx no cap es)) mx
  (gse_no (rf_run c O mx no cap es)) (gse_cap (rf_run c O mx no cap es)) outX /\
Permutation (ablocks B lyX SX) (rf_tblk T ++ aout_blks (gse_cap (rf_run c O mx no cap es)) outX ++ rest) /\
(exists lst, val_mem SEGS (arm WX memX) GL 4 lst) /\ awr WX memX GL 4 /\
apres_kept B W mem WX memX /\
mo_le MT S SX (rf_cost MT c O mx no cap es) /\
(* the room round: the room left after every round, which rf_post_x passes on *)
rp_RM RP SX kr.
Definition rf_tail_stmt_xR : Prop :=
forall regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr,
RFX_xR regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr ->
YA0nH.SRrG SEGS R WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS)) mdX)
(rf_post_xR B PST ARx R MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
Lemma rf_tail_xR : rf_tail_stmt_xR.
Proof using All - (AFREE AFREE0 GSE).
unfold rf_tail_stmt_xR.
intros regs ly S Hp W mem md T es c O mx no cap out rest lyX SX HpX WX regsX memX mdX kr HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16672) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HX as (kX & outX & HJX & ((ch & HPRE0) & HPERM0 & HG1 & HG2 & HG3) & HKP & HSV & HDONE & HLK
  & HAO & HPERM & HGLv & HGLw & HPRES & HMO & HRMX).
pose proof HPRE0 as (_ & Hra & _ & Hgp & Htp & _). clear HPERM0.
destruct HKP as (KSP & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K9).
pose proof HJX as (HSTK & HXO & (memS & HJi & HAG) & HOUT).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARx & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (rfx_entry WX regsX memX regs
  ltac:(rewrite KSP; rewrite WS in Hslo; lia) ltac:(rewrite KSP; lia) K9
  ltac:(replace (spZ regsX + 48) with (spZ regs) by lia; exact HSV)
  (proj1 HDONE) ltac:(pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _); exact Hw) HGLw) as HS.
remember (Eimg (Ereg regsX (rfx_extra regs))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 6)%nat -> ew E (32 + i) = getr regs (nth i RF_SAVED 0%bv))
by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact (nth_rfx_extra regs i Hi)).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
assert (U5 : bv_unsigned (ew E 285%nat) = VAL (A_HI 5)) by exact (UH 5%nat ltac:(lia)).
assert (U7 : bv_unsigned (ew E 287%nat) = VAL (A_HI 7)) by exact (UH 7%nat ltac:(lia)).
assert (U8 : bv_unsigned (ew E 288%nat) = VAL (A_HI 8)) by exact (UH 8%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
clear HE.
assert (SHOK : sh_ok SEGS BxX [] E (mrestrict (w_H WX) memX)) by constructor.
(* the globals relay_finish writes are bytes of G *)
assert (INL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (INS : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (INC : forall a, rg_client RG <= a < rg_client RG + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ING : forall a, GL <= a < GL + 4 -> inG G a)
by (intros a Ha; apply HG1; unfold RF_G, inG; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
paj_run_tok_xR RUNG HS HJX SHOK Bspan.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U5, ?U7, ?U8 in Hr;
    first [ lia | right; left; apply INS; lia | right; left; apply INC; lia | right; left; apply ING; lia ] | ]).
  destruct Hin. }
(* ---- what the stores left: g_nsrc = 0, g_client = g_listen = 2^32 - 1, every other byte as at the cut ---- *)
lazymatch goal with Hx : mem_grows _ _ |- _ => rename Hx into MG1 end.
rename HFr into HFr1. clear HF.
assert (NWA : forall a, ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> ~ in_wrange E (ss_mem ss_rfx) a).
{ intros a N1 N2 N3 (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U5, ?U7, ?U8 in Hr; lia | ]).
  destruct Hin. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E _ (w_H WX) memX (ms_mem ms) HFr1 a Ha (NWA a N1 N2 N3))).
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HRn.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HRc.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HRg.
cbn [ms_mem restrict] in HRn, HRc, HRg.
pose proof (field_of_region E _ 285%nat _ _ _ _ _ _ (-1672) 4%N (SLit 0) 0 HRn U5 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as VNS1.
rewrite HH5 in VNS1. change (N.to_nat 4) with 4%nat in VNS1.
pose proof HRc as (_ & _ & _ & HCc). cbn [YP09.r_chunks YP09.r_base base_val] in HCc. apply Forall_inv in HCc.
pose proof (rfx_m1_val E _ _ _ HCc) as VCL1. rewrite U7, HH7 in VCL1.
pose proof HRg as (_ & _ & _ & HCg). cbn [YP09.r_chunks YP09.r_base base_val] in HCg. apply Forall_inv in HCg.
pose proof (rfx_m1_val E _ _ _ HCg) as VGL1. rewrite U8, HH8 in VGL1.
clear HRn HRc HRg HCc HCg.
(* ---- the tail call to pthread_mutex_unlock (a0 = &g_lock = VAL (A_OBJ 3)), at the caller's sp ---- *)
rewrite WS in Hslo.
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as Bl.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as Bn.
pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as Bg.
cbn [fst snd] in Bl, Bn, Bc, Bg.
assert (KLK1 : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a).
{ intros a Ha. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  apply KA; lia. }
assert (LK0m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG) 4 0)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 0); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK0]).
assert (LK4m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + 4) 4 16)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 16); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK4]).
assert (LK8m : val_mem SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + 8) 4 0)
by (apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX (ms_mem ms) _ 4 0); [intros k Hk; apply KLK1; cbn in Hk; lia | exact LK8]).
assert (LKW1 : forall i, 0 <= i < 12 -> writable_at SEGS (mrestrict (w_H WX) (ms_mem ms)) (rg_lock RG + i))
by (intros i Hi; exact (writable_at_grows SEGS _ _ _ MG1 (LKW i Hi))).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (HSPc : spZ (ms_regs ms) = spZ regs + 0).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). unfold spZ in *. lia. }
assert (QA0 : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 244%nat with (A_OBJ 3).
  rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), HV3. reflexivity. }
assert (QRA : getr (ms_regs ms) 1 = getr regs 1) by (rewrite Q1; exact (EX 5%nat ltac:(lia))).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR1.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B lyX SX a).
{ intros a Ha Ho. destruct (HG a (INL a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho). }
eapply SRrG_mono.
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H WX) mem') (rg_lock RG + 4) 4 0)
    WX (ms_regs ms) (ms_mem ms) RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ 0 (getr regs 1) HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), K3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), K4. exact Htp.
  - exact QRA.
  - exact Hra.
  - intros a. lia.
  - intros a Ha _. exact (rfx_av_ne WX (ms_mem ms) (rg_lock RG + 4) 4%nat 16 a LK4m ltac:(cbn; lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply INL. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0.
    + lia.
    + exact RGAL.
    + lia.
    + exact LK0m.
    + exact LK4m.
    + exact LK8m.
    + intros a Ha. split.
      * destruct (Z_lt_le_dec a (rg_lock RG + 4)) as [h1 | h1]; [exact (rfx_av_ne WX _ _ 4%nat 0 a LK0m ltac:(cbn; lia))|].
        destruct (Z_lt_le_dec a (rg_lock RG + 8)) as [h2 | h2]; [exact (rfx_av_ne WX _ _ 4%nat 16 a LK4m ltac:(cbn; lia))|].
        exact (rfx_av_ne WX _ _ 4%nat 0 a LK8m ltac:(cbn; lia)).
      * rewrite HSPc. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. exact (LKW1 (a - rg_lock RG) ltac:(lia)).
      * apply HNOWN. lia.
      * rewrite HSPc. unfold spZ in *. lia.
    + intros a Ha HK. exact (proj2 (proj2 (HG a (INL a ltac:(lia)))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK43) & Hfr3 & Hpres3).
(* ---- from the cut to the return: presence, writability and the bytes ---- *)
pose proof pa_img_range as Himg.
assert (PR2 : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) mem3 a)
by (intros a Ha; apply Hpres3; exact (apresent_grows (w_H WX) memX (ms_mem ms) a MG1 Ha)).
assert (WKf : forall x, writable_at SEGS (arm WX memX) x -> writable_at SEGS (arm WX mem3) x)
by (intros x Hx; exact (writable_kept (w_H WX) memX mem3 x (PR2 x) Hx)).
(* an image-band byte off the lock word keeps its view from after the stores to the return *)
assert (KIMG : forall x, 0x10000 <= x < 0x5fc000 -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) (ms_mem ms) x).
{ intros x Hx Nl. apply Hfr3; [lia | exact Nl | unfold spZ in *; lia]. }
(* ... and from the cut, when it is none of the three stored cells *)
assert (KALL : forall x, 0x10000 <= x < 0x5fc000 -> ~ (rg_nsrc RG <= x < rg_nsrc RG + 4) ->
  ~ (rg_client RG <= x < rg_client RG + 4) -> ~ (GL <= x < GL + 4) -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x)
by (intros x Hx N1 N2 N3 N4; rewrite (KIMG x Hx N4); apply KA; [lia | exact N1 | exact N2 | exact N3]).
(* a byte of a live block keeps its view from the cut to the return *)
assert (KBLK : forall p n x, In (p, n) (ablocks B lyX SX) -> p <= x < p + req_size n ->
  aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros p n x Hin Hx.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARx Hin) as (_ & Hp4096 & Hpceil & _).
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n x HARx Hin Hx) as Hxn.
  assert (Nc : forall i lo m, nth_error rf_cells i = Some (lo, m) -> ~ (lo <= x < lo + m)).
  { intros i lo m Hn Hr. exact (Hxn (proj1 (HPLAIN x (in_rf_cell i lo m x Hn Hr)))). }
  rewrite (Hfr3 x ltac:(unfold ASAN_CEIL in *; lia) ltac:(intros Hl; apply (Nc 1%nat (rg_lock RG) 12); [reflexivity | lia])
    ltac:(unfold ASAN_CEIL, spZ in *; lia)).
  apply KA; [unfold ASAN_CEIL in *; lia | apply (Nc 2%nat); reflexivity | apply (Nc 5%nat); reflexivity | apply (Nc 6%nat); reflexivity]. }
(* the values the tail stored, at the return *)
assert (VNSf : val_mem SEGS (arm WX mem3) (rg_nsrc RG) 4 0).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 0); [|exact VNS1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 1%nat S01. apply KIMG; lia. }
assert (VCLf : val_mem SEGS (arm WX mem3) (rg_client RG) 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VCL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 2%nat S02. apply KIMG; lia. }
assert (VGLf : val_mem SEGS (arm WX mem3) GL 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VGL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 3%nat S03. apply KIMG; lia. }
(* the lock: released (word 4 by the unlock), type and waiter words kept *)
assert (LKF : alock_at RG WX mem3 false).
{ unfold alock_at, arm. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK0]. intros k Hk. cbn in Hk. apply KALL; lia.
  - exact HLK43.
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK8]. intros k Hk. cbn in Hk. apply KALL; lia.
  - intros i Hi. apply WKf. exact (LKW i Hi). }
(* the controller's cells (all but g_client) and the g_out block, from the cut *)
assert (AK : akept WX memX WX mem3 (rfx_aout_fp (gse_cap (rf_run c O mx no cap es)) outX)).
{ intros r Hr a Ha. split; [|apply WKf].
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_max RG, 8) ltac:(left; reflexivity)) as B4.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_nout RG, 8) ltac:(do 1 right; left; reflexivity)) as B5.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_capout RG, 8) ltac:(do 2 right; left; reflexivity)) as B6.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_out RG, 8) ltac:(do 3 right; left; reflexivity)) as B7.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_client_broken RG, 1) ltac:(do 4 right; left; reflexivity)) as B8.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_dead RG, 1) ltac:(do 5 right; left; reflexivity)) as B9.
  pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_eintr RG, 1) ltac:(do 6 right; left; reflexivity)) as B10.
  cbn [fst snd] in B4, B5, B6, B7, B8, B9, B10.
  unfold rfx_aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]; cbn [fst snd] in Ha.
  - rfx_cell KALL HSEPO 4%nat.
  - rfx_cell KALL HSEPO 5%nat.
  - rfx_cell KALL HSEPO 6%nat.
  - rfx_cell KALL HSEPO 7%nat.
  - rfx_cell KALL HSEPO 8%nat.
  - rfx_cell KALL HSEPO 9%nat.
  - rfx_cell KALL HSEPO 10%nat.
  - assert (Hb : 0x10000 <= a < 0x5fc000).
    { apply Himg. apply (proj1 (HG a (HG2 a ltac:(unfold G_SL, inG; do 5 apply Exists_cons_tl; apply Exists_cons_hd;
        unfold in_zr; cbn [fst snd]; lia)))). }
    rfx_cell KALL HSEPO 11%nat.
  - pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAOB).
    destruct (Z.eq_dec (gse_cap (rf_run c O mx no cap es)) 0) as [Hc0 | Hc0].
    { rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hr. destruct Hr. }
    rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [lia|].
    apply (KBLK _ _ a HoIn). unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). exact Ha. }
(* g_src and g_capsrc as the cut found them *)
assert (KSRC : forall x, rg_src RG <= x < rg_src RG + 8 -> aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 3%nat 5%nat T1. zsep_pick HSEPG 4%nat 5%nat T2. zsep_pick HSEPG 5%nat 7%nat T3. zsep_pick HSEPG 5%nat 8%nat T4.
  apply KALL; lia. }
assert (KCAP : forall x, rg_capsrc RG <= x < rg_capsrc RG + 4 -> aview SEGS (w_H WX) mem3 x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 3%nat 6%nat T1. zsep_pick HSEPG 4%nat 6%nat T2. zsep_pick HSEPG 6%nat 7%nat T3. zsep_pick HSEPG 6%nat 8%nat T4.
  apply KALL; lia. }
pose proof HJX3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HARf & _ & _ & _ & _ & Hfrf & _).
(* ---- the post ---- *)
unfold rf_post_xR.
exists lyX, SX, HpX, regs3, mem3, md3, kX, outX.
split; [reflexivity|].
split; [exact HJX3|].
split.
{ intros r Hr. rewrite (HP3 r Hr). unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2, Usp, KSP.
    replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (EE 3%nat 3%bv eq_refl). exact K3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (EE 4%nat 4%bv eq_refl). exact K4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (EX 0%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21, (EE 21%nat 21%bv eq_refl). exact K21.
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22, (EE 22%nat 22%bv eq_refl). exact K22.
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23, (EE 23%nat 23%bv eq_refl). exact K23.
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (EE 24%nat 24%bv eq_refl). exact K24.
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (EE 25%nat 25%bv eq_refl). exact K25.
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (EE 26%nat 26%bv eq_refl). exact K26.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (EE 27%nat 27%bv eq_refl). exact K27. }
split. { intros a Hi Ho He Hpr. exact (PR2 a (HPRES a Hi Ho He Hpr)). }
split. { cbn [app] in Hfrf. exact Hfrf. }
split. { exact HMO. }
(* the room round: the unlock keeps the allocator state, so RFX's room is rf_post_x's *)
split. { exact HRMX. }
split. { exact HPERM. }
split.
{ apply (rfx_aout_m1 lyX SX WX memX _ _ WX _ _ _ mx _ _ outX HAO AK WKf VCLf).
  intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  apply in_or_app. right. apply in_or_app. left. exact Hb. }
split. { exact LKF. }
split.
{ destruct HDONE as (HNSW & [(HT0 & VS0 & WS0 & VC0 & WC0) | (HT & VST & WST & VCT & WCT & HTin)]).
  - left. split; [exact HT0|]. split; [reflexivity|]. unfold arelay_empty.
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 8 0); [intros k Hk; cbn in Hk; apply KSRC; lia | exact VS0]|].
    split; [intros i Hi; apply WKf; exact (WS0 i Hi)|].
    split; [exact VNSf|].
    split; [intros i Hi; apply WKf; exact (HNSW i Hi)|].
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [intros k Hk; cbn in Hk; apply KCAP; lia | exact VC0]|].
    intros i Hi; apply WKf; exact (WC0 i Hi).
  - right. unfold arelay_at.
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 8 T); [intros k Hk; cbn in Hk; apply KSRC; lia | exact VST]|].
    split; [intros i Hi; apply WKf; exact (WST i Hi)|].
    split; [exact VNSf|].
    split; [intros i Hi; apply WKf; exact (HNSW i Hi)|].
    split; [unfold arm; apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 16); [intros k Hk; cbn in Hk; apply KCAP; lia | exact VCT]|].
    split; [intros i Hi; apply WKf; exact (WCT i Hi)|].
    split; [cbn; lia|].
    split; [exact HTin|].
    split; [|split; [constructor | split; constructor]].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HARf HTin) as (_ & _ & _ & _ & HTp & _).
    destruct (garr8_of_present SEGS (arm WX mem3) T 896) as (l & Hl & Hg).
    { intros a Ha. destruct (HTp a ltac:(unfold req_size, ATABLE; cbn in Ha |- *; lia)) as ((Hh & b & Hb) & _).
      exists b. unfold arm, mrestrict. rewrite Hh. exact Hb. }
    exists (map (Z_to_bv 8) l). unfold atable_at. cbn [length map concat app].
    rewrite (rfx_bzs_map l (garr8_bytes_ok SEGS _ _ _ Hg)), length_map, Hl.
    unfold ATABLE, AENT. split; [cbn; lia|]. split; [cbn; lia|]. exact Hg. }
split; [exact VGLf|].
intros i Hi. apply WKf. exact (HGLw i Hi).
Qed.
Definition RFI_xR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (i : nat) (lyL : alayout) (SL : astate) (HpL : list Z) (WL : world SEGS)
(regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (kr : nat) : Prop :=
exists kL outL spent,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []
  lyL SL HpL WL memL mdL kL /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsL (spZ regs) /\
getr regsL 8 = w64 SB /\ getr regsL 20 = w64 (VAL (A_HI 6)) /\
getr regsL 19 = w64 (Z.of_nat i) /\ getr regsL 18 = w64 (56 * Z.of_nat i) /\
rf_saved WL memL (spZ regs) regs /\
(i < length es)%nat /\ (length es <= 16)%nat /\ T <> 0 /\
val_mem SEGS (arm WL memL) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr WL memL (rg_nsrc RG) 4 /\
val_mem SEGS (arm WL memL) (rg_src RG) 8 T /\ awr WL memL (rg_src RG) 8 /\
val_mem SEGS (arm WL memL) (rg_capsrc RG) 4 16 /\ awr WL memL (rg_capsrc RG) 4 /\
In (T, ATABLE) (ablocks B lyL SL) /\
(forall j, (i <= j < length es)%nat ->
   garr8 SEGS (arm WL memL) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
   awr WL memL (T + AENT * Z.of_nat j) AENT /\
   aheld_ok B lyL SL WL memL (nth j es rf_e0) /\
   ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
    (0 < re_cap (nth j es rf_e0) /\
     In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B lyL SL)))) /\
alock_at RG WL memL true /\
aout_at B RG lyL SL WL memL
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es))) outL /\
Permutation (ablocks B lyL SL)
  (rf_tblk T ++ rf_eblks (skipn i es) ++
   aout_blks (gse_cap (rf_run c O mx no cap (firstn i es))) outL ++ rest) /\
(exists lst, val_mem SEGS (arm WL memL) GL 4 lst) /\ awr WL memL GL 4 /\
garr8 SEGS (arm WL memL) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS WL memL /\
apres_kept B W mem WL memL /\
rf_room MMAX (blocks_bytes SL)
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es) /\
mo_le MT S SL spent /\
spent + rf_cost MT
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es) <= rf_cost MT c O mx no cap es /\
mo_ok MT S (rf_cost MT c O mx no cap es) /\
(* the room round: the room the remaining rounds charge (each a free and a gestures_end), then rf_post_x's kr *)
rp_RM RP SL (Z.to_nat (rf_cost MT_rk
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es)) + kr).
Definition rf_loop_stmt_xR : Prop :=
In [BASE + AF_fr_relay_finish + 200] CTX ->
forall (k : nat) regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr,
(length es - i <= k)%nat ->
cnt_ok_pk RP rf_pk (ablocks B ly S) ->
RFI_xR regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr ->
YA0nH.SRrG SEGS R WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)) mdL)
(rf_post_xR B PST ARx R MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
Lemma rf_loop_xR : rf_tail_stmt_xR -> rf_loop_stmt_xR.
Proof using All - (AFREE AFREE0 GSE).
intros TAIL HCTX. unfold rf_loop_stmt_xR.
induction k as [|k IH]; intros regs ly S Hp W mem md T es c O mx no cap out rest i lyL SL HpL WL regsL memL mdL kr Hk HCNT0 HRFI.
{ exfalso. destruct HRFI as (kL & outL & spent & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRFI as (kL & outL & spent & HJ & HEF & HKP & H8 & H20 & H19 & H18 & HSV & Hi & Hn16 & HT0 &
  HNS & HNSw & HSRC & HSRCw & HCAP & HCAPw & HTB & HENT & HLK & HOUT & HPERM & HGLv & HGLw & HEND5 & HROM & HPK &
  HROOM & HMLE & HSP & HMOK & HRML).
set (sp0 := spZ regs) in *.
set (e := nth i es rf_e0).
destruct (HENT i ltac:(lia)) as (HG8 & HAW & HHELD & HBUF). fold e in HG8, HAW, HHELD, HBUF.
change (rfl_bufok lyL SL e) in HBUF.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARL.
destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL T ATABLE HARL HTB) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTapp, HTpres.
assert (Rb : 0 <= re_buf e < 2 ^ 64).
{ destruct HBUF as [(_ & ->) | (Hc & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL _ _ HARL Hin) as (_ & Hb4096 & Hbceil & _). pose proof (req_size_pos (re_cap e) ltac:(lia)). lia. }
set (p := T + 56 * Z.of_nat i).
set (n := Z.of_nat (length es)).
assert (HVB : val_mem SEGS (mrestrict (w_H WL) memL) (p + 16) 8 (re_buf e)).
{ pose proof HHELD as (Hp1 & _). pose proof (rfl_buf_field _ _ e Hp1 Rb HG8) as H. unfold p, AENT in *. exact H. }
remember (Eimg (Ereg regsL (rfl_extra T p (re_buf e) n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regsL rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 T) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
pose proof HKP as (Ksp & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K9).
assert (E8 : ew E 8 = Z_to_bv 64 SB) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 (56 * Z.of_nat i)) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (EO : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j)) by (intros j Hj; subst E; apply Eimg_img; exact Hj).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsrc : forall x, rg_src RG <= x < rg_src RG + 8 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 3%nat _ 8 x eq_refl Hx)).
assert (Hnsrc : forall x, rg_nsrc RG <= x < rg_nsrc RG + 4 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 2%nat _ 4 x eq_refl Hx)).
assert (HTni : forall x, T <= x < T + 896 -> ~ in_img SEGS x)
by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL memL mdL T ATABLE x HARL HTB ltac:(change (req_size ATABLE) with 896; lia))).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb. cbn [fst snd] in HNSb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as HSRb. cbn [fst snd] in HSRb.
assert (H56 : (56 * Z.of_nat i) mod 8 = 0) by (replace (56 * Z.of_nat i) with (Z.of_nat i * 7 * 8) by ring; apply Z_mod_mult).
assert (Hp8 : p mod 8 = 0).
{ unfold p. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 56 * Z.of_nat i) with ((2 * (T / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
assert (HS : st_ok_pi SEGS VAL E ss_rfl (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rfl. apply pa_entry_st_ok_full.
  - unfold rfl_sr. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    + cbn [sv_denot]. rewrite (EO (A_HI 5) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact K9.
    + cbn [sv_denot]. rewrite (EO (A_HI 6) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact H20.
  - vm_compute. reflexivity.
  - unfold rfl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 5) _ (EO (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 5))), HV5.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) T);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HSRC.
    + rewrite (VB (A_OBJ 4) _ (EO (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 4))), HV4.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold n; zside | zside |].
      rewrite Z.add_0_r. exact HNS.
    + rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
      split; [unfold p; lia|]. split; [unfold p; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 16 8 (SOff 34 0) (re_buf e));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact HVB.
  - apply pairwise_disjoint_of_extents. unfold rfl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 5) _ (EO (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 5))), HV5.
    rewrite (VB (A_OBJ 4) _ (EO (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 4))), HV4.
    rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    zsep_pick HSEPG 4%nat 5%nat D45.
    assert (DS : rg_src RG + 8 <= p + 16 \/ p + 16 + 8 <= rg_src RG).
    { apply rfl_apart; [lia | lia |]. intros x Hx1 Hx2. apply (HTni x ltac:(unfold p in Hx2; lia)).
      exact (proj1 (HPLAIN x (Hsrc x ltac:(lia)))). }
    assert (DN : rg_nsrc RG + 4 <= p + 16 \/ p + 16 + 8 <= rg_nsrc RG).
    { apply rfl_apart; [lia | lia |]. intros x Hx1 Hx2. apply (HTni x ltac:(unfold p in Hx2; lia)).
      exact (proj1 (HPLAIN x (Hnsrc x ltac:(lia)))). }
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [rfl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E8, E18, E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, p, n; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold n. revert HT16 HT4096 HTceil Hp8 H56 Rb Hn16 Hi C1. clear. unfold p, SB. intros.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    + cbn [rfl_facts f_alias alias_ok]. split; [|split; [|exact I]].
      * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 18 _ E18), (U_atom E 32 T E32), (U_atom E 33 p E33) by (unfold p; lia).
        unfold p. replace (56 * Z.of_nat i + T) with (T + 56 * Z.of_nat i) by lia. apply zcanon_id. unfold M64. lia.
      * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 18 _ E18), (U_atom E 32 T E32), (U_atom E 33 p E33) by (unfold p; lia).
        unfold p. apply zcanon_id. unfold M64. lia. }
clear HE.
assert (HBx : U E rfl_Bx = SHADOW_OFF) by (unfold rfl_Bx; rewrite (U_atom E 8 SB E8) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS rfl_Bx rfl_SH E (mrestrict (w_H WL) memL)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H WL) memL E rfl_Bx 33 (p + 16) 8 p 16 24
    (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyL SL HpL WL memL mdL T ATABLE (p + 16) 8 HARL HTB
      ltac:(unfold p; change (req_size ATABLE) with 896; lia) ltac:(unfold p; change (req_size ATABLE) with 896; lia)) HBx);
  [rewrite (U_atom E 33 p E33) by (unfold p; lia); reflexivity | lia | lia |].
  intros x Hx. unfold p, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold A_rf_loop.
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ apply awr_ok_x_of0. awr_any. }
(* 0x823c8 bltu a1,a0: B's UBSan pointer-overflow trap on p = T + 56 i, never taken (W_traps.v trap_ptr_wrap_atom) *)
psrr_branch_tok RUNG BRR HS SHOK Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 33 32 T (56 * Z.of_nat i) E33 E32 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
  discriminate. }
assert (MEQ0 : forall x, mrestrict (w_H WL) memL x = mrestrict (w_H WL) memL x) by reflexivity.
rfl_meq MEQ0 MEQ1.
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { rf_awr. }
rfl_meq MEQ1 MEQ2.
rfl_cur HS msF. clear Hc.
(* ---- free (s->buf).  The runs wrote nothing: the memory at the call is memL as the walk sees it. ---- *)
assert (AV1 : forall a, aview SEGS (w_H WL) (ms_mem msF) a = aview SEGS (w_H WL) memL a)
by (intros a; apply aview_eq_of; apply MEQ2).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
pose proof HEF as ((che & HARe & Hrae & Hra4e & HGP0 & HTP0 & HstkE & HpresE & HchE & HQTE) & HPERM0 & HRFG & HSLG & HRFGe).
(* the room round: every class's live count at this round's loop head is at most the entry's plus one *)
assert (HCL : forall P, (ReplyCnt.acnt P (ablocks B lyL SL) <= ReplyCnt.acnt P (ablocks B ly S) + 1)%nat).
{ intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPERM0). apply rfl_acnt_round. }
change (spZ regs) with sp0 in HstkE, HpresE, HchE.
pose proof HstkE as (HalE & HstkE0 & HceilE & HsloE & HshiE & H47E & HbotE & HtopE & Htop2E).
assert (RSTK0 : 48 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (RSTKG : 48 + GSE_STK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_l GSE_STK ASTACK); lia).
assert (HceilS : alloc_ceiling + RF_STK <= sp0) by lia.
assert (Usp1 : spZ (ms_regs msF) = sp0 + -48) by (unfold spZ in Ksp |- *; rewrite Q2, (EE 2%nat 2%bv eq_refl); lia).
assert (Q3' : getr (ms_regs msF) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), K3; exact HGP0).
assert (Q4' : getr (ms_regs msF) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), K4; exact HTP0).
assert (Q10' : getr (ms_regs msF) 10 = w64 (re_buf e)) by (rewrite Q10, E34; reflexivity).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the free returns to 0x8240c = relay_finish + 200: its caller context is rf_spec's one-entry trace *)
assert (HCF : In (raZ (ms_regs msF) :: spine []) CTX).
{ assert (HRAF : raZ (ms_regs msF) = BASE + AF_fr_relay_finish + 200)
  by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; unfold AF_fr_relay_finish, A_relay_finish in *; lia).
  rewrite HRAF. exact HCTX. }
(* B keeps no frame pointer (s0 is the shadow base SB, below alloc_ceiling): the callee's chain is empty *)
assert (HCH : chain_pre lyL (aview SEGS (w_H WL) (ms_mem msF)) (ms_regs msF) []).
{ apply (achain_chain_pre lyL _ (spZ (ms_regs msF)) SB [] (ms_regs msF)).
  - apply achain_low. unfold SB. lia.
  - rewrite Usp1. unfold ASTACK in RSTK0. lia.
  - unfold s0Z. rewrite Q8, E8. apply unsigned_lit_small. unfold SB. lia.
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
set (r0 := rf_run c O mx no cap (firstn i es)) in *.
assert (Hcap0 : 0 <= gse_cap r0).
{ destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  destruct H26 as [(Hq & _) | (Hq & _)]; lia. }
rewrite (rfl_skipn_S es i Hi) in HSP, HROOM, HPERM, HRML. cbn [rf_cost rf_room rf_eblks concat map] in HSP, HROOM, HPERM, HRML.
fold e in HSP, HROOM, HPERM, HRML.
set (r1 := gse_run (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) in *.
destruct (rfl_gse_nonneg MT MLAW (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0) as [Hgc0 Hgk0].
fold r1 in Hgk0.
pose proof (rfl_cost_nonneg MT MLAW (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0) as Hrc0.
(* the room round: the room this round charges - the free's 1, then gestures_end's - and what the rounds after it
   and rf_post_x are owed (kr5), split exactly: MT_rk's costs are nonnegative *)
pose proof (proj1 (rfl_gse_nonneg MT_rk rfl_rk_laws (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0))
  as Hgrk0.
pose proof (rfl_cost_nonneg MT_rk rfl_rk_laws (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0)
  as Hrrk0.
set (kr5 := (Z.to_nat (rf_cost MT_rk (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) (skipn (Datatypes.S i) es)) + kr)%nat).
set (kr4 := (Z.to_nat (gse_cost MT_rk (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) + kr5)%nat).
assert (HRMf : rp_RM RP SL (1 + kr4)).
{ refine (@eq_ind _ _ (rp_RM RP SL) HRML _ _). unfold kr4, kr5. try change (mo_free MT_rk) with 1. lia. }
(* the room round: the free's count premise, the live counts at its pre state SL (peak 0) *)
assert (HCNTf : cnt_ok RP (ablocks B lyL SL)).
{ unfold cnt_ok. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P). unfold rf_pk. cbv beta. lia. }
pose proof (mo_free_nonneg MT MLAW) as Hmf0.
assert (HMOf : mo_ok MT SL (mo_free MT))
by (exact (mok_station MT S SL (rf_cost MT c O mx no cap es) spent (mo_free MT) MLAW HMOK HMLE Hmf0 ltac:(lia))).
assert (HFPof : 0 < re_cap e -> In (re_buf e, re_cap e) (ablocks B ly S) -> forall j, 0 <= j < req_size (re_cap e) ->
  inFP (rf_FP T es cap out) (re_buf e + j)).
{ intros Hc0 _ j Hj. unfold rf_FP. apply (inFP_ablocks_fp _ (re_buf e) (re_cap e) j); [|exact Hj]. apply in_or_app; right; apply in_or_app; left.
  unfold rf_eblks. apply in_concat. exists (aentry_blks e). split; [apply in_map; apply nth_In; lia|].
  unfold aentry_blks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left; reflexivity. }
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
rewrite (pal_free B TL).
assert (HRFS : ASTACK - -48 <= RF_STK) by lia.
(* the room round: the free's stack room, from the round's inner journal (W_journal_x.v aj_stack_room_x) *)
assert (HSR : ly_bot lyL + ACALL_PREFIX < spZ (ms_regs msF))
by (eapply aj_stack_room_xR; [exact HJi | exact Usp1 | exact HRFS]).
(* the call-boundary premise of the R free rules, from the inner journal's ARx at the call (RO_ARx) *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply (YA0nH.SRrG_bind SEGS R R_trans) with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_xR (SK := SK) SEGS B PST ARx R RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md []
    ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  Permutation (ablocks B lyL SL) (rfl_bblk e ++ ablocks B ly4 S4) /\
  acall_kept SEGS B lyL SL WL mm W4 mem4 (sp0 + -48 - ASTACK) (sp0 + -48) (rfl_bex e) /\
  mo_le MT SL S4 (mo_free MT) /\
  rp_RM RP S4 kr4 /\
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + j) = aview SEGS (w_H WL) mm (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H WL) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct HBUF as [(Hc0 & Hb0) | (Hc0 & Hin0)].
  - eapply SRrG_mono.
    { exact (AFREEN_R WL (ms_regs msF) (ms_mem msF) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [] lyL SL HpL _ _
        (-48) (getr (ms_regs msF) 1) [] kr4 HJi ltac:(rewrite Q10', Hb0; reflexivity) Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HRO HCF HRMf HCNTf HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_eq _ 0) Hc0); exact (Permutation_sym HPm)|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a []|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He Hpr).
  - eapply SRrG_mono.
    { exact (AFREE_R WL (ms_regs msF) (ms_mem msF) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [] lyL SL HpL _ _
        (re_buf e) (re_cap e) (-48) (getr (ms_regs msF) 1) [] kr4 HJi Hin0 Q10' Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HRO HCF HRMf HCNTf
        (HFPof Hc0) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)), Eb1, Eb2; cbn [app];
      exact (Permutation_sym (Permutation_middle l1 l2 _))|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a Ha; unfold rfl_bex; split; [lia | exact Ha]|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He); [|exact Hpr].
    intros Hblk. exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL (ms_mem msF) _ (re_buf e) (re_cap e) a HARc Hin0 Hblk Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HK4 & HML4 & HRM4 & HERR4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK sp0 (rf_FP T es cap out) ly S Hp W mem md []
  ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RF_STK sp0 _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4 memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | intros a Ha _; lia]. }
(* ---- back from free: g_src and g_nsrc are image cells outside the freed block, so free kept them ---- *)
destruct HK4 as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
assert (KFI : forall a, inG rf_cells a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H WL) memL a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & Ho1 & He1). rewrite (KF3 a Hi1 Ho1 He1). apply AV1. }
assert (VS4 : val_mem SEGS (mrestrict (w_H W4) mem4) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W4) memL mem4); [intros q Hq; apply KFI, Hsrc; lia | exact HSRC]. }
assert (VN4 : val_mem SEGS (mrestrict (w_H W4) mem4) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W4) memL mem4); [intros q Hq; apply KFI, Hnsrc; lia | exact HNS]. }
jafter_call_keep_pi HS 36%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - apply (region_kept_val_at E _ _ 246%nat (rg_src RG) 8 T);
    [change 246%nat with (A_OBJ 5); rewrite <- HV5; exact (HEI (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem msF)); [intros q _; apply AV1 | exact HSRC]
    | exact VS4 | lia].
  - apply (region_kept_val_at E _ _ 245%nat (rg_nsrc RG) 4 n);
    [change 245%nat with (A_OBJ 4); rewrite <- HV4; exact (HEI (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem msF)); [intros q _; apply AV1 | exact HNS]
    | exact VN4 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 36 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOK4 : sh_ok SEGS rfl_Bx [] Ea (mrestrict (w_H W4) mem4)) by constructor.
paj_run_to_tok_xR RUNTOG HS HJ4 SHOK4 Bspan AF_fr_gestures_end. { rf_awr. }
rfl_cur HS msG.
assert (MEQb : forall x, mrestrict (w_H W4) mem4 x = mrestrict (w_H W4) mem4 x) by reflexivity.
rfl_meq MEQb MEQ3.
assert (AV2 : forall a, aview SEGS (w_H W4) (ms_mem msG) a = aview SEGS (w_H W4) mem4 a) by (intros a; apply aview_eq_of; apply MEQ3).
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
(* ---- the call gestures_end (s), s = T + 56 i = p.  The run wrote nothing. ---- *)
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR5.
(* the start-of-round block list, entry i's buffer block split off, and it is apart from every other block *)
assert (HPERM' : Permutation (ablocks B lyL SL) ((T, ATABLE) :: rfl_bblk e ++
  (gse_blks e ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r0) outL ++ rest))).
{ eapply Permutation_trans; [exact HPERM|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0).
  change (aentry_blks e) with (rfl_bblk e ++ gse_blks e). fold (rf_eblks (skipn (Datatypes.S i) es)).
  rewrite <- !app_assoc. apply Permutation_refl. }
set (X := gse_blks e ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r0) outL ++ rest) in *.
pose proof (Permutation_NoDup HPERM' (rfl_ablocks_nodup _ _ _ _ _ _ HARL)) as HND.
assert (BUFNOT : re_cap e <> 0 -> ~ In (re_buf e, re_cap e) ((T, ATABLE) :: X)).
{ intros Hc Hin. unfold rfl_bblk in HND. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) Hc) in HND. cbn [app] in HND.
  inversion HND as [|y l Hy Hl]; subst. inversion Hl as [|y' l' Hy' Hl']; subst.
  destruct Hin as [Hin | Hin]; [apply Hy; rewrite Hin; left; reflexivity | exact (Hy' Hin)]. }
assert (HPERM4 : Permutation (ablocks B ly4 S4) ((T, ATABLE) :: X)).
{ apply (Permutation_app_inv_l (rfl_bblk e)). eapply Permutation_trans; [apply Permutation_sym; exact HPM4|].
  eapply Permutation_trans; [exact HPERM'|]. apply Permutation_middle. }
assert (KB : forall b m x, In (b, m) ((T, ATABLE) :: X) -> b <= x < b + req_size m ->
  aview SEGS (w_H W4) (ms_mem msG) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hx. rewrite AV2.
  assert (Hin1 : In (b, m) (ablocks B lyL SL)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM'|];
    destruct Hin as [<- | Hin]; [left; reflexivity | right; apply in_or_app; right; exact Hin]).
  replace x with (b + (x - b)) by lia. rewrite (KF2 b m (x - b) Hin1 ltac:(lia)); [apply AV1|].
  intros (Hc & Hx2). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
  assert (Hne : (b, m) <> (re_buf e, re_cap e)) by (intros Heq; apply (BUFNOT Hc); rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x SEGS B ARx LAWS lyL SL _ WL memL mdL b m _ _ HARL Hin1 Hin0 Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (PR2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H WL) memL a -> apresent (w_H W4) (ms_mem msG) a).
{ intros a Ha Ho He [Hh [b Hb]].
  assert (HP4a : apresent (w_H W4) mem4 a).
  { apply (HPR4 a Ha Ho He). split; [exact Hh|]. exists b. pose proof (MEQ2 (Z_to_bv 64 a)) as E1. unfold mrestrict in E1.
    rewrite Hh in E1. rewrite E1. exact Hb. }
  destruct HP4a as [Hh4 [b4 Hb4]]. split; [exact Hh4|]. exists b4. pose proof (MEQ3 (Z_to_bv 64 a)) as E1.
  unfold mrestrict in E1. rewrite Hh4 in E1. rewrite E1. exact Hb4. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept WL memL W4 (ms_mem msG) a).
{ intros a Ha Ho He. split; [rewrite AV2, (KF3 a Ha Ho He); apply AV1|].
  apply rfl_wr_pres2. exact (PR2 a Ha Ho He). }
assert (HTB4 : In (T, ATABLE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | left; reflexivity]).
assert (HX4 : forall b, In b X -> In b (ablocks B ly4 S4)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | right; exact Hb]).
assert (T10' : getr (ms_regs msG) 10 = w64 p).
{ rewrite T10, OLDa, E33 by lia. reflexivity. }
pose proof HHELD as (Hpd1 & Hpd2 & _).
assert (HrqG : forall m, m <= req_size m) by (intros m; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (GX : forall b, In b (gse_blks e) -> In b X) by (intros b Hb; unfold X; apply in_or_app; left; exact Hb).
assert (OX : forall b, In b (aout_blks (gse_cap r0) outL) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (GA5 : garr8 SEGS (arm W4 (ms_mem msG)) p (bzs (entry_bytes e))).
{ apply (garr8_frame SEGS (arm WL memL) (arm W4 (ms_mem msG)) p _); [unfold p; unfold AENT in HG8; exact HG8|].
  intros x Hx. rewrite (rfl_len_entry e Hpd1 Hpd2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
  apply (KB T ATABLE x (or_introl eq_refl)). change (req_size ATABLE) with 896. unfold p in Hx. lia. }
assert (AW5 : awr W4 (ms_mem msG) p AENT).
{ intros j Hj. apply (apresent_writable SEGS).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ T ATABLE HAR5 HTB4) as (_ & _ & _ & _ & HP & _).
  change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (p + j) ltac:(unfold p, AENT in *; lia))). }
assert (HELD5 : aheld_ok B ly4 S4 W4 (ms_mem msG) e).
{ apply (rfl_aheld_ok_kept lyL SL WL memL ly4 S4 W4 (ms_mem msG) e HHELD).
  - intros b Hb. exact (HX4 b (GX b Hb)).
  - intros b m x Hb Hx. apply (KB b m x (or_intror (GX _ Hb))). pose proof (HrqG m). lia. }
assert (AK5 : akept WL memL W4 (ms_mem msG) (aout_fp B RG (gse_cap r0) outL)).
{ assert (GSL : forall a, inG (G_SL B RG) a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (intros a Ha; destruct (HG a (HSLG a Ha)) as (Gi & Gn & _); exact (conj Gi Gn)).
  intros r Hr a Har. unfold aout_fp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Har.
  - destruct (HPLAINO a (or_introl Har)) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_nout RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 5%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_capout RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 6%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_out RG, 8);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 7%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (HPLAIN a (in_rf_cell 5%nat _ 4 a eq_refl ltac:(clear - Har; lia))) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_client_broken RG, 1);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 8%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - destruct (HPLAINO a (or_intror Har)) as (Ha1 & Ha2 & Ha3). apply KI; assumption.
  - destruct (GSL a ltac:(unfold G_SL, inG; apply Exists_exists; exists (rg_send_eintr RG, 1);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia])) as [Ha1 Ha2].
    zsep_pick HSEPO 10%nat 11%nat DO. apply KI; [exact Ha1 | exact Ha2 | clear - Har DO; lia].
  - split; [rewrite AV2; replace a with (as_errno B + (a - as_errno B)) by lia; rewrite (HERR4 (a - as_errno B) ltac:(lia)); apply AV1|].
    intros _. destruct (HG a (HSLG a ltac:(unfold G_SL, inG; apply Exists_exists; exists (as_errno B, 4);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia]))) as (Hi1 & _ & _).
    unfold arm. apply rf_writable_of_seg; [|exact (HWSEGE a Har)].
    apply (hidden_not_img SEGS W4). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia.
  - destruct (Z.eqb_spec (gse_cap r0) 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Har.
    assert (HobX : In (outL, gse_cap r0) X)
    by (apply OX; unfold aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); left; reflexivity).
    assert (Hrq : req_size (gse_cap r0) = gse_cap r0) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); reflexivity).
    split; [apply (KB outL (gse_cap r0) a (or_intror HobX)); lia|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ outL (gse_cap r0) HAR5 (HX4 _ HobX)) as (_ & _ & _ & _ & HP & _).
    exact (proj1 (HP a ltac:(lia))). }
assert (AOUT5 : aout_at B RG ly4 S4 W4 (ms_mem msG) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL)
by (exact (aout_at_kept B RG lyL SL WL memL ly4 S4 W4 (ms_mem msG) _ _ mx _ _ outL HOUT AK5 (fun b Hb => HX4 b (OX b Hb)))).
assert (HPG5 : Permutation (ablocks B ly4 S4)
  ((T, ATABLE) :: gse_blks e ++ aout_blks (gse_cap r0) outL ++ (rf_eblks (skipn (Datatypes.S i) es) ++ rest))).
{ eapply Permutation_trans; [exact HPERM4|]. unfold X. apply perm_skip. apply Permutation_app_head.
  apply Permutation_app_swap_app. }
destruct HROOM as [HR1 HR2].
assert (HBB4 : blocks_bytes S4 <= blocks_bytes SL).
{ rewrite (blocks_bytes_bsum B lyL SL), (blocks_bytes_bsum B ly4 S4). rewrite (bsum_perm _ _ HPM4), bsum_app.
  assert (0 <= bsum (rfl_bblk e)); [|lia].
  unfold rfl_bblk, bsum. destruct (re_cap e =? 0); cbn [fold_right fst snd]; [lia|].
  destruct HBUF as [(Hc0 & _) | (Hc0 & _)]; lia. }
assert (ROOM5 : gse_room MMAX (blocks_bytes S4) (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e))
by (exact (rfl_gse_room_mono _ _ _ _ _ _ _ HBB4 HR1)).
assert (MO5 : mo_ok MT S4 (gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e))).
{ exact (mok_station MT S S4 (rf_cost MT c O mx no cap es) (spent + mo_free MT) _ MLAW HMOK
    (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) Hgc0 ltac:(lia)). }
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (memS5 & HJin5 & HagS5).
assert (Usp5 : spZ (ms_regs msG) = sp0 + -48) by (unfold spZ in Ksp |- *; rewrite T2, OLDa, (EE 2%nat 2%bv eq_refl) by lia; lia).
assert (T3' : getr (ms_regs msG) 3 = w64 (as_gp B)) by (rewrite T3, OLDa, (EE 3%nat 3%bv eq_refl), K3 by lia; exact HGP0).
assert (T4' : getr (ms_regs msG) 4 = w64 (as_tp B)) by (rewrite T4, OLDa, (EE 4%nat 4%bv eq_refl), K4 by lia; exact HTP0).
assert (HCH5 : achain ly4 (aview SEGS (w_H W4) (ms_mem msG)) (spZ (ms_regs msG)) (s0Z (ms_regs msG)) []).
{ apply achain_low. unfold s0Z. rewrite T8, OLDa, E8 by lia. rewrite unsigned_lit_small by (unfold SB; lia). unfold SB. lia. }
eassert (HPRE5 : afn_pre_x SEGS B ARx GSE_STK ly4 S4 Hp4 W4 (ms_regs msG) (ms_mem msG) _ []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (RF_STK + 0) (sp0 + 0) (rf_FP T es cap out) ly S Hp W memS5 md []
    ly4 S4 Hp4 W4 (ms_mem msG) _ _ (ms_regs msG) GSE_STK (-48) [] HJin5).
  - rewrite Usp5. lia.
  - reflexivity.
  - lia.
  - unfold GSE_STK, GSE_FRAME. pose proof (Z.le_max_r GE_STK ASTACK). unfold ASTACK in *. lia.
  - lia.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1, unsigned_lit_small by lia. lia.
  - exact T3'.
  - exact T4'.
  - exact HCH5. }
assert (ROM4 : rom_view SEGS W4 mem4).
{ apply (acall_kept_rom_view_x SEGS B ARx LAWS lyL SL WL (ms_mem msF) W4 mem4 _ _ (rfl_bex e) ly4 S4 Hp4 md4
    (proj1 HJi4) (conj KF1 (conj KF2 (conj KF3 (conj KF4 (conj KF5 KF6)))))).
  - intros a Ha. destruct (HROMO a Ha) as (_ & H2 & H3 & _). split; [exact H3 | exact H2].
  - intros a Ha. rewrite AV1. exact (HROM a Ha). }
assert (ROM5 : rom_view SEGS W4 (ms_mem msG)) by (intros a Ha; rewrite AV2; exact (ROM4 a Ha)).
assert (END5' : garr8 SEGS (arm W4 (ms_mem msG)) (VAL A_lit_end5) (bzs END5))
by (exact (rfl_end5_kept WL W4 memL (ms_mem msG) HROM ROM5 HEND5)).
(* the room round: at S4 the free only removed a block and the loop head is at most one above the entry (HCL), so
   every callee peak up to 4 fits under the entry's rf_pk = 5 (HCNT5g); gestures_end's gse_pk = 4 is the tight
   instance *)
assert (HCNT5g : forall pk : (Z -> bool) -> nat, (forall P, (pk P <= 4)%nat) -> cnt_ok_pk RP pk (ablocks B ly4 S4)).
{ intros pk Hpk. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P) as H1. pose proof (ReplyCnt.acnt_perm P _ _ HPM4) as H2. rewrite ReplyCnt.acnt_app in H2.
  pose proof (Hpk P) as H3. unfold rf_pk. cbv beta. lia. }
assert (HCNT5 : cnt_ok_pk RP gse_pk (ablocks B ly4 S4)) by (apply HCNT5g; intros P; unfold gse_pk; lia).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ exact (GSE_R W4 ly4 S4 Hp4 (ms_regs msG) (ms_mem msG) _ [] p T e (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL
    (rf_eblks (skipn (Datatypes.S i) es) ++ rest) HPRE5 T10' HTB4 ltac:(unfold p; lia) ltac:(unfold p, AENT, ATABLE; lia) Hp8
    GA5 AW5 HELD5 AOUT5 HPG5 END5' ROM5 ROOM5 MO5 kr5 HRM4 HCNT5). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & out5 & -> & HJsl & HPsl & HPKsl & HMOsl & HRMsl & HPERMsl & HAOsl & HGAsl & HAWsl).
rewrite T1. fold r1 in HPERMsl, HAOsl.
(* ---- back from gestures_end: its journal (at G_SL) lifted to G and composed into the round's ---- *)
pose proof (ajournal_gx_G_mono_xR SEGS B PST ARx (G_SL B RG) G 0 [] GSE_STK (spZ (ms_regs msG)) _ ly4 S4 Hp4 W4 (ms_mem msG) _ []
  ly5 S5 Hp5 W5 mem5 md5 k5 HSLG HJsl) as HJslG.
assert (FPC : forall a, inFP ((p + 40, p + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL)) a ->
  (inFP (rf_FP T es cap out) a /\ exists b n, In (b, n) (ablocks B ly4 S4) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly4 S4) a).
{ intros a Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
  - left. split.
    + replace a with (T + (a - T)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ T ATABLE (a - T));
      [apply in_or_app; left; unfold rf_tblk; rewrite (proj2 (Z.eqb_neq T 0) HT0); left; reflexivity
      | change (req_size ATABLE) with 896; unfold p in Hf; lia].
    + exists T, ATABLE. split; [exact HTB4 | change (req_size ATABLE) with 896; unfold p in Hf; lia].
  - destruct (inFP_ablocks_fp_inv _ a Hf) as (b & m & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. split.
      * replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [|lia].
        apply in_or_app; right; apply in_or_app; left. unfold rf_eblks. apply in_concat. exists (aentry_blks e).
        split; [apply in_map, nth_In; lia|]. change (aentry_blks e) with (rfl_bblk e ++ gse_blks e).
        apply in_or_app; right; exact Hin.
      * exists b, m. split; [exact (HX4 _ (GX _ Hin)) | exact Hr].
    + destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly S)) as [Hin0 | Hnin0].
      * left. split; [|exists b, m; split; [exact (HX4 _ (OX _ Hin)) | exact Hr]].
        assert (Hin1 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest))
        by (eapply Permutation_in; [exact HPERM0 | exact Hin0]).
        assert (Hin2 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
        { rewrite !app_assoc in Hin1. rewrite !app_assoc. apply in_app_or in Hin1. destruct Hin1 as [H1 | H1]; [exact H1|].
          exfalso. pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HNf.
          inversion HNf as [|y0 l0 _ HNXf]; subst y0 l0.
          exact (rfl_nodup_app_r _ _ (b, m) (rfl_nodup_tl _ _ (rfl_nodup_tl _ _ HNXf)) Hin H1). }
        replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [exact Hin2 | lia].
      * right. exists b, m. split; [exact (HX4 _ (OX _ Hin)) | split; [exact Hnin0 | exact Hr]]. }
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G RF_STK sp0 0 [] (rf_FP T es cap out) ly S Hp W mem md []
  ly4 S4 Hp4 W4 (ms_mem msG) _ _ GSE_STK (spZ (ms_regs msG)) 0 [] _ [] ly5 S5 Hp5 W5 mem5 md5 k5 HJ4 HJslG
  ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia)
  ltac:(intros a Hf; exfalso; exact (inFP_nil a Hf)) HG FPC) as HJ6.
cbn [app] in HJ6.
(* what gestures_end kept: every image byte outside G_SL, and live blocks' bytes outside its footprint *)
pose proof (ajournal_gx_inner_xR SEGS B PST ARx (G_SL B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS6 & HJin6 & HagS6).
pose proof HJin6 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (HFPC1 : ~ YI16.sink_open_fp ((p + 40, p + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL))).
{ apply sink_closed_pos. constructor; [cbn [fst]; unfold p; lia|]. unfold ablocks_fp. apply Forall_map.
  apply Forall_forall. intros [b m] Hb. cbn [fst].
  assert (Hb4 : In (b, m) (ablocks B ly4 S4))
  by (apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [exact (HX4 _ (GX _ Hb)) | exact (HX4 _ (OX _ Hb))]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ b m HAR5 Hb4) as (_ & H4096 & _). lia. }
assert (KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msG) a).
{ intros a Ha Ho He Hps Hg. rewrite (G3 a Ha Ho He Hps (fp_spares_closed _ a HFPC1)).
  apply HagS6. rewrite unsigned_lit_small; [exact Hg|]. pose proof (Hsegs a Ha). unfold kLowMemEnd in *. lia. }
assert (NGN : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 1%nat).
assert (VN5a : val_mem SEGS (mrestrict (w_H W4) (ms_mem msG)) (rg_nsrc RG) 4 n)
by (apply (val_mem_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem msG)); [intros q _; apply AV2 | exact VN4]).
assert (VN5 : val_mem SEGS (mrestrict (w_H W5) mem5) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H W4) (w_H W5) (ms_mem msG) mem5); [|exact VN5a].
  intros q Hq. destruct (HPLAIN (rg_nsrc RG + q) (Hnsrc (rg_nsrc RG + q) ltac:(lia))) as (Hq1 & Hq2 & Hq3).
  exact (KG _ Hq1 Hq2 Hq3 (PSTC _ (Hnsrc (rg_nsrc RG + q) ltac:(lia))) (NGN (rg_nsrc RG + q) ltac:(lia))). }
jafter_call_keep_pi HS 52%nat regs5 (mrestrict (w_H W5) mem5) HPsl [1]%nat HS6.
match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  apply (region_kept_val_at Ea _ _ 245%nat (rg_nsrc RG) 4 n);
  [change 245%nat with (A_OBJ 4); rewrite <- HV4; exact (HEIa (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | exact VN5a | exact VN5 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc Ea 52 (map (getr regs5) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (SHOK6 : sh_ok SEGS rfl_Bx [] Eb (mrestrict (w_H W5) mem5)) by constructor.
paj_run_tok_xR RUNG HS HJ6 SHOK6 Bspan. { rf_awr. }
(* ---- the round's end state N (the last run wrote nothing): what RFI at i + 1 and RFX need ---- *)
rfl_cur HS msN.
assert (MEQc : forall x, mrestrict (w_H W5) mem5 x = mrestrict (w_H W5) mem5 x) by reflexivity.
rfl_meq MEQc MEQ4.
assert (AV3 : forall a, aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H W5) mem5 a) by (intros a; apply aview_eq_of; apply MEQ4).
assert (MG3 : mem_grows (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem msN))) by (intros x Hx; rewrite MEQ4; exact Hx).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
(* the read-only view after gestures_end: its journal at G_SL keeps it (rom_out of G_SL) *)
assert (ROM6 : rom_view SEGS W5 mem5).
{ eapply (ajournal_gx_rom_view_xR SEGS B PST ARx). all: first [exact LAWS | exact Hsegs | exact HJsl | exact HROMO | exact PSTR | exact ROM5]. }
assert (ROMN : rom_view SEGS W5 (ms_mem msN)) by (intros a Ha; rewrite AV3; exact (ROM6 a Ha)).
assert (KNI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H WL) memL a).
{ intros a Ha Ho He Hps Hg. rewrite AV3, (KG a Ha Ho He Hps Hg), AV2, (KF3 a Ha Ho He). apply AV1. }
assert (RFW : forall a, inG rf_cells a -> writable_at SEGS (arm W5 (ms_mem msN)) a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
  apply (hidden_not_img SEGS W5). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (KCELL : forall lo len, (forall x, lo <= x < lo + len -> inG rf_cells x /\ ~ inG (G_SL B RG) x) ->
  forall q, lo <= q < lo + len -> abyte_kept WL memL W5 (ms_mem msN) q).
{ intros lo len Hc q Hq. destruct (Hc q Hq) as [Hq1 Hq2]. destruct (HPLAIN q Hq1) as (Hi1 & Ho1 & He1).
  split; [exact (KNI q Hi1 Ho1 He1 (PSTC q Hq1) Hq2) | intros _; exact (RFW q Hq1)]. }
assert (NGL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 0%nat).
assert (NGG : forall a, GL <= a < GL + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 3%nat).
assert (NGS : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 12%nat).
assert (NGC : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 13%nat).
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 1%nat _ 12 a eq_refl Ha)).
assert (ICS : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 4%nat _ 4 a eq_refl Ha)).
assert (IGL : forall a, GL <= a < GL + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 6%nat _ 4 a eq_refl Ha)).
assert (VNN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HNS]. intros q Hq.
  exact (proj1 (KCELL (rg_nsrc RG) 4 (fun x Hx => conj (Hnsrc x Hx) (NGN x Hx)) (rg_nsrc RG + q) ltac:(lia))). }
assert (VSN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HSRC]. intros q Hq.
  exact (proj1 (KCELL (rg_src RG) 8 (fun x Hx => conj (Hsrc x Hx) (NGS x Hx)) (rg_src RG + q) ltac:(lia))). }
assert (VCN : val_mem SEGS (arm W5 (ms_mem msN)) (rg_capsrc RG) 4 16).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact HCAP]. intros q Hq.
  exact (proj1 (KCELL (rg_capsrc RG) 4 (fun x Hx => conj (ICS x Hx) (NGC x Hx)) (rg_capsrc RG + q) ltac:(lia))). }
assert (WNN : awr W5 (ms_mem msN) (rg_nsrc RG) 4) by (intros j Hj; exact (RFW _ (Hnsrc (rg_nsrc RG + j) ltac:(lia)))).
assert (WSN : awr W5 (ms_mem msN) (rg_src RG) 8) by (intros j Hj; exact (RFW _ (Hsrc (rg_src RG + j) ltac:(lia)))).
assert (WCN : awr W5 (ms_mem msN) (rg_capsrc RG) 4) by (intros j Hj; exact (RFW _ (ICS (rg_capsrc RG + j) ltac:(lia)))).
assert (LKN : alock_at RG W5 (ms_mem msN) true).
{ apply (alock_at_kept RG WL memL W5 (ms_mem msN) true HLK). intros r [<- | []] a Har. cbn [fst snd] in Har.
  exact (KCELL (rg_lock RG) 12 (fun x Hx => conj (ILK x Hx) (NGL x Hx)) a Har). }
assert (GLN : exists lst, val_mem SEGS (arm W5 (ms_mem msN)) GL 4 lst).
{ destruct HGLv as [lst Hl]. exists lst. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact Hl].
  intros q Hq. exact (proj1 (KCELL GL 4 (fun x Hx => conj (IGL x Hx) (NGG x Hx)) (GL + q) ltac:(lia))). }
assert (GLW : awr W5 (ms_mem msN) GL 4) by (intros j Hj; exact (RFW _ (IGL (GL + j) ltac:(lia)))).
assert (HTBN : In (T, ATABLE) (ablocks B ly5 S5)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | left; reflexivity]).
(* the round's own stack frame [sp0 - 48, sp0) is kept: the callees run below sp0 - 48 *)
assert (KNF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W5) (ms_mem msN) a = aview SEGS (w_H WL) memL a).
{ intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (clear - Ha HceilS RSTK0 HshiE H47E; unfold ASTACK in *; lia).
  rewrite AV3. rewrite (G1 a Hac ltac:(rewrite Usp5; lia)).
  rewrite HagS6; [rewrite AV2, (KF1 a Hac ltac:(lia)); apply AV1|].
  rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as (Hi1 & _ & _). pose proof (Hsegs a Hi1).
  unfold kLowMemEnd in *. lia. }
assert (RSV : rf_saved W5 (ms_mem msN) sp0 regs).
{ intros k0 Hk0. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem msN)); [|exact (HSV k0 Hk0)].
  intros q Hq. apply KNF. lia. }
(* the entries the loop has not reached keep their bytes and blocks: none of them is in gestures_end's footprint *)
pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HND4.
assert (HRN : forall b, In b (rf_eblks (skipn (Datatypes.S i) es) ++ rest) -> In b (ablocks B ly5 S5))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; right; exact Hb]).
assert (EX : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (KR : forall b m x, In (b, m) ((T, ATABLE) :: X) -> In (b, m) (ablocks B ly5 S5) ->
  ~ In (b, m) (gse_blks e ++ aout_blks (gse_cap r0) outL) -> b <= x < b + req_size m -> ~ (p + 40 <= x < p + 52) ->
  aview SEGS (w_H W5) (ms_mem msN) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hin5 Hng Hx Hs. rewrite AV3.
  assert (Hin4 : In (b, m) (ablocks B ly4 S4)) by (destruct Hin as [<- | Hin]; [exact HTB4 | exact (HX4 _ Hin)]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem msG) _ b m HAR5 Hin4) as (_ & Hb4096 & Hbceil & _).
  replace x with (b + (x - b)) by lia. rewrite (G2 b m (x - b) Hin4 Hin5 ltac:(lia)).
  - rewrite HagS6.
    + replace (b + (x - b)) with x by lia. exact (KB b m x Hin Hx).
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as (Hi2 & _ & _).
      exact (blk_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m (b + (x - b)) HAR5 Hin4 ltac:(lia) Hi2).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia|].
    destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
    assert (Hin4' : In (b', m') (ablocks B ly4 S4))
    by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
    assert (Hne : (b, m) <> (b', m')) by (intros Heq; apply Hng; rewrite Heq; exact Hin').
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m b' m' HAR5 Hin4 Hin4' Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ENTN : forall j, (Datatypes.S i <= j < length es)%nat ->
  garr8 SEGS (arm W5 (ms_mem msN)) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
  awr W5 (ms_mem msN) (T + AENT * Z.of_nat j) AENT /\
  aheld_ok B ly5 S5 W5 (ms_mem msN) (nth j es rf_e0) /\
  ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
   (0 < re_cap (nth j es rf_e0) /\ In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly5 S5)))).
{ intros j Hj. destruct (HENT j ltac:(lia)) as (Gj & Aj & Hj' & Bj). pose proof Hj' as (Pj1 & Pj2 & _).
  assert (Hej : In (nth j es rf_e0) (skipn (Datatypes.S i) es)) by (apply rfl_in_skipn; lia).
  assert (EBj : forall b, In b (aentry_blks (nth j es rf_e0)) -> In b (rf_eblks (skipn (Datatypes.S i) es)))
  by (intros b Hb; unfold rf_eblks; apply in_concat; exists (aentry_blks (nth j es rf_e0)); split; [apply in_map; exact Hej | exact Hb]).
  inversion HND4 as [|y0 l0 HnT HNX]; subst y0 l0.
  assert (NGj : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> ~ In b (gse_blks e ++ aout_blks (gse_cap r0) outL)).
  { intros b Hb Hb2. apply in_app_or in Hb2. destruct Hb2 as [Hb2 | Hb2].
    - exact (rfl_nodup_app_r _ _ b HNX Hb2 (in_or_app _ _ _ (or_introl Hb))).
    - pose proof (rfl_nodup_tl _ _ HNX) as HNX'.
      exact (rfl_nodup_app_r _ _ b HNX' Hb (in_or_app _ _ _ (or_introl Hb2))). }
  assert (NGT : ~ In (T, ATABLE) (gse_blks e ++ aout_blks (gse_cap r0) outL)).
  { intros Hb2. apply HnT. apply in_app_or in Hb2. destruct Hb2 as [Hb2 | Hb2]; [exact (GX _ Hb2) | exact (OX _ Hb2)]. }
  assert (NTj : forall b m x, In (b, m) (rf_eblks (skipn (Datatypes.S i) es)) -> b <= x < b + req_size m ->
    ~ (T <= x < T + 896)).
  { intros b m x Hb Hx Hx2.
    assert (Hne : (b, m) <> (T, ATABLE)) by (intros Heq; apply HnT; rewrite <- Heq; exact (EX _ Hb)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem msG) _ b m T ATABLE HAR5 (HX4 _ (EX _ Hb)) HTB4 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D. lia. }
  split; [|split; [|split]].
  - apply (garr8_frame SEGS (arm WL memL) (arm W5 (ms_mem msN)) _ _ Gj). intros x Hx.
    rewrite (rfl_len_entry _ Pj1 Pj2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
    apply (KR T ATABLE x (or_introl eq_refl) HTBN NGT); [change (req_size ATABLE) with 896; unfold AENT in Hx; lia | unfold p, AENT in *; lia].
  - intros q Hq. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly5 S5 _ W5 (ms_mem msN) _ T ATABLE HAR6 HTBN) as (_ & _ & _ & _ & HP & _).
    change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
  - apply (rfl_aheld_ok_kept lyL SL WL memL ly5 S5 W5 (ms_mem msN) _ Hj').
    + intros b Hb. apply HRN. apply in_or_app; left. apply EBj.
      change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
      apply in_or_app; right; exact Hb.
    + intros b m x Hb Hx.
      assert (HbE : In (b, m) (rf_eblks (skipn (Datatypes.S i) es))).
      { apply EBj. change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
        apply in_or_app; right; exact Hb. }
      pose proof (HrqG m) as Hm.
      apply (KR b m x (or_intror (EX _ HbE)) (HRN _ (in_or_app _ _ _ (or_introl HbE))) (NGj _ HbE)); [lia|].
      intros Hs. apply (NTj b m x HbE ltac:(lia)). unfold p in Hs. lia.
  - destruct Bj as [Bj | (Bc & Bin)]; [left; exact Bj | right; split; [exact Bc|]].
    apply HRN. apply in_or_app; left. apply EBj. unfold aentry_blks.
    rewrite (proj2 (Z.eqb_neq (re_cap (nth j es rf_e0)) 0) ltac:(lia)). left; reflexivity. }
(* the stream, the blocks, presence, the meter and the model after round i *)
assert (AOUTN : aout_at B RG ly5 S5 W5 (ms_mem msN) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5).
{ apply (aout_at_kept B RG ly5 S5 W5 mem5 ly5 S5 W5 (ms_mem msN) _ _ mx _ _ out5 HAOsl).
  - intros r Hr a Har. split; [apply AV3 | apply (writable_at_grows SEGS _ _ a MG3)].
  - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]. }
assert (PERMN : Permutation (ablocks B ly5 S5)
  (rf_tblk T ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r1) out5 ++ rest)).
{ eapply Permutation_trans; [exact HPERMsl|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0). cbn [app].
  apply perm_skip. apply Permutation_app_swap_app. }
assert (APK : apres_kept B W mem W5 (ms_mem msN)).
{ intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) mem5 (ms_mem msN) a MG3). apply (HPKsl a Ha Ho He).
  apply (PR2 a Ha Ho He). exact (HPK a Ha Ho He Hpr). }
assert (MLE : mo_le MT S S5 (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)))
by (exact (mle_station MT S S4 S5 _ _ MLAW (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) HMOsl)).
assert (NNL : forall b, In b (ablocks B lyL SL) -> 0 <= snd b).
{ intros [bb mm] Hb. cbn [snd]. exact (BLKN lyL SL HpL WL memL mdL bb mm HARL Hb). }
assert (INL : forall b, In b ((T, ATABLE) :: rfl_bblk e ++ X) -> In b (ablocks B lyL SL))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM' | exact Hb]).
(* rf_room's `- cap` threading (W_contract.v rf_room): the round frees the OLD g_out block (outL, gse_cap r0) and
   holds the new one (out5, gse_cap r1), so the rest's room grows only by gse_cap r1 - gse_cap r0; the old block's
   bytes are exactly gse_cap r0 (rfl_bsum_aout_eq), not merely nonnegative *)
assert (HBB5 : blocks_bytes S5 <= blocks_bytes SL + gse_cap r1 - gse_cap r0).
{ rewrite (blocks_bytes_bsum B ly5 S5), (blocks_bytes_bsum B lyL SL), (bsum_perm _ _ HPERMsl), (bsum_perm _ _ HPERM').
  rewrite !bsum_cons, !bsum_app. unfold X. rewrite !bsum_app.
  pose proof (rfl_bsum_aout (gse_cap r1) out5 Hgk0).
  pose proof (rfl_bsum_nonneg (rfl_bblk e) (fun b Hb => NNL b (INL b (or_intror (in_or_app _ _ _ (or_introl Hb)))))).
  pose proof (rfl_bsum_nonneg (gse_blks e) (fun b Hb => NNL b (INL b (or_intror (in_or_app _ _ _ (or_intror (GX _ Hb))))))).
  rewrite (rfl_bsum_aout_eq (gse_cap r0) outL).
  lia. }
assert (ROOMN : rf_room MMAX (blocks_bytes S5) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) (skipn (Datatypes.S i) es))
by (exact (rfl_room_mono _ _ _ _ _ _ _ _ HBB5 HR2)).
assert (RUNS : rf_run c O mx no cap (firstn (Datatypes.S i) es) = (gse_c r1, gse_O r1, gse_no r1, gse_cap r1))
by (rewrite (rfl_firstn_S es i Hi), rfl_run_app; reflexivity).
assert (U19 : U Eb (SOff 19 1) = Z.of_nat i + 1).
{ apply (U_atom_off Eb 19 (Z.of_nat i) 1); [rewrite OLDb, OLDa, (EE 19%nat 19%bv eq_refl) by lia; exact H19 | lia | lia]. }
assert (U35 : U Eb (SOff 35 0) = n) by (apply (U_atom Eb 35 n); [rewrite OLDb, OLDa by lia; exact E35 | unfold n; lia]).
assert (RKF : forall regsF : bvmap 5 word,
  (forall r, In r [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsF r = getr regsL r) ->
  getr regsF 9 = ew Eb 285 -> getr regsF 20 = ew Eb 286 ->
  rf_kept regs regsF sp0 /\ getr regsF 8 = w64 SB /\ getr regsF 20 = w64 (VAL (A_HI 6))).
{ intros regsF HKN N9 N20. split; [|split].
  - unfold rf_kept.
    split; [unfold spZ in Ksp |- *; rewrite (HKN 2%bv ltac:(cbv; tauto)); exact Ksp|].
    split; [rewrite (HKN 3%bv ltac:(cbv; tauto)); exact K3|].
    split; [rewrite (HKN 4%bv ltac:(cbv; tauto)); exact K4|].
    split; [rewrite (HKN 21%bv ltac:(cbv; tauto)); exact K21|].
    split; [rewrite (HKN 22%bv ltac:(cbv; tauto)); exact K22|].
    split; [rewrite (HKN 23%bv ltac:(cbv; tauto)); exact K23|].
    split; [rewrite (HKN 24%bv ltac:(cbv; tauto)); exact K24|].
    split; [rewrite (HKN 25%bv ltac:(cbv; tauto)); exact K25|].
    split; [rewrite (HKN 26%bv ltac:(cbv; tauto)); exact K26|].
    split; [rewrite (HKN 27%bv ltac:(cbv; tauto)); exact K27|].
    rewrite N9. change 285%nat with (A_HI 5). exact (img_env_atomP Eb (A_HI 5) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
  - rewrite (HKN 8%bv ltac:(cbv; tauto)). exact H8.
  - rewrite N20. change 286%nat with (A_HI 6). exact (img_env_atomP Eb (A_HI 6) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)). }
(* the branch and the jump to its target write nothing: every fact above carries to the final memory *)
assert (FIN : forall m, (forall a, aview SEGS (w_H W5) m a = aview SEGS (w_H W5) (ms_mem msN) a) ->
  mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) m) ->
  rf_saved W5 m sp0 regs /\
  val_mem SEGS (arm W5 m) (rg_nsrc RG) 4 n /\ awr W5 m (rg_nsrc RG) 4 /\
  val_mem SEGS (arm W5 m) (rg_src RG) 8 T /\ awr W5 m (rg_src RG) 8 /\
  val_mem SEGS (arm W5 m) (rg_capsrc RG) 4 16 /\ awr W5 m (rg_capsrc RG) 4 /\
  (forall j, (Datatypes.S i <= j < length es)%nat ->
    garr8 SEGS (arm W5 m) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
    awr W5 m (T + AENT * Z.of_nat j) AENT /\
    aheld_ok B ly5 S5 W5 m (nth j es rf_e0) /\
    ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
     (0 < re_cap (nth j es rf_e0) /\ In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly5 S5)))) /\
  alock_at RG W5 m true /\
  aout_at B RG ly5 S5 W5 m (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5 /\
  (exists lst, val_mem SEGS (arm W5 m) GL 4 lst) /\ awr W5 m GL 4 /\
  apres_kept B W mem W5 m).
{ intros m AVF MGF.
  assert (KF : forall a, abyte_kept W5 (ms_mem msN) W5 m a)
  by (intros a; split; [apply AVF | apply (writable_at_grows SEGS _ _ a MGF)]).
  split; [intros k0 Hk0; apply (val_mem_kept SEGS (w_H W5) (w_H W5) (ms_mem msN) m); [intros q _; apply AVF | exact (RSV k0 Hk0)]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VNN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WNN]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VSN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WSN]|].
  split; [apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact VCN]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact WCN]|].
  split.
  { intros j Hj. destruct (ENTN j Hj) as (G1' & A1' & H1' & B1'). split; [|split; [|split]].
    - apply (akept_garr8 W5 (ms_mem msN)); [intros x _; apply KF | exact G1'].
    - apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact A1'].
    - exact (rfl_aheld_ok_mem ly5 S5 W5 (ms_mem msN) W5 m _ H1' AVF).
    - exact B1'. }
  split; [apply (alock_at_kept RG W5 (ms_mem msN) W5 m true LKN); intros r _ a _; apply KF|].
  split; [apply (aout_at_kept B RG ly5 S5 W5 (ms_mem msN) ly5 S5 W5 m _ _ mx _ _ out5 AOUTN);
    [intros r _ a _; apply KF
    | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]]|].
  split; [destruct GLN as [lst Hl]; exists lst; apply (akept_vm W5 (ms_mem msN)); [intros x _; apply KF | exact Hl]|].
  split; [apply (akept_awr W5 (ms_mem msN)); [intros x _; apply KF | exact GLW]|].
  intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) (ms_mem msN) m a MGF). exact (APK a Ha Ho He Hpr). }
psrr_branch_tok RUNG BRR HS SHOK6 Bspan.
- (* i + 1 < |es|: back to the loop head, RFI at i + 1 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U19, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U19, ?U35; unfold n; lia). rewrite U19, U35 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_xR RUNTOG HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 0x7c). { rf_awr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem msN) a)
  by (intros a; apply aview_eq_of; apply Hx; rfl_nowr) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  assert (ROMF : rom_view SEGS W5 (ms_mem msF)) by (intros a Ha; rewrite AV4; exact (ROMN a Ha));
  assert (E5F : garr8 SEGS (arm W5 (ms_mem msF)) (VAL A_lit_end5) (bzs END5))
  by (exact (rfl_end5_kept WL W5 memL (ms_mem msF) HROM ROMF HEND5));
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  pmkst HS.
  apply (IH regs ly S Hp W mem md T es c O mx no cap out rest (Datatypes.S i) ly5 S5 Hp5 W5); [lia | exact HCNT0 |].
  assert (RC : gse_c (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (ROc : gse_O (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_cap r1) by (rewrite RUNS; reflexivity).
  destruct (RKF _ HKN2 N9 N20) as (RK1 & RK2 & RK3).
  refine (ex_intro _ _ (ex_intro _ out5 (ex_intro _ (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) _))).
  rewrite RC, ROc, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact RK1|].
  split; [exact RK2|].
  split; [exact RK3|].
  split; [rewrite N19, OLDb, OLDa, (EE 19%nat 19%bv eq_refl), H19 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N18, OLDb, OLDa, (EE 18%nat 18%bv eq_refl), H18 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [exact RSVF|].
  split; [lia|]. split; [exact Hn16|]. split; [exact HT0|].
  split; [exact VNF|]. split; [exact WNF|]. split; [exact VSF|]. split; [exact WSF|]. split; [exact VCF|]. split; [exact WCF|].
  split; [exact HTBN|].
  split; [exact ENTF|].
  split; [exact LKF|].
  split; [exact AOUTF|].
  split; [exact PERMN|].
  split; [exact GLF|]. split; [exact GLWF|].
  split; [exact E5F|]. split; [exact ROMF|].
  split; [exact APKF|].
  split; [exact ROOMN|].
  split; [exact MLE|].
  split; [lia|].
  split; [exact HMOK|].
  (* the room round: gestures_end's post leaves what the rounds after this one are owed, then kr *)
  exact HRMsl.
- (* i + 1 = |es|: the tail, RFX *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U19, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U19, ?U35; unfold n; lia). rewrite U19, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Hlast : Datatypes.S i = length es) by (unfold n in Hc; lia).
  paj_run_to_tok_xR RUNTOG HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 0xf8). { rf_awr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem msN) a)
  by (intros a; apply aview_eq_of; apply Hx; rfl_nowr) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem msN)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (9%bv : bv 5) N9. prreg HS (20%bv : bv 5) N20.
  pmkst HS.
  assert (SK0 : skipn (Datatypes.S i) es = []) by (rewrite Hlast; apply skipn_all).
  assert (FA : firstn (Datatypes.S i) es = es) by (rewrite Hlast; apply firstn_all).
  rewrite SK0 in HSP, PERMN. cbn [rf_cost rf_eblks concat map app] in HSP, PERMN. rewrite FA in RUNS.
  assert (RC : gse_c (rf_run c O mx no cap es) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (ROc : gse_O (rf_run c O mx no cap es) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap es) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap es) = gse_cap r1) by (rewrite RUNS; reflexivity).
  destruct (RKF _ HKN2 N9 N20) as (RK1 & _ & _).
  apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest ly5 S5 Hp5 W5).
  refine (ex_intro _ _ (ex_intro _ out5 _)).
  rewrite RC, ROc, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact RK1|].
  split; [exact RSVF|].
  split; [split; [exact WNF | right; split; [exact HT0 | split; [exact VSF | split; [exact WSF | split; [exact VCF | split; [exact WCF | exact HTBN]]]]]]|].
  split; [exact LKF|].
  split; [exact AOUTF|].
  split; [exact PERMN|].
  split; [exact GLF|]. split; [exact GLWF|].
  split; [exact APKF|].
  split; [apply (mle_weaken MT S S5 _ _ MLAW MLE); lia|].
  (* the room round: no round is left, so gestures_end's post leaves exactly kr *)
  refine (@eq_ind _ _ (rp_RM RP S5) HRMsl _ _). unfold kr5. rewrite SK0. reflexivity.
Qed.
Theorem pb_relay_finish_xR : rf_spec_xR B PST ARx R MT RP MMAX G RG GTU GL CTX (BASE + AF_fr_relay_finish).
Proof using All - (AFREE AFREE0 GSE).
unfold rf_spec_xR. intros W ly S Hp regs mem md ch T es c O mx no cap out rest
HPRE Hal32 HCNT HGTU0 HLOCK HREL HGLv HGLw HOUT HPERM HEND5 HROM HG1 HG2 HG3 HROOM HCTX HMOK kr HRMe HCNTe.
change (BASE + AF_fr_relay_finish) with A_relay_finishP.
pose proof (rf_loop_xR rf_tail_xR HCTX) as LOOP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rf_entry W ly S Hp regs mem md ch HPRE HGTU0) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16672) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (ajournal_x_initR (SK := SK) SEGS B PST ARx R_refl RF_STK (rf_FP T es cap out) ly S Hp W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs rf_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rf_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_relay_finishP) with (Z_to_bv 64 A_relay_finishP). unfold A_relay_finishP, A_relay_finish.
paj_run_tok_xR RUN0G HS HJ SHOK Bspan. { awr_any. exact Usp. }
lazymatch goal with Hx : mem_grows _ _ |- _ => rename Hx into MG0 end.
lazymatch goal with Hx : frame_of _ _ _ _ |- _ => rename Hx into HFr0 end.
(* the prologue run writes only the frame [sp0 - 48, sp0) *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr0 a Ha).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia | ]).
  destruct Hin. }
assert (P0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
by (intros a Ha; exact (apresent_grows (w_H W) mem (ms_mem ms) a MG0 Ha)).
assert (WK0 : forall a, writable_at SEGS (arm W mem) a -> writable_at SEGS (arm W (ms_mem ms)) a)
by (intros a Ha; exact (writable_at_grows SEGS _ _ a MG0 Ha)).
(* the six saved words, as the prologue stored them *)
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (SV0 : rf_saved W (ms_mem ms) (spZ regs) regs).
{ intros k Hk.
  destruct k as [|[|[|[|[|[|k]]]]]]; [ | | | | | | lia].
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 20%bv 20%nat (-48) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 0) with (spZ regs + -48) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 19%bv 19%nat (-40) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 1) with (spZ regs + -40) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 18%bv 18%nat (-32) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 2) with (spZ regs + -32) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 9%bv 9%nat (-24) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 3) with (spZ regs + -24) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 8%bv 8%nat (-16) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 4) with (spZ regs + -16) by lia. exact V.
  - pose proof (rf_saved_word E _ (spZ regs) _ _ _ _ _ 1%bv 1%nat (-8) regs rf_extra HR0 Usp
      ltac:(repeat (first [left; reflexivity | right])) eq_refl HAE ltac:(lia)) as V.
    replace (spZ regs - 48 + 8 * Z.of_nat 5) with (spZ regs + -8) by lia. exact V. }
clear HR0.
(* the call to pthread_mutex_lock (&g_lock) *)
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
eassert (HJX : ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md
  _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_xR; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ | apply gagree_refl | intros a Ha Hn; lia]. }
assert (HPOS : Forall (fun b : Z * Z => 0 < fst b) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
{ apply Forall_forall. intros [p n] Hb. cbn [fst].
  assert (Hin : In (p, n) (ablocks B ly S)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
    apply in_app_iff in Hb. apply in_or_app.
    destruct Hb as [Hb | Hb]; [left; exact Hb|]. right.
    apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb | Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md p n HAR Hin) as (_ & H4096 & _). lia. }
assert (HFPC : ~ YI16.sink_open_fp (rf_FP T es cap out))
by (unfold rf_FP; exact (sink_closed_ablocks_fp _ HPOS)).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed _ a HFPC)). }
pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a)
by (intros a Ha; exact (in_rf_cell 1%nat (rg_lock RG) 12 a eq_refl Ha)).
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as HLKb. cbn [fst snd] in HLKb.
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; destruct (HPLAIN a (ILK a Ha)) as (Hi & Ho & He); exact (KIMG a Hi Ho He (PSTC a (ILK a Ha)))).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms) = spZ regs + -48).
{ unfold spZ at 1. rewrite QSP, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3). rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV3. reflexivity. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-48) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (LKK a ltac:(lia)). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + exact RGAL.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4m.
    + intros a Ha. split; [rewrite (LKK a ltac:(lia)); exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. destruct (HPLAIN a (ILK a ltac:(lia))) as (Hi & Ho & He). split; [|split].
      * apply rf_writable_of_seg; [exact (hidden_not_img SEGS W (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hi))
        | exact (HWSEG a (ILK a ltac:(lia)))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))).
      apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
jafter_call_keep_pi HS 33%nat regs3 (mrestrict (w_H W) mem3) HP3 ([] : list nat) HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* the saved words survive the lock (it writes only the lock word and its scratch below sp0 - 48) *)
assert (SV3 : rf_saved W mem3 (spZ regs) regs).
{ intros k Hk. apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms) mem3); [|exact (SV0 k Hk)].
  intros q Hq. apply Hfr3; [lia | lia | unfold ESTACK; lia]. }
(* the env after the call *)
remember (YN3v.havoc E 33 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 33)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rf_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
(* the relay's count, as the walk finds it: |es| in both arms of ra_rel (T = 0 forces es = []) *)
assert (NS0 : val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr W mem (rg_nsrc RG) 4).
{ destruct HREL as [(HT0 & Hes0 & (_ & _ & Hv & Hw & _)) | (_ & _ & Hv & Hw & _)];
  [rewrite Hes0; cbn [length Z.of_nat]; split; [exact Hv | exact Hw] | split; [exact Hv | exact Hw]]. }
assert (IGB : forall a, inG rf_cells a -> 0x10000 <= a /\ a < 0x5fc000).
{ intros a Ha. unfold inG, rf_cells in Ha. apply Exists_exists in Ha. destruct Ha as ((lo, sz) & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) HIG (lo, sz) Hin) as Hbb. unfold in_zr in Hr.
  cbn [fst snd] in Hbb, Hr. lia. }
assert (KC3 : forall a, inG rf_cells a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnl. destruct (HPLAIN a Ha) as (Hi & Ho & He). destruct (IGB a Ha) as (Hb1 & Hb2).
  rewrite (Hfr3 a ltac:(lia) Hnl ltac:(clear -Hb1 Hb2 Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He (PSTC a Ha)). }
zsep_pick HSEPG 3%nat 4%nat DLN.
assert (NS3 : val_mem SEGS (arm W mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 (Z.of_nat (length es)));
  [intros k Hk; apply KC3; [apply (in_rf_cell 2%nat (rg_nsrc RG) 4 (rg_nsrc RG + k) eq_refl); lia | lia]
  | exact (proj1 NS0)]. }
assert (NSB : (length es <= 16)%nat).
{ destruct HREL as [(_ & Hes0 & _) | (_ & _ & _ & _ & _ & _ & Hle & _)]; [rewrite Hes0; cbn [length]; lia | exact Hle]. }
(* the g_nsrc cell as a region: the lw at 0x823ac reads it through the object atom (HV4) *)
pose proof (st_ok_pi_havoc_hi 49 Ea _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (YN3v.havoc Ea 49 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDd : forall m, (m < 49)%nat -> ew Ed m = ew Ea m)
by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E49 : ew Ed 49 = Z_to_bv 64 (Z.of_nat (length es)))
by (rewrite HEd; exact (ew_havoc_new Ea 49 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rf_extra) Ed)
by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEd.
assert (U245d : bv_unsigned (ew Ed (A_OBJ 4)) = rg_nsrc RG)
by (rewrite <- HV4; exact (HEId (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB4 : base_val Ed (Some (A_OBJ 4)) = rg_nsrc RG) by (cbn [base_val]; exact U245d).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb.
cbn [fst snd] in HNSb.
pose proof (st_ok_pi_add_region Ed _ _
  (YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 49 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
        rewrite VB4; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        constructor; [|constructor];
        apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 49 0) (Z.of_nat (length es)));
        [cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        rewrite Z.add_0_r; exact NS3)
  ltac:(cbn [all_disjoint]; exact I)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (SHOKd : sh_ok SEGS Bx rf_SH0 Ed (mrestrict (w_H W) mem3)) by (unfold sh_ok, rf_SH0; constructor).
paj_run_tok_xR RUNG HS HJX3 SHOKd Bspan.
{ apply awr_ok_x_of0. intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
  destruct Hin. }
rfl_cur HS msB.
assert (MEQ0 : forall x, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem3 x) by reflexivity.
rfl_meq MEQ0 MEQ1.
(* the value the blez compares: g_nsrc is |es|, loaded as a signed 4-byte cell *)
assert (HNU : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 49 0))) = Z.of_nat (length es)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 49 0))) with (U Ed (SOff 49 0)).
  rewrite (U_atom Ed 49 (Z.of_nat (length es)) E49 ltac:(lia)). apply sx32_small. lia. }
assert (HNS : bv_signed (sv_denot Ed (SExt true 32 (SOff 49 0))) = Z.of_nat (length es))
by (rewrite bv_signed_small by (rewrite HNU; lia); exact HNU).
assert (HZ0 : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity.
(* the entry registers, read through the env at the two cut points *)
assert (RG0 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ed n = getr regs r)
by (intros n r Hn Hnr; rewrite OLDd, OLDa by lia; exact (EE n r Hnr)).
assert (UH5 : ew Ed 285 = w64 (VAL (A_HI 5)))
by (change 285%nat with (A_HI 5); exact (img_env_atomP Ed (A_HI 5) HEId ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
assert (UH6 : ew Ed 286 = w64 (VAL (A_HI 6)))
by (change 286%nat with (A_HI 6); exact (img_env_atomP Ed (A_HI 6) HEId ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
(* everything the cut points carry from the entry, at any memory the walk sees as mem3 *)
assert (CELLS : forall m, (forall x, mrestrict (w_H W) m x = mrestrict (w_H W) mem3 x) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W m a) /\
  (forall a, inG rf_cells a -> writable_at SEGS (arm W m) a) /\
  rf_saved W m (spZ regs) regs /\ alock_at RG W m true /\ aout_at B RG ly S W m c O mx no cap out /\
  (exists lst, val_mem SEGS (arm W m) GL 4 lst) /\ awr W m GL 4 /\ apres_kept B W mem W m).
{ intros m HM.
  assert (AVm : forall a, aview SEGS (w_H W) m a = aview SEGS (w_H W) mem3 a) by (intros a; apply aview_eq_of; apply HM).
  assert (HMf : mrestrict (w_H W) m = mrestrict (w_H W) mem3) by (apply functional_extensionality; exact HM).
  assert (KM : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W m a).
  { intros a Ha Hn. split.
    - rewrite AVm, (Hfr3 a ltac:(lia) Hn ltac:(unfold ESTACK; lia)). apply K0; lia.
    - intros Hw. unfold arm in *. rewrite HMf. apply (writable_kept (w_H W) (ms_mem ms) mem3 a (Hpres3 a)). exact (WK0 a Hw). }
  assert (RFWm : forall a, inG rf_cells a -> writable_at SEGS (arm W m) a).
  { intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
    apply (hidden_not_img SEGS W). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
  zsep_pick HSEPG 3%nat 8%nat DLG.
  pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as HGLb. cbn [fst snd] in HGLb.
  split; [exact KM|]. split; [exact RFWm|].
  split; [intros k Hk; rewrite HMf; exact (SV3 k Hk)|].
  split.
  { unfold alock_at. split; [|split; [|split]].
    - apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact LK0].
    - unfold arm. rewrite HMf. exact HLK3.
    - apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact LK8].
    - intros j Hj. apply RFWm. apply ILK. lia. }
  split.
  { apply (aout_at_kept B RG ly S W mem ly S W m c O mx no cap out HOUT).
    - pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_max RG, 8) ltac:(left; reflexivity)) as B4.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_nout RG, 8) ltac:(do 1 right; left; reflexivity)) as B5.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_capout RG, 8) ltac:(do 2 right; left; reflexivity)) as B6.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_out RG, 8) ltac:(do 3 right; left; reflexivity)) as B7.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_client_broken RG, 1) ltac:(do 4 right; left; reflexivity)) as B8.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_dead RG, 1) ltac:(do 5 right; left; reflexivity)) as B9.
      pose proof (proj1 (Forall_forall _ _) HIGO (rg_send_eintr RG, 1) ltac:(do 6 right; left; reflexivity)) as B10.
      pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
      cbn [fst snd] in B4, B5, B6, B7, B8, B9, B10, Bc.
      intros r Hr a Har. unfold aout_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Har.
      + zsep_pick HSEPO 0%nat 4%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 5%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 6%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 7%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 2%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 8%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 9%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 10%nat D. apply KM; lia.
      + zsep_pick HSEPO 0%nat 11%nat D.
        assert (Hb : 0x10000 <= a < 0x5fc000).
        { apply pa_img_range. apply (proj1 (HG a (HG2 a ltac:(unfold G_SL, inG; do 5 apply Exists_cons_tl; apply Exists_cons_hd;
            unfold in_zr; cbn [fst snd]; lia)))). }
        apply KM; lia.
      + destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
        pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAOB).
        destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [lia|].
        destruct (alx_blocks _ _ _ LAWS ly S _ W mem md out cap HAR HoIn) as (_ & Ho4096 & Hoceil & _).
        assert (Hrq : req_size cap = cap) by (unfold req_size; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity).
        rewrite Hrq in Hoceil.
        pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md out cap a HAR HoIn ltac:(lia)) as Hni.
        apply KM; [unfold ASAN_CEIL in Hoceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN a (ILK a ltac:(lia)))).
    - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
  split; [destruct HGLv as [lst Hl]; exists lst; apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KM; lia | exact Hl]|].
  split; [intros j Hj; apply RFWm; eapply (in_rf_cell 6%nat _ 4); [reflexivity | lia]|].
  intros a _ _ _ Ha. destruct (Hpres3 a (P0 a Ha)) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  pose proof (HM (Z_to_bv 64 a)) as E1. unfold mrestrict in E1. rewrite Hh in E1. rewrite E1. exact Hb. }
zsep_pick HSEPG 3%nat 5%nat DLS. zsep_pick HSEPG 3%nat 6%nat DLC.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as HSRb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as HCSb.
cbn [fst snd] in HSRb, HCSb.
psrr_branch_tok RUNG BRR HS SHOKd Bspan.
- (* g_nsrc <= 0: no source (es = []), straight to the tail X *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
  apply Bool.negb_true_iff, Z.ltb_ge in Hc.
  assert (Hnil : es = []) by (destruct es as [|e es']; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_to_tok_xR RUNTOG HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0xf8).
  { apply awr_ok_x_of0. intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
    destruct Hin. }
  rfl_cur HS msX. rfl_meq MEQ1 MEQ2.
  destruct (CELLS (ms_mem msX) MEQ2) as (KX & RFWX & SVX & LKX & AOX & GLX & GLWX & APX).
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (9%bv : bv 5) N9.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
  pmkst HS.
  subst es.
  apply (rf_tail_xR regs ly S Hp W mem md T [] c O mx no cap out rest ly S Hp W).
  eexists. exists out.
  split; [exact HJX3|].
  split; [exact (conj (ex_intro _ ch HPRE) (conj HPERM (conj HG1 (conj HG2 HG3))))|].
  split.
  { unfold rf_kept.
    split; [unfold spZ at 1; rewrite N2, (RG0 2%nat 2%bv ltac:(lia) eq_refl), unsigned_lit_small by (unfold spZ in *; lia); unfold spZ; lia|].
    split; [rewrite N3; exact (RG0 3%nat 3%bv ltac:(lia) eq_refl)|].
    split; [rewrite N4; exact (RG0 4%nat 4%bv ltac:(lia) eq_refl)|].
    split; [rewrite N21; exact (RG0 21%nat 21%bv ltac:(lia) eq_refl)|].
    split; [rewrite N22; exact (RG0 22%nat 22%bv ltac:(lia) eq_refl)|].
    split; [rewrite N23; exact (RG0 23%nat 23%bv ltac:(lia) eq_refl)|].
    split; [rewrite N24; exact (RG0 24%nat 24%bv ltac:(lia) eq_refl)|].
    split; [rewrite N25; exact (RG0 25%nat 25%bv ltac:(lia) eq_refl)|].
    split; [rewrite N26; exact (RG0 26%nat 26%bv ltac:(lia) eq_refl)|].
    split; [rewrite N27; exact (RG0 27%nat 27%bv ltac:(lia) eq_refl)|].
    rewrite N9. exact UH5. }
  split; [exact SVX|].
  split.
  { destruct HREL as [(HT0 & _ & (VS0 & WS0 & VN0 & WN0 & VC0 & WC0)) | (VST & WST & VNT & WNT & VCT & WCT & _ & HTin & _)].
    - split; [intros j Hj; apply RFWX; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
      left. split; [exact HT0|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VS0]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VC0]|].
      intros j Hj; apply RFWX; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia].
    - split; [intros j Hj; apply RFWX; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
      right. destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR HTin) as (_ & HT4096 & _).
      split; [lia|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VST]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
      split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KX; lia | exact VCT]|].
      split; [intros j Hj; apply RFWX; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia]|].
      exact HTin. }
  split; [exact LKX|].
  split; [exact AOX|].
  split; [exact HPERM|].
  split; [exact GLX|]. split; [exact GLWX|].
  split; [exact APX|].
  split; [exact (mle_start MT S MLAW)|].
  (* the room round: no source, so nothing was charged: the entry's room is rf_post_x's kr *)
  exact HRMe.
- (* g_nsrc > 0: the loop L from i = 0 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
  apply Bool.negb_false_iff, Z.ltb_lt in Hc.
  destruct HREL as [(_ & Hes0 & _) | HRA]; [rewrite Hes0 in Hc; cbn [length] in Hc; lia|].
  pose proof HRA as (VST & WST & VNT & WNT & VCT & WCT & Hle & HTin & (tail & HTA) & HAOK & HNDF).
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR HTin) as (HT16 & HT4096 & HTceil & _ & _ & _).
  change (req_size ATABLE) with 896 in HTceil.
  paj_run_to_tok_xR RUNTOG HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x7c).
  { apply awr_ok_x_of0. intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia | ]).
    destruct Hin. }
  rfl_cur HS msL. rfl_meq MEQ1 MEQ2.
  destruct (CELLS (ms_mem msL) MEQ2) as (KL & RFWL & SVL & LKL & AOL & GLL & GLWL & APL).
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARL.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
  pmkst HS.
  (* the table's bytes as the loop head finds them *)
  assert (KT : forall x, T <= x < T + 896 -> abyte_kept W mem W (ms_mem msL) x).
  { intros x Hx. pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md T ATABLE x HAR HTin ltac:(change (req_size ATABLE) with 896; lia)) as Hni.
    apply KL; [unfold ASAN_CEIL in HTceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN x (ILK x ltac:(lia)))). }
  assert (KBL : forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n ->
    aview SEGS (w_H W) (ms_mem msL) x = aview SEGS (w_H W) mem x).
  { intros b n x Hin Hx. destruct (alx_blocks _ _ _ LAWS ly S _ W mem md b n HAR Hin) as (_ & Hb4096 & Hbceil & _).
    pose proof (blk_img_x SEGS B ARx LAWS ly S _ W mem md b n x HAR Hin Hx) as Hni.
    apply KL; [unfold ASAN_CEIL in Hbceil; lia|]. intros Hl. apply Hni. exact (proj1 (HPLAIN x (ILK x ltac:(lia)))). }
  assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es).
  { eapply Forall_impl; [|exact HAOK]. intros e (_ & _ & P1 & P2 & _). split; [exact P1 | exact P2]. }
  pose proof HTA as (_ & _ & HTG).
  apply (LOOP (length es) regs ly S Hp W mem md T es c O mx no cap out rest 0%nat ly S Hp W); [lia | exact HCNTe |].
  eexists. exists out, 0.
  split; [exact HJX3|].
  split; [exact (conj (ex_intro _ ch HPRE) (conj HPERM (conj HG1 (conj HG2 HG3))))|].
  split.
  { unfold rf_kept.
    split; [unfold spZ at 1; rewrite N2, (RG0 2%nat 2%bv ltac:(lia) eq_refl), unsigned_lit_small by (unfold spZ in *; lia); unfold spZ; lia|].
    split; [rewrite N3; exact (RG0 3%nat 3%bv ltac:(lia) eq_refl)|].
    split; [rewrite N4; exact (RG0 4%nat 4%bv ltac:(lia) eq_refl)|].
    split; [rewrite N21; exact (RG0 21%nat 21%bv ltac:(lia) eq_refl)|].
    split; [rewrite N22; exact (RG0 22%nat 22%bv ltac:(lia) eq_refl)|].
    split; [rewrite N23; exact (RG0 23%nat 23%bv ltac:(lia) eq_refl)|].
    split; [rewrite N24; exact (RG0 24%nat 24%bv ltac:(lia) eq_refl)|].
    split; [rewrite N25; exact (RG0 25%nat 25%bv ltac:(lia) eq_refl)|].
    split; [rewrite N26; exact (RG0 26%nat 26%bv ltac:(lia) eq_refl)|].
    split; [rewrite N27; exact (RG0 27%nat 27%bv ltac:(lia) eq_refl)|].
    rewrite N9. exact UH5. }
  split; [rewrite N8, OLDd, OLDa, E32 by lia; reflexivity|].
  split; [rewrite N20; exact UH6|].
  split; [rewrite N19; reflexivity|].
  split; [rewrite N18; reflexivity|].
  split; [exact SVL|].
  split; [lia|]. split; [exact Hle|]. split; [lia|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VNT]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 2%nat _ 4); [reflexivity | lia]|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VST]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 3%nat _ 8); [reflexivity | lia]|].
  split; [apply (akept_vm W mem); [intros x Hx; cbn in Hx; apply KL; lia | exact VCT]|].
  split; [intros j Hj; apply RFWL; eapply (in_rf_cell 4%nat _ 4); [reflexivity | lia]|].
  split; [exact HTin|].
  split.
  { intros j Hj.
    assert (HOK : aentry_ok B ly S W mem (nth j es rf_e0)) by (exact (proj1 (Forall_forall _ _) HAOK _ (@nth_In _ j es rf_e0 ltac:(lia)))).
    destruct HOK as (_ & _ & P1 & P2 & _ & _ & _ & _ & _ & BUF & NH & HP & ND1 & ND2 & KS).
    assert (HHE : aheld_ok B ly S W mem (nth j es rf_e0)) by (exact (conj P1 (conj P2 (conj NH (conj HP (conj ND1 (conj ND2 KS))))))).
    pose proof (rf_garr8_entry _ es T tail j HPADS HTG ltac:(lia)) as GJ.
    split; [|split; [|split]].
    - apply (akept_garr8 W mem); [|exact GJ]. intros x Hx. apply KT.
      unfold bzs in Hx. rewrite length_map in Hx. pose proof (rfl_len_entry _ P1 P2) as L. unfold bzs in L. rewrite length_map in L.
      rewrite L in Hx. unfold AENT in Hx. lia.
    - intros q Hq. apply (apresent_writable SEGS).
      destruct (alx_blocks _ _ _ LAWS ly S _ W (ms_mem msL) _ T ATABLE HARL HTin) as (_ & _ & _ & _ & HTp & _).
      change (req_size ATABLE) with 896 in HTp. exact (proj1 (HTp (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
    - apply (rfl_aheld_ok_kept ly S W mem ly S W (ms_mem msL) _ HHE).
      + intros b Hb. unfold gse_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
        * destruct (Z.eqb_spec (re_hp (nth j es rf_e0)) 0) as [Ez | Ez]; [destruct Hb|]. destruct Hb as [<- | []].
          destruct HP as [(Hz & _) | (_ & Hin & _)]; [contradiction | exact Hin].
        * apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in KS. exact (proj1 (KS k Hk)).
      + intros b n x Hb Hx.
        assert (HbI : In (b, n) (ablocks B ly S)).
        { unfold gse_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
          - destruct (Z.eqb_spec (re_hp (nth j es rf_e0)) 0) as [Ez | Ez]; [destruct Hb|]. destruct Hb as [Hb | []].
            injection Hb as <- <-. destruct HP as [(Hz & _) | (_ & Hin & _)]; [contradiction | exact Hin].
          - apply in_map_iff in Hb as (k & Hk1 & Hk). injection Hk1 as <- <-. rewrite Forall_forall in KS. exact (proj1 (KS k Hk)). }
        apply (KBL b n x HbI). unfold req_size. destruct (Z.eqb_spec n 0); lia.
    - destruct BUF as [(Hc0 & Hb0 & _) | (Hc0 & Hin0 & _)]; [left; split; assumption | right; split; assumption]. }
  split; [exact LKL|].
  split; [exact AOL|].
  split; [exact HPERM|].
  split; [exact GLL|]. split; [exact GLWL|].
  assert (ROML : rom_view SEGS W (ms_mem msL)).
  { intros a Ha. pose proof Ha as (sg & Hsg & Hwr & Hr).
    pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hb.
    rewrite (proj1 (KL a ltac:(lia) ltac:(intros Hl; apply (HROMG a ltac:(left; unfold RF_G, inG; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia)); exact Ha))).
    exact (HROM a Ha). }
  split; [exact (rfl_end5_kept W W mem (ms_mem msL) HROM ROML HEND5)|].
  split; [exact ROML|].
  split; [exact APL|].
  split; [exact HROOM|].
  split; [exact (mle_start MT S MLAW)|].
  split; [apply Z.eq_le_incl; reflexivity|].
  split; [exact HMOK|].
  (* the room round: round 0 is owed the whole charge, and the prologue and the lock kept the allocator state *)
  cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]. exact HRMe.
Qed.
End wR.
End c.
(* ---- THE AR STATEMENT, re-derived: pb_relay_finish keeps its statement and its Section hypotheses (a Theorem Labs lane's
   ruling for the plain B names: LAWS : AR_laws, not LX0; the terms and order are Section c's of the AR walk, with
   rf_cells written rf_cells RG GTU GL); it is a corollary of pb_relay_finish_x at ARx := ARi0
   (cgif's AR with the head set empty), PST := [], RP := RP_AR, with LX0 from LAWS by rf_lx_AR_laws_x_ARi0_of above.
   The bridges: W_contract_x.v rf_spec_x_AR0 (the conclusion) and gse_spec_x_of_AR0 (GSE); W_sites_x.v
   alock_realizes_x_of_AR0 / aunlock_realizes_x_of_AR0; W_journal_x.v afree_cf_rule_c_x_of_AR0 /
   afree_null_cf_rule_c_x_of_AR0 and ARi0_hp0 (HP0); W_kit_x.v AR_blkn (BLKN); PSTR / PSTC hold at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
(* the allocator rules' caller-context table (W_journal.v Section hc), rf_spec's last Section variable *)
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
(* the allocator's free rules in their caller-context `_c` forms (kit candidate cand10, W_journal.v
   afree_cf_rule_c / afree_null_cf_rule_c): the free at 0x82408 returns to 0x8240c = relay_finish + 200, and B keeps
   no frame pointer, so its context is the one-entry trace [pc + 200] rf_spec's premise puts in CTX *)
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX.
Hypothesis AFREE0 : afree_null_cf_rule_c SEGS B MT CTX.
Hypothesis GSE : gse_spec B MT MMAX RG (BASE + AF_fr_gestures_end).
(* the placement hypotheses, Section c's (its note says which instruction reads each) *)
Hypothesis HV1 : VAL (A_OBJ 1) = GTU.
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HH5 : VAL (A_HI 5) + (-1672) = rg_nsrc RG.
Hypothesis HH7 : VAL (A_HI 7) + 292 = rg_client RG.
Hypothesis HH8 : VAL (A_HI 8) + 248 = GL.
Hypothesis HIG : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 30), 8);
 (GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (as_errno B, 4)].
Hypothesis HPLAIN : forall a, inG (rf_cells RG GTU GL) a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HWSEG : forall a, inG (rf_cells RG GTU GL) a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis RGAL : rg_lock RG mod 4 = 0.
Hypothesis HIGO : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1)].
Hypothesis HSEPO : zseps
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1); (as_errno B, 4);
 (rg_src RG, 8); (rg_capsrc RG, 4)].
Hypothesis HPLAINO : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HROMG : forall a,
inG (RF_G RG GL) a \/ inG (G_SL B RG) a \/
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ in_rom SEGS a.
Hypothesis HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + Z.of_nat (length END5) -> in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HWSEGE : forall a, as_errno B <= a < as_errno B + 4 ->
wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Theorem pb_relay_finish : rf_spec B MT MMAX G RG GTU GL CTX (BASE + AF_fr_relay_finish).
Proof.
apply rf_spec_x_AR0.
pose proof (rf_lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (alock_realizes_x_of_AR0 B _ ALOCK) as ALOCKX.
pose proof (aunlock_realizes_x_of_AR0 B _ AUNLOCK) as AUNLOCKX.
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE) as AFREEX.
pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE0) as AFREE0X.
pose proof (gse_spec_x_of_AR0 B MT MMAX RG _ GSE) as GSEX.
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
assert (PSTC : forall a, inG (rf_cells RG GTU GL) a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
eapply (pb_relay_finish_x B [] (ARi0 SEGS B) MT RP_AR MMAX G RG GTU GL CTX); eassumption.
Qed.
End cAR.
End b.
End a.
(* ---- The placement facts of the walk at the pinned placement PB_fr (lib/B/W_img.v), the allocator symbols
   YD2l.TfibB and the B globals fr_globals_b (lib/B/W_rep.v), in the form of W_next_line.v pb_next_line_fr and
   W_check_no_loss.v cnl_objs_apart_fr: GTU is g_thread_up's object (VAL (A_OBJ 1) = nm 0x5d8ce0), GL is g_listen
   (VAL (A_HI 8) + 248 = nm 0xa2540, the store at 0x8244c).  Each fact is decided by computation against the
   listing's objects, the image's segments (AsanUbsan) and the generated tables of lib/B/YF0m.v (TfibSyms):
   HV1 .. HH8 by vm_compute; HIG / HIGO / HSEPG / HSEPO by the numbers; HPLAIN / HPLAINO in the RW LOAD
   0x9fc60 .. 0x5fb2d0 and outside Tfib_owned_static; HWSEG / HWSEGE by wview at each byte; HROMG because the image's
   read-only segments end below 0x9d000; HE5R in segment 000.  HROMO stays a hypothesis of pb_relay_finish_fr, as in
   lib/B/W_asm.v (I_HROMO, generic sink class): its last clause names the sink class's ofl_head.  At the image-B sink
   class it is discharged below (rf_HROMO_tfib, from lib/B/YF0mFacts.v tfib_rom_owned_pinned), and
   pb_relay_finish_fr_tfib states the walk without it. ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tbl W_img YF0m YF0mFacts YD2l.
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing W_img.PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing W_img.PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing W_img.PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing W_img.PB_fr A_TEXT).
#[local] Notation TB := YD2l.TfibB.
#[local] Notation RG := fr_globals_b.
Lemma rf_rg_fr : rg_lock RG = 0x5d9040 /\ rg_nsrc RG = 0x5d8d20 /\ rg_src RG = 0x5d8d40 /\
  rg_capsrc RG = 0x5d8d80 /\ rg_client RG = 0xa2560 /\ rg_send_max RG = 0x5d8dc0 /\
  rg_nout RG = 0x5d8e40 /\ rg_capout RG = 0x5d90a0 /\ rg_out RG = 0x5d90c0 /\
  rg_client_broken RG = 0x5d8d60 /\ rg_send_dead RG = 0x5d8e00 /\ rg_send_eintr RG = 0x5d8e20.
Proof. repeat (split; [reflexivity|]); reflexivity. Qed.
Lemma rf_GTU_fr : VAL (A_OBJ 1) = 0x5d8ce0. Proof. vm_compute. reflexivity. Qed.
Lemma rf_GL_fr : VAL (A_HI 8) + 248 = 0xa2540. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HV3_fr : VAL (A_OBJ 3) = rg_lock RG. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HV4_fr : VAL (A_OBJ 4) = rg_nsrc RG. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HV5_fr : VAL (A_OBJ 5) = rg_src RG. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HH5_fr : VAL (A_HI 5) + (-1672) = rg_nsrc RG. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HH7_fr : VAL (A_HI 7) + 292 = rg_client RG. Proof. vm_compute. reflexivity. Qed.
Lemma rf_RGAL_fr : rg_lock RG mod 4 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma rf_HIG_fr : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(VAL (A_OBJ 1), 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4);
 (VAL (A_HI 8) + 248, 4)].
Proof.
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & _). rewrite E1, E2, E3, E4, E5, rf_GTU_fr, rf_GL_fr.
repeat constructor; cbn [fst snd]; lia.
Qed.
Lemma rf_HIGO_fr : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1)].
Proof.
destruct rf_rg_fr as (_ & _ & _ & _ & _ & E6 & E7 & E8 & E9 & E10 & E11 & E12). rewrite E6, E7, E8, E9, E10, E11, E12.
repeat constructor; cbn [fst snd]; lia.
Qed.
(* the writable segment of image B (the RW LOAD 0x9fc60 .. 0x5fb2d0) *)
Lemma rf_rw_img_fr : forall a, 0x9fc60 <= a < 0x5fb2d0 -> in_img SEGS a.
Proof.
intros a Ha. unfold in_img. eexists. split; [do 3 right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma rf_wseg_fr : forall lo (n : nat),
(forall k, (k < n)%nat -> wview SEGS (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat k)) <> None) ->
forall a, lo <= a < lo + Z.of_nat n -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Proof.
intros lo n H a Ha. replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia. apply H. lia.
Qed.
Lemma rf_ws_lem_fr : forall lo n,
forallb (fun k => match wview SEGS (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat k)) with Some _ => true | None => false end)
  (seq 0 n) = true ->
forall k, (k < n)%nat -> wview SEGS (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat k)) <> None.
Proof.
intros lo n H k Hk. rewrite forallb_forall in H. specialize (H k (proj2 (in_seq n 0 k) ltac:(lia))).
destruct (wview SEGS (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat k))); [discriminate | discriminate H].
Qed.
Ltac rf_ws_fr := apply rf_ws_lem_fr; vm_compute; reflexivity.
Ltac rf_noown_fr := let r := fresh "r" in let Hr := fresh "Hr" in let Hz := fresh "Hz" in
  rewrite Exists_exists; intros (r & Hr & Hz); cbn [YF0m.Tfib_owned_static In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia | ]); destruct Hr.
Lemma rf_HSEPG_fr : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 30), 8);
 (VAL (A_OBJ 1), 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4);
 (VAL (A_HI 8) + 248, 4); (as_errno TB, 4)].
Proof.
assert (E0 : VAL (A_OBJ 0) = 0x9df50) by (vm_compute; reflexivity).
assert (E30 : VAL (A_OBJ 30) = 0xa6638) by (vm_compute; reflexivity).
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & _).
rewrite E0, E30, E1, E2, E3, E4, E5, rf_GTU_fr, rf_GL_fr, (YF0m.ts_errno TB YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO.
cbn [zseps zseps_from fst snd]. repeat split; lia.
Qed.
Lemma rf_HSEPO_fr : zseps
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_client RG, 4); (VAL (A_HI 8) + 248, 4);
 (rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1); (as_errno TB, 4);
 (rg_src RG, 8); (rg_capsrc RG, 4)].
Proof.
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, rf_GL_fr, (YF0m.ts_errno TB YD2l.TfibB_syms).
unfold YF0m.TFIB_ERRNO. cbn [zseps zseps_from fst snd]. repeat split; lia.
Qed.
Lemma rf_HPLAIN_fr : forall a, inG (rf_cells RG (VAL (A_OBJ 1)) (VAL (A_HI 8) + 248)) a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
intros a Ha. rewrite (YF0m.ts_owned TB YD2l.TfibB_syms), (YF0m.ts_errno TB YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO.
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & _).
unfold inG, rf_cells in Ha. rewrite E1, E2, E3, E4, E5, rf_GTU_fr, rf_GL_fr in Ha.
apply Exists_exists in Ha as ((lo & n) & Hin & Hr). unfold in_zr in Hr. cbn [fst snd] in Hr.
cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; split; [apply rf_rw_img_fr; lia | split; [rf_noown_fr | lia]] | ]).
destruct Hin.
Qed.
Lemma rf_HPLAINO_fr : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
intros a Ha. rewrite (YF0m.ts_owned TB YD2l.TfibB_syms), (YF0m.ts_errno TB YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO.
destruct rf_rg_fr as (_ & _ & _ & _ & _ & E6 & _ & _ & _ & _ & E11 & _). rewrite E6, E11 in Ha.
split; [apply rf_rw_img_fr; lia | split; [rf_noown_fr | lia]].
Qed.
Lemma rf_HWSEG_fr : forall a, inG (rf_cells RG (VAL (A_OBJ 1)) (VAL (A_HI 8) + 248)) a ->
wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & _).
unfold inG, rf_cells in Ha. rewrite E1, E2, E3, E4, E5, rf_GTU_fr, rf_GL_fr in Ha.
apply Exists_exists in Ha as ((lo & n) & Hin & Hr). unfold in_zr in Hr. cbn [fst snd] in Hr.
cbn [In] in Hin.
destruct Hin as [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | []]]]]]]]; injection Hin as <- <-.
- apply (rf_wseg_fr 0x5d8ce0 1); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0x5d9040 12); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0x5d8d20 4); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0x5d8d40 8); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0x5d8d80 4); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0xa2560 4); [rf_ws_fr | cbn; lia].
- apply (rf_wseg_fr 0xa2540 4); [rf_ws_fr | cbn; lia].
Qed.
Lemma rf_HWSEGE_fr : forall a, as_errno TB <= a < as_errno TB + 4 -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. rewrite (YF0m.ts_errno TB YD2l.TfibB_syms) in Ha. unfold YF0m.TFIB_ERRNO in Ha.
apply (rf_wseg_fr 0x5d994c 4); [rf_ws_fr | cbn; lia].
Qed.
(* the image's read-only segments (000 r--, 001 r-x) end below 0x9d000 *)
Lemma rf_rom_lo_fr : forall a, in_rom SEGS a -> a < 0x9d000.
Proof.
intros a (sg & Hsg & Hw & Hr). change (@pa_segs _ fr_prog_listing W_img.PB_fr) with W_tbl.frsegs in Hsg.
unfold W_tbl.frsegs, AsanUbsan.M.loaded_segments in Hsg. cbn in Hsg.
destruct Hsg as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw, Hr; first [discriminate | lia].
Qed.
Lemma rf_HROMG_fr : forall a,
inG (RF_G RG (VAL (A_HI 8) + 248)) a \/ inG (G_SL TB RG) a \/
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ in_rom SEGS a.
Proof.
intros a Ha Hr. pose proof (rf_rom_lo_fr a Hr) as Hlo.
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
unfold RF_G, G_SL, inG in Ha.
rewrite E1, E2, E5, E6, E7, E8, E9, E10, E11, E12, rf_GL_fr, (YF0m.ts_errno TB YD2l.TfibB_syms) in Ha.
unfold YF0m.TFIB_ERRNO in Ha.
destruct Ha as [Ha | [Ha | Ha]]; [apply Exists_exists in Ha as ((lo & n) & Hin & Hz) | apply Exists_exists in Ha as ((lo & n) & Hin & Hz) |];
[cbn [In] in Hin; unfold in_zr in Hz; cbn [fst snd] in Hz;
 repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia | ]); destruct Hin
| cbn [In] in Hin; unfold in_zr in Hz; cbn [fst snd] in Hz;
 repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia | ]); destruct Hin
| lia].
Qed.
Lemma rf_HE5R_fr : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + Z.of_nat (length END5) -> in_rom SEGS a.
Proof.
intros a Ha. assert (E28 : VAL A_lit_end5 = 0x20f00) by (vm_compute; reflexivity).
rewrite E28 in Ha. cbn [length END5 map Z.of_nat] in Ha.
exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
(* pb_relay_finish at PB_fr / TfibB / fr_globals_b, GTU = g_thread_up, GL = g_listen, with the placement hypotheses
   discharged: LAWS, TL, MLAW, ALOCK, AUNLOCK, AFREE, AFREE0, GSE and HROMO remain, and G at gx_ok *)
Theorem pb_relay_finish_fr : forall (MT : ameter_ops) (MMAX : Z) (CTX : list (list Z)),
AR_laws SEGS TB -> PALib (PI := W_img.PB_fr) TB -> ameter_laws MT ->
alock_realizes (PI := W_img.PB_fr) TB (SIGMA WS_pthread_mutex_lock) ->
aunlock_realizes (PI := W_img.PB_fr) TB (SIGMA WS_pthread_mutex_unlock) ->
afree_cf_rule_c SEGS TB MT CTX -> afree_null_cf_rule_c SEGS TB MT CTX ->
gse_spec (PI := W_img.PB_fr) TB MT MMAX RG (BASE + AF_fr_gestures_end) ->
rom_out SEGS TB (G_SL TB RG) ->
forall G, gx_ok SEGS TB G ->
rf_spec (PI := W_img.PB_fr) TB MT MMAX G RG (VAL (A_OBJ 1)) (VAL (A_HI 8) + 248) CTX (BASE + AF_fr_relay_finish).
Proof.
intros MT MMAX CTX LAWS TL MLAW ALOCK AUNLOCK AFREE AFREE0 GSE HROMO G HG.
pose proof rf_HV3_fr as HV3. pose proof rf_HV4_fr as HV4. pose proof rf_HV5_fr as HV5.
pose proof rf_HH5_fr as HH5. pose proof rf_HH7_fr as HH7. pose proof rf_RGAL_fr as RGAL.
pose proof rf_HIG_fr as HIG. pose proof rf_HIGO_fr as HIGO. pose proof rf_HSEPG_fr as HSEPG. pose proof rf_HSEPO_fr as HSEPO.
pose proof rf_HPLAIN_fr as HPLAIN. pose proof rf_HPLAINO_fr as HPLAINO. pose proof rf_HWSEG_fr as HWSEG.
pose proof rf_HWSEGE_fr as HWSEGE. pose proof rf_HROMG_fr as HROMG. pose proof rf_HE5R_fr as HE5R.
apply (pb_relay_finish (PI := W_img.PB_fr) TB MT MMAX G RG (VAL (A_OBJ 1)) (VAL (A_HI 8) + 248) CTX).
all: first [assumption | reflexivity].
Qed.
(* the byte a literal cell states, YF0mFacts.v's form (Z.land of the shifted literal) = le_byte's *)
Lemma rf_le_byte_land : forall v (w k : nat), (k < w)%nat -> le_byte v w k = Z.land (Z.shiftr v (8 * Z.of_nat k)) 255.
Proof.
intros v w k Hk. unfold le_byte. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change 256 with (2 ^ 8).
apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 8) as [Hn8 | Hn8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* an owned read-only byte of image B is pinned (rom_pinned), from lib/B/YF0mFacts.v tfib_rom_owned_pinned *)
Lemma rf_rom_pinned_tfib : forall a, in_rom SEGS a -> Exists (in_zr a) (as_owned_static TB) -> rom_pinned SEGS TB a.
Proof.
intros a Hr Ho ly. rewrite (YF0m.ts_owned TB YD2l.TfibB_syms) in Ho.
destruct (YF0mFacts.tfib_rom_owned_pinned a Hr Ho) as (c & Hc & Hne & Heq).
destruct c as [cat cw cv].
unfold YF0mFacts.tfib_cell_byte, YF0mFacts.tfib_cell_lit in Hne, Heq. cbn [c_at c_w c_val] in Hne, Heq.
destruct cat as [z| | | | | | | | | | | | | | | | | | ]; try (exfalso; apply Hne; reflexivity).
destruct cv as [e|]; try (exfalso; apply Hne; reflexivity).
destruct e as [v| | | | | | | | | | | | | | | | | | ]; try (exfalso; apply Hne; reflexivity).
cbv beta iota zeta in Hne, Heq.
lazymatch type of Heq with context [if ?b then _ else _] => destruct b eqn:Er end; [|exfalso; apply Hne; reflexivity].
apply andb_prop in Er as [Er1 Er2]. apply Z.leb_le in Er1. apply Z.ltb_lt in Er2.
exists (ACell (ANum z) cw (AV (ANum v))), (ANum v). rewrite (YF0m.ts_const TB YD2l.TfibB_syms).
split; [unfold YF0m.Tfib_const; apply in_or_app; right; apply in_or_app; left; exact Hc|].
split; [reflexivity|]. cbn [aeval c_at c_w]. split; [lia|].
rewrite rf_le_byte_land by lia. rewrite Z2Nat.id by lia. exact Heq.
Qed.
End fr.
(* HROMO at the image-B sink class (YE2k.tfib_sink_head, ofl_head 0x5fa0e8), and the walk without it *)
Section frt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing W_img.PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing W_img.PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing W_img.PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing W_img.PB_fr A_TEXT).
#[local] Notation TB := YD2l.TfibB.
#[local] Notation RG := fr_globals_b.
Lemma rf_HROMO_tfib : rom_out (SK := YE2k.tfib_sink_head) SEGS TB (G_SL TB RG).
Proof.
intros a Ha. pose proof (rf_rom_lo_fr a Ha) as Hlo.
destruct rf_rg_fr as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
split; [|split; [|split]].
- unfold G_SL, inG. rewrite E7, E8, E9, E10, E12, (YF0m.ts_errno TB YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO.
  intros Hg. apply Exists_exists in Hg as ((lo & n) & Hin & Hz). cbn [In] in Hin. unfold in_zr in Hz. cbn [fst snd] in Hz.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia | ]); destruct Hin.
- exact (rf_rom_pinned_tfib a Ha).
- rewrite (YF0m.ts_errno TB YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO. lia.
- lazymatch goal with |- ~ (?h <= a < ?h + 8) =>
    assert (Eh : h = 0x5fa0e8) by (vm_compute; reflexivity); rewrite Eh; lia end.
Qed.
Theorem pb_relay_finish_fr_tfib : forall (MT : ameter_ops) (MMAX : Z) (CTX : list (list Z)),
AR_laws SEGS TB -> PALib (PI := W_img.PB_fr) TB -> ameter_laws MT ->
alock_realizes (PI := W_img.PB_fr) TB (SIGMA WS_pthread_mutex_lock) ->
aunlock_realizes (PI := W_img.PB_fr) TB (SIGMA WS_pthread_mutex_unlock) ->
afree_cf_rule_c (SK := YE2k.tfib_sink_head) SEGS TB MT CTX ->
afree_null_cf_rule_c (SK := YE2k.tfib_sink_head) SEGS TB MT CTX ->
gse_spec (SK := YE2k.tfib_sink_head) (PI := W_img.PB_fr) TB MT MMAX RG (BASE + AF_fr_gestures_end) ->
forall G, gx_ok SEGS TB G ->
rf_spec (SK := YE2k.tfib_sink_head) (PI := W_img.PB_fr) TB MT MMAX G RG (VAL (A_OBJ 1)) (VAL (A_HI 8) + 248) CTX
  (BASE + AF_fr_relay_finish).
Proof.
intros MT MMAX CTX LAWS TL MLAW ALOCK AUNLOCK AFREE AFREE0 GSE G HG.
exact (pb_relay_finish_fr (SK := YE2k.tfib_sink_head) MT MMAX CTX LAWS TL MLAW ALOCK AUNLOCK AFREE AFREE0 GSE rf_HROMO_tfib G HG).
Qed.
End frt.
