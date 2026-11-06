(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of plugin-hostd's relay_finish, in the form of the cgif fake-frame
   walks of proofs/cgif/cgif_file_fuzzer/lib/A/ACk1.v (prologue, stack_malloc, exit), lib/A/AC8h.v (call sites) and
   lib/A/ACfj.v:157-163 (a loop closed by induction on its trip count). *)
(* Modified by Theorem Labs, 2026-10: lane W5 relay_finish_h (a Theorem Labs lane): started from W_relay_finish.v's text at
   a working branch 273def0a61d, which stops after the pthread_mutex_lock call; this file walks the rest. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), row C1 of
   a Theorem Labs lane's pool (a Theorem Labs lane): the walk is pb_relay_finish_h_x, stated over any allocator relation ARx with its laws
   (W_contract_x.v rf_spec_x; Section c below, the AR Section's hypotheses as their twins plus PST / ARx / hl / LAWS /
   HP0 and the frame twins' hypotheses of W_frame_x.v); pb_relay_finish_h keeps its statement, byte-identical,
   re-derived from pb_relay_finish_h_x at ARx := ARi0, PST := [] (W_contract_x.v rf_spec_x_AR0; Section cAR, which
   takes LX0 in place of LAWS). *)
(* Modified by Theorem Labs, 2026-10: the room round (ROOM-TEXTS.md v3 (sha256 767baa12f13c; internal record)): the walk
   takes RP and threads rf_spec_x's rp_RM budget (each round: the free's 1, then gestures_end's charge) and its
   cnt_ok_pk count premise to the free and to gestures_end; the fake frame's seat and release keep the room by roomp's
   law rp_RPF; the seat is W_frame_x.v's aj_stack_malloc_pres_at_raw_x, whose post states S2 = set_fs f Sc. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_frame W_sites W_rebase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH YC80xR.
(* the room round's count names (acnt and its list lemmas): lib/A/ReplyCnt.v, the one definition; Required, not
   Imported, and named qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Two cells of a zseps list (W_frame.v) are apart, picked by index: never tauto / lia over the whole list, whose
   disjunctions make both exponential. *)
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
(* An atom above a havoc's window keeps its value (the fake frame's atoms 512 and 513 outlive every later call's
   havoc of the caller-saved atoms). *)
Lemma ew_havoc_above : forall E k ws i, (k + length ws <= i)%nat -> ew (YN3v.havoc E k ws) i = ew E i.
Proof.
intros E k ws i Hi. unfold YN3v.havoc. cbn [ew].
destruct (i <? k)%nat eqn:Hlt; [reflexivity|]. apply nth_overflow. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* The spec rf_spec / rf_spec_g and its parts (RF_STK, rf_FP, rf_run, rf_cost, rf_room, rf_post, RF_G) are published
   in W_contract.v Section w5f (W5Relay's push 80298a7d491, this lane's text). *)

(* ---- THE WALK. ---- *)
Definition A_relay_finish : Z := AF_fr_relay_finish.
Definition A_relay_finishP : Z := BASE + A_relay_finish.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): relay_finish over any allocator relation ARx
   with its laws, stated as W_contract_x.rf_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS
   (the generic relation); HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: W_journal_x's
   range_addressable_of_block_hp0_x); the frame twins' hypotheses of W_frame_x.v in place of ML / SMP: IMGC
   (frm_off_imgP_x), OWNLOW / WFx / WFL / SMALLOC (aj_stack_malloc_pres_at_raw_x), WFx / WFL / SFREE
   (aj_flag_store_pi_x); and three facts on the program statics PST (PSTR / PSTC / PSTO below). ---- *)
Section c.
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
(* the allocator rules' caller-context table (W_journal.v Section hc), rf_spec's last Section variable *)
Variable CTX : list (list Z).
Context {hl : Z}.
(* ---- WHICH GOAL DEMANDS EACH SECTION HYPOTHESIS (a Theorem Labs lane's rule, 2026-10-29; the next porter reads this) ----
   Every PLACEMENT hypothesis below was decided TRUE at the pinned instance - PI = PB_fr, RG = fr_globals,
   B = AF0m's TfibSyms B (tables from AF0m.v (sha256 3845e3de2622; internal record)), SK =
   AE2k.tfib_sink_head, GTU = 0x5d8760, GL = 0xa1fc0 - each in Rocq with Qed, by the measurement lane
   with build rc=0, its build log (sha256 c6d2ed4e375b; internal record).
   - LAWS TL TLF ML MLAW SMP ASM0 ASF FFL HG: the instance's and the fake frame's laws; every run and every call.
     In this generic Section ML / SMP give way to IMGC OWNLOW WFx WFL SFREE SMALLOC (W_frame_x.v), and HP0 joins.
   - ALOCK, AUNLOCK: the two mutex entries (0x82438, 0x824b4), through aj_gx_entry_at.
   - AFREE, AFREE0: free (s->buf) in a round (0x82470), the non-null and the null case - the `_c` forms (W_journal.v
     Section hc), whose caller-context premise `In (raZ regsT :: spine ch) CTX` is rf_spec's own premise at the
     chain the round builds ((sp0, ra, s0) pushed on the entry's, so its spine is the entry's ra then the caller's).
   - GSE: the internal call to gestures_end (0x82480).
   - MO_FR: the fake frame's seat and release cost the meter nothing - rf_post's mo_le, in both segments.
   - HV3: the g_thread_up test at 0x823e4 (PLdHi through A_OBJ 3).
   - HV6: a0 = &g_lock at 0x82434 and 0x824b0 (PAddHi through A_OBJ 6).
   - HV7: the g_nsrc loads at 0x82440 and 0x82484 (PLdHi through A_OBJ 7).
   - HV8: the g_src loads at 0x82454 and 0x82474 (PLdHi through A_OBJ 8).
   - HH9: the g_nsrc STORE at 0x82494 goes through the kept auipc register s6, so its region is based on A_HI 9.
   - HH11, HH12: the same for the g_client store at 0x824a0 and the g_listen store at 0x824a8.
   - HIG, HSEPG: the cells the walk reads or writes lie in the image band and are pairwise apart - every region_ok
     and every pairwise_disjoint of a symbolic state, and every transport of a cell across a call.
   - HPLAIN: those cells are plain image bytes - the image clause of acall_kept and of the journal, which is how
     each cell's value crosses the prologue, the fake-frame entry and the two mutex calls.
   - HWSEG: those cells are writable in every memory - alock_at's awr and the three stores' region_ok.
   - RGAL: musl's mutex needs g_lock 4-aligned - ALOCK's and AUNLOCK's premise.
   - HIGO, HSEPO: aout_at names seven cells this function never mentions; the tail's three stores must not move
     them and the loop must carry them - aout_at_kept, in rf_post and in RFI.
   - HPLAINO: g_send_max and g_send_dead are in neither rf_cells nor G_SL, so only this makes them plain image
     bytes - aout_at's carry across the free (acall_kept's image clause).
   - HROMG: no cell this walk writes is read-only, so rom_view survives the three stores and the unlock - the
     rom_view RFI carries, which gse_spec demands.
   - HE5R: the "end5" literal is read-only, so rom_view carries its five bytes - gse_spec's garr8 premise in RFI.
   - HROMO: rom_out at G_SL in the corrected text of a Theorem Labs lane's 45a3cc9bdd0 - ajournal_gx_rom_view across
     gestures_end, and its last clauses for acall_kept_rom_view across the free.
   - HWSEGE: errno is writable in every memory - aout_at's awr at errno after the free, which the free's
     view-only errno clause does not give.
   - (none) the errno carry across the fake-frame seat is NOT a hypothesis: it comes from the root lemma
     aj_stack_malloc_pres_at_raw and errno_not_aowned (W5's 5d3fbcd7529); see the history note before
     rf_writable_of_seg for the false stopgap and the proved lemma that preceded it.
   NO gx_rt: the note at HG says why taking it would make every goal of this walk closable. *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x); the owned-low law OWNLOW, the
   model invariant WFx with its law WFL, and the two facts the twins read off model_laws / stack_malloc_progressP
   (SFREE, SMALLOC) - at ARi0 all from the AR Section's ML / SMP (W_frame_x.v Section br, YG0s.AR_owned_low_law_ok) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
(* a live block's size is non-negative (W_kit_x.v's BLKN: AR_blocks_law's last conjunct, which AR_laws_x's
   alx_blocks does not state) *)
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASM0 : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B G.
(* NO gx_rt HERE.  The paused walk W_relay_finish.v:80 took `Hypothesis HGRT : gx_rt B G`, which says no byte of G
   is errno (W_contract.v:505); rf_spec's own premise says G_SL B RG is inside G, and G_SL holds (as_errno B, 4)
   (W_contract.v:775).  The two together are contradictory, so with HGRT every goal of this walk closes vacuously.
   Nothing here needs gx_rt, so it is dropped (a Theorem Labs lane 2026-10-29, after a Theorem Labs lane refused to write
   the vacuous proof).  A Theorem Labs lane's ruling (2026-10-29 09:2xZ): neither gx_rt nor G_SL changes - a _g form is
   sound only when its G provably EXCLUDES errno - so W_contract.v's re_spec_g and rf_spec_g are being DELETED,
   while ra_spec_g stands (ra_spec has no G_SL premise and RA_G excludes errno by construction).  Consumers take
   rf_spec at the concrete G, as this file's top does.  The same clash was found in five other files of this unit
   (_exit.v, _write.v, W_xends.v, W_xreset.v, W_xrf.v), so W8 now greps its build for it. *)
(* the runtime entries relay_finish calls, and the allocator's free rules on the live-state instance - in their
   caller-context `_c` forms, the WEAKER ones (afree_cf_rule_c_weak, afree_null_cf_rule_c_weak): the instance proves
   these, and any caller holding the forms without the premise can still supply them *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREE0 : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* the internal callee, W4's published statement (W_contract_x.v's twin) *)
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* the meter does not charge the fake frame's seat and release (both are set_fs steps: the seat's post states
   s' = set_fs f s, and YG01.v's stack_free_state is a set_fs) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the placement of the globals relay_finish reads and writes: by the object the listing names, and - for a store
   through a kept auipc register - by the hi slot and the store's immediate (W_rebase.v). *)
Hypothesis HV3 : VAL (A_OBJ 3) = GTU.
Hypothesis HV6 : VAL (A_OBJ 6) = rg_lock RG.
Hypothesis HV7 : VAL (A_OBJ 7) = rg_nsrc RG.
Hypothesis HV8 : VAL (A_OBJ 8) = rg_src RG.
Hypothesis HH9 : VAL (A_HI 9) + 868 = rg_nsrc RG.
Hypothesis HH11 : VAL (A_HI 11) + (-1208) = rg_client RG.
Hypothesis HH12 : VAL (A_HI 12) + (-1252) = GL.
(* the cells are in the image band and pairwise apart (the pinned placement decides both by vm_compute) *)
Hypothesis HIG : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fb000)
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 1), 8); (VAL (A_OBJ 32), 8); (as_uar_cell B, 4);
 (GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (as_errno B, 4)].
(* The cells are plain image bytes, as the plain contract asks (Prog/relay_finish_b_c.v:79-82 img_plain): that is
   what carries their values across a call, by acall_kept's image clause and the journal's. *)
Definition rf_cells : list (Z * Z) :=
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HPLAIN : forall a, inG rf_cells a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ... and bytes of writable image segments (the mutex and the program's stores need them writable in every memory),
   g_lock 4-aligned (musl's mutex); both decided on the pinned image *)
Hypothesis HWSEG : forall a, inG rf_cells a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis RGAL : rg_lock RG mod 4 = 0.
(* The output globals of W_rep.v's aout_at that relay_finish does not name: they must be apart from the four cells
   it writes, or its three stores would move them, and in the image band.  W_relay_event.v takes the same two facts
   for the same reason (its HAOD and HAO3); the pinned placement decides both by vm_compute.  (Added by
   a Theorem Labs lane 2026-10-29 after the tail's walk showed HSEPG and HIG cover none of these seven cells.) *)
Hypothesis HIGO : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fb000)
[(rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1)].
Hypothesis HSEPO : zseps
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1); (as_errno B, 4);
 (rg_src RG, 8); (rg_capsrc RG, 4)].
(* g_send_max and g_send_dead are the two cells of aout_at that are in neither rf_cells nor G_SL: the callees' image
   clause needs them to be plain image bytes, as HPLAIN says of relay_finish's own cells. *)
Hypothesis HPLAINO : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* No cell any step of this walk writes is a read-only image byte, so the walk's rom_view survives each of them
   (W_relay_event.v takes HLRW for the lock alone, for the same reason). *)
Hypothesis HROMG : forall a,
inG (RF_G RG GL) a \/ inG (G_SL B RG) a \/
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ in_rom SEGS a.
(* ... and the "end5" literal gestures_end sends is a read-only image byte, so rom_view carries its five bytes
   across every call of a round. *)
Hypothesis HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + Z.of_nat (length END5) -> in_rom SEGS a.
(* NO "read-only bytes are not allocator statics" HERE: it is false on image A (408 owned-static bytes lie inside the
   read-only LOADs, a Theorem Labs lane 2026-10-29 08:46Z).  A rom_view carry across an allocator call goes through
   W_journal.v's acall_kept_rom_view / rom_pinned (a Theorem Labs lane's 45a3cc9bdd0, cherry-picked onto this branch). *)
(* rom_out at G_SL, in the corrected text of a Theorem Labs lane's 45a3cc9bdd0: no read-only byte is a cell gestures_end may
   write, an owned static inside a read-only LOAD is pinned to its image value by AR's const table (rom_pinned), and
   no read-only byte is errno or the sink's overflow head.  It carries rom_view across gestures_end
   (ajournal_gx_rom_view), and its last three conjuncts are what acall_kept_rom_view needs across the free. *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
(* errno's four bytes are bytes of a writable image segment, as HWSEG says of relay_finish's own cells: the
   allocator's free keeps errno's VIEW (afree_cf_rule's errno clause) but not its presence, and a kept view alone
   does not keep a byte writable, which aout_at's `awr W mem (as_errno B) 4` needs after a free. *)
Hypothesis HWSEGE : forall a, as_errno B <= a < as_errno B + 4 ->
wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x and the rom_view carry of the prologue), no byte of
   rf_cells, no byte of aout_at's cells.  At PST := [] all three hold trivially (W_gse_loop.v's PSTR, a Theorem Labs lane). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTC : forall a, inG rf_cells a -> ~ Exists (in_zr a) PST.
Hypothesis PSTO : forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8)
   \/ (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8)
   \/ (rg_client RG <= a < rg_client RG + 4)
   \/ (rg_client_broken RG <= a < rg_client_broken RG + 1)
   \/ (rg_send_dead RG <= a < rg_send_dead RG + 1)
   \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) -> ~ Exists (in_zr a) PST.
(* THE ERRNO CARRY ACROSS THE FAKE-FRAME SEAT - history, so a reader sees why this file once carried a hypothesis
   or a lemma here and now carries neither:
   - 08:5xZ-10:0xZ `Hypothesis ASMERR`: FALSE AS STATED (a Theorem Labs lane 09:56Z,
     its note Q3-stack-malloc-errno.md (sha256 003dd031be9c; internal record)).  It quantified over every
     `acall_kept ... (fun _ => False)`, which says nothing about errno: two memories differing only at errno, with no
     blocks, no frames and slo = shi, satisfy its premise and break its conclusion.  No proof used it.
   - 10:0xZ-11:1xZ `Lemma ASMX` (a Theorem Labs lane, Qed, Rocq primitives only): aj_stack_malloc_pres_at's proof
     copied at cid 0, plus a QUANTIFIED keep clause (image bytes that are not owned-static), proved from ASM0's frame
     clause with only the law al_owned_image and segs_low - so no instance fact was needed in the lemma; the caller
     supplied "errno is not owned-static" from gx_ok on G_SL.
   - from 11:1xZ: the ROOT carries it.  W5's working branch 5d3fbcd7529 (cherry-picked here, W_frame.v only)
     adds `aj_stack_malloc_pres_at_raw` - today's post plus the RAW frame clause (every byte that is neither aowned
     before nor after the call nor scratch keeps its view) - and `errno_not_aowned`.  The walk calls the raw lemma at
     the seat and takes errno's view from its raw clause with errno_not_aowned at both states, the owned-static fact
     for errno coming from HG (gx_ok SEGS B G) at errno, which is in G_SL and so in G.
   Corroborated by three hands from three directions (this prologue; W7's DropWhole, `HERRW`; a Theorem Labs lane's free,
   `free_leaf_cf_pres`): one root gap, now closed at the root. *)
(* W6's lemma (W_relay_instance_gone.v:73): a byte the loaded image holds writable is writable in every memory that
   does not hide it *)
Lemma rf_writable_of_seg : forall (H : word -> bool) (m : word -> option byte) a,
H (Z_to_bv 64 a) = false -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a Hh Hw. unfold writable_at, mrestrict, wview in *. rewrite Hh.
destruct (m (Z_to_bv 64 a)) as [b|]; [cbv iota; discriminate | exact Hw].
Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the plain token runner on the donor journal ajournal_x (W_kit.v:98 paj_run's text over YC80x.v) *)
Let RUN0 := SRr_run_pi_tok_AJx (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr).
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 ([] : list (Z * Z)).
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 ([] : list (Z * Z)).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS. Let RUNTOP := SRr_run_to_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Let RUNF := aj_flag_store_pi_x (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE.
Definition Bx : sv := SOff 33 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gtu_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 3)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rf_regions0 : smem :=
[ stack_region RF_FRAME; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32; gtu_region ].
Definition rf_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0x10000 0x5fb000 2); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_rf0 : sstate := mkSS A_relay_finish sr_atoms rf_regions0 None rf_facts0.
Definition rf_SH0 : list shent := [].
Definition rf_extra : list word := map (Z_to_bv 64) [as_uar_cell B; SB].
(* Carrying a cell's value across a run (it writes only inside its regions' windows) and across a call (the entry
   keeps every plain image byte: acall_kept's image clause, Reusable/YCbq.v:830, and aentry_post's frame clause). *)
Lemma keep_vm_frame : forall E0 rs (H : word -> bool) m m' a (n : nat) v,
frame_of E0 rs (mrestrict H m) (mrestrict H m') -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall x, a <= x < a + Z.of_nat n -> ~ in_wrange E0 rs x) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros E0 rs H m m' a n v HF Ha Han Hout Hv k Hk.
pose proof (Nat2Z.is_nonneg k) as Hk0. assert (Hkn : Z.of_nat k < Z.of_nat n) by lia.
rewrite <- (Hv k Hk). unfold mbyte.
rewrite (HF (Z_to_bv 64 (a + Z.of_nat k)) ltac:(rewrite unsigned_lit_small by lia; apply Hout; lia)). reflexivity.
Qed.
Lemma keep_vm_img : forall (W1 W2 : world SEGS) m m' a (n : nat) v,
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
 aview SEGS (w_H W2) m' x = aview SEGS (w_H W1) m x) ->
(forall x, a <= x < a + Z.of_nat n -> inG rf_cells x) ->
val_mem SEGS (mrestrict (w_H W1) m) a n v -> val_mem SEGS (mrestrict (w_H W2) m') a n v.
Proof.
intros W1 W2 m m' a n v HK Hin Hv k Hk.
pose proof (Nat2Z.is_nonneg k) as Hk0. assert (Hkn : Z.of_nat k < Z.of_nat n) by lia.
rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
assert (Hxin : inG rf_cells (a + Z.of_nat k)) by (apply Hin; lia).
destruct (HPLAIN (a + Z.of_nat k) Hxin) as (Hi & Ho & He). exact (HK _ Hi Ho He).
Qed.
Lemma in_rf_cell : forall i lo n x, nth_error rf_cells i = Some (lo, n) -> lo <= x < lo + n -> inG rf_cells x.
Proof.
intros i lo n x Hn Hx. unfold inG. apply Exists_exists. exists (lo, n).
split; [exact (nth_error_In _ i Hn) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma rf_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
val_mem SEGS (arm W mem) GTU 1 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs rf_extra)) ss_rf0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_finishP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx rf_SH0 (Eimg (Ereg regs rf_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE Hal32 HGTU0.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16704) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
zsep_pick HSEPG 0%nat 4%nat D1. zsep_pick HSEPG 1%nat 4%nat D2. zsep_pick HSEPG 2%nat 4%nat D3. zsep_pick HSEPG 3%nat 4%nat D4.
cbn [zseps zseps_from fst snd] in HSEP.
pose proof (proj1 (Forall_forall _ _) HIG (GTU, 1) ltac:(left; reflexivity)) as HGTUb. cbn [fst snd] in HGTUb.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs rf_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E244 : ew E (A_OBJ 3) = Z_to_bv 64 (VAL (A_OBJ 3))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_rf0, A_relay_finishP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rf_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, gtu_region, RF_FRAME;
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 33 0) SB);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 32 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
* rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
* rewrite (VB (A_OBJ 3) (VAL (A_OBJ 3)) E244) by (pose proof (pa_val_range (A_OBJ 3)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 3)) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
rewrite Z.add_0_r, HV3. exact HGTU0.
+ apply pairwise_disjoint_of_extents. unfold rf_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, gtu_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 3) (VAL (A_OBJ 3)) E244) by (pose proof (pa_val_range (A_OBJ 3)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite HV3.
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HGTUb HSEP D1 D2 D3 D4. clear.
unfold RF_FRAME, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hS hd1 hd2 hd3 hd4.
repeat split;
first [ solve [clear hd1 hd2 hd3 hd4; lia]
      | solve [clear hS hd2 hd3 hd4; lia]
      | solve [clear hS hd1 hd3 hd4; lia]
      | solve [clear hS hd1 hd2 hd4; lia]
      | solve [clear hS hd1 hd2 hd3; lia]
      | solve [clear hS hd1 hd2 hd3 hd4; lia] ].
+ split; [|split; [exact I | exact I]].
cbn [rf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal32 C1 C3 WS Hstk0 HuR HuA. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rf_SH0. constructor.
Qed.
(* ---------------------------------------------------------------------------------------------------
   THE TWO CUT POINTS.  After the lock the walk splits into three segments joined at concrete machine
   states, in the form of lib/A/W_send_line_cx.v (sl_epi_entry, SLI, sl_loop_stmt):
     - the tail X at 0x82494 (offset 0x1a8): g_nsrc = 0, g_client = -1, g_listen = -1, the unlock, the
       release of the fake frame, the epilogue and the return;
     - the loop L at 0x82454 (offset 0x168), by induction on the entries left: one round checks the
       shadow of s->buf, frees s->buf and calls gestures_end (s);
     - the entry: from the lock's return to the blez, then the tail (no source) or the loop at i = 0.
   The two defects the OLD unit model's walk of this function met (reported by a Theorem Labs lane 2026-10-29)
   cannot arise here: (1) the per-round state speaks only of the entries the loop has NOT reached
   (skipn i es), never of the freed ones, so no round can make it unsatisfiable; (2) the output stream
   is carried as W_rep.v's aout_at, whose block clause is already a disjunction on cap = 0, so nothing
   is claimed about the g_out block when there is none. *)
Definition A_rf_loop : Z := AF_fr_relay_finish + 0x168.
Definition A_rf_tail : Z := AF_fr_relay_finish + 0x1a8.
(* a default entry, for nth *)
Definition rf_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
(* the eleven callee-saved words the prologue wrote into the frame, by rising address: s9 at sp0 - 88,
   s8, s7, s6, s5, s4, s3, s2, s1, s0, ra at sp0 - 8 *)
Definition RF_SAVED : list (bv 5) := [25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition rf_saved (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regsE : bvmap 5 word) : Prop :=
forall i, (i < 11)%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 88 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i RF_SAVED 0%bv))).
(* the registers the walk keeps from its prologue to the return: sp, the frame pointer s0, the fake frame F
   in s2 and s4, the shadow base s3, the frame's shadow s5, the kept auipc register s6 of g_nsrc, and the
   two callee-saved registers the epilogue does not restore *)
Definition rf_kept (regs regsX : bvmap 5 word) (sp0 F : Z) : Prop :=
spZ regsX = sp0 - 96 /\
getr regsX 3 = getr regs 3 /\ getr regsX 4 = getr regs 4 /\
getr regsX 26 = getr regs 26 /\ getr regsX 27 = getr regs 27 /\
getr regsX 8 = w64 sp0 /\ getr regsX 18 = w64 F /\ getr regsX 19 = w64 SB /\
getr regsX 20 = w64 F /\ getr regsX 21 = w64 (SB + F / 8) /\ getr regsX 22 = w64 (VAL (A_HI 9)).
(* The relay's cells when the loop is done: g_src and g_capsrc are as relay_finish found them (it writes
   neither), the table block is still live, and g_nsrc - the only one of them the tail writes - is writable. *)
Definition rf_done (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (T : Z) : Prop :=
awr W mem (rg_nsrc RG) 4 /\
((T = 0 /\ val_mem SEGS (arm W mem) (rg_src RG) 8 0 /\ awr W mem (rg_src RG) 8 /\
  val_mem SEGS (arm W mem) (rg_capsrc RG) 4 0 /\ awr W mem (rg_capsrc RG) 4) \/
 (T <> 0 /\ val_mem SEGS (arm W mem) (rg_src RG) 8 T /\ awr W mem (rg_src RG) 8 /\
  val_mem SEGS (arm W mem) (rg_capsrc RG) 4 16 /\ awr W mem (rg_capsrc RG) 4 /\
  In (T, ATABLE) (ablocks B ly S))).
(* What both segments need from relay_finish's own entry state: its whole afn_pre (the callees' afn_pre and the
   allocator's chain_pre ask for the ABI registers, the frame-pointer chain and the stack geometry; the post names
   the entry's ra), the three inclusions rf_spec gives about the globals, and the blocks it started from. *)
Definition rf_entry_facts (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
(md : Model) (regs : bvmap 5 word) (T : Z) (es : list rentry) (cap out : Z) (rest : list (Z * Z)) : Prop :=
(exists ch, afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch) /\
Permutation (ablocks B ly S) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest) /\
(forall a, inG (RF_G RG GL) a -> inG G a) /\ (forall a, inG (G_SL B RG) a -> inG G a) /\
(forall a, inG (RF_G RG GL) a -> ~ (as_errno B <= a < as_errno B + 4)).
(* ---- X, the state at the tail 0x82494. ---- *)
Definition RFX (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (fpos : Z) (lyX : alayout) (SX : astate) (HpX : list Z) (WX : world SEGS)
(regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) (kr : nat) : Prop :=
exists kX outX,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  lyX SX HpX WX memX mdX kX /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsX (spZ regs) (frame_addr ly 0 fpos) /\ frame_addr ly 0 fpos <> 0 /\
rf_saved WX memX (spZ regs) regs /\
val_mem SEGS (arm WX memX) (frame_addr ly 0 fpos + 56) 8 (flag_addr ly 0 fpos) /\
val_mem SEGS (arm WX memX) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\
rf_done lyX SX WX memX T /\
alock_at RG WX memX true /\
aout_at B RG lyX SX WX memX
  (gse_c (rf_run c O mx no cap es)) (gse_O (rf_run c O mx no cap es)) mx
  (gse_no (rf_run c O mx no cap es)) (gse_cap (rf_run c O mx no cap es)) outX /\
Permutation (ablocks B lyX SX) (rf_tblk T ++ aout_blks (gse_cap (rf_run c O mx no cap es)) outX ++ rest) /\
(exists lst, val_mem SEGS (arm WX memX) GL 4 lst) /\ awr WX memX GL 4 /\
apres_kept B W mem WX memX /\
mo_le MT S SX (rf_cost MT c O mx no cap es) /\
(* the room round: the room left after every round, which rf_post passes on *)
rp_RM RP SX kr.
(* ---- L, the state at the loop head 0x82454, round i: entries 0 .. i-1 are done, i .. n-1 untouched. ---- *)
Definition RFI (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (fpos : Z) (i : nat) (lyL : alayout) (SL : astate) (HpL : list Z) (WL : world SEGS)
(regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (kr : nat) : Prop :=
exists kL outL spent,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  lyL SL HpL WL memL mdL kL /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsL (spZ regs) (frame_addr ly 0 fpos) /\ frame_addr ly 0 fpos <> 0 /\
getr regsL 23 = w64 (Z.of_nat i) /\ getr regsL 24 = w64 (16 + 56 * Z.of_nat i) /\
getr regsL 25 = w64 (VAL (A_HI 10)) /\
rf_saved WL memL (spZ regs) regs /\
val_mem SEGS (arm WL memL) (frame_addr ly 0 fpos + 56) 8 (flag_addr ly 0 fpos) /\
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
(* the room round: the room the remaining rounds charge (each a free and a gestures_end), then rf_post's kr *)
rp_RM RP SL (Z.to_nat (rf_cost MT_rk
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es)) + kr).
(* ---- the two segment statements ---- *)
Definition rf_tail_stmt : Prop :=
forall regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr,
RFX regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS)) mdX)
(rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* rf_spec's caller-context premises for the loop's free (s->buf), at the entry's own chain: the room above sp for
   relay_finish's frame record, and the trace "the free's return address (pc + 392), relay_finish's return address,
   the caller chain's" in CTX.  A premise of the loop, not a conjunct of RFI: it speaks of the entry state only, so
   every round passes it on unchanged. *)
Definition rf_ctx (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) : Prop :=
spZ regs + 16 < ly_top ly /\
exists ch, afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch /\ In (A_relay_finishP + 392 :: raZ regs :: spine ch) CTX.
(* the room round: rf_spec's count premise at the entry state (rf_pk = 5: every round's g_out block may be one more
   request of a class than the entry held, and gestures_end's own premise constant is gse_pk = 4), also a premise
   of the loop - each round's free and gestures_end read their own count premise off it and the round's block
   equation *)
Definition rf_loop_stmt : Prop :=
forall (k : nat) regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr,
(length es - i <= k)%nat ->
rf_ctx regs ly S Hp W mem md ->
cnt_ok_pk RP rf_pk (ablocks B ly S) ->
RFI regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)) mdL)
(rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* RF-TAIL-BEGIN *)
(* ---- The tail X (0x82494 = relay_finish + 0x1a8): g_nsrc = 0, g_client = -1, g_listen = -1, the unlock, the
   fake frame's release (header word, shadow 0xf5, flag byte 0), the epilogue and the return. ----
   The cut state is a fresh symbolic state.  Its regions: the frame (atom 2 = sp0 - 96; the eleven saved words of
   rf_saved at 8 .. 88, read-only), and the three globals the tail stores to, based on the kept auipc atoms (s6 is
   pinned to A_HI 9; the two auipc's of the tail give A_HI 11 and A_HI 12).  s0 is pinned to sp + 96 (the
   epilogue's addi sp, s0, -0x60) and s2 to s4's atom 20 (F; one region would serve both).  The fake frame, its
   shadow and the flag byte are added after the unlock, for the plain flag-store run. *)
Definition rfx_extra (regsE : bvmap 5 word) (fl : Z) : list word := map (getr regsE) RF_SAVED ++ [Z_to_bv 64 fl].
Lemma nth_rfx_extra : forall regsE fl i, (i < 11)%nat ->
nth i (rfx_extra regsE fl) (Z_to_bv 64 0) = getr regsE (nth i RF_SAVED 0%bv).
Proof.
intros regsE fl i Hi. unfold rfx_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
(* every byte of a val_mem is visible (W_relay_event.v re_av_ne) *)
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
Definition rfx_sr : list sv :=
sr_set (sr_set (sr_set sr_atoms 8 (SOff 2 96)) 18 (SOff 20 0)) 22 (SOff (A_HI 9) 0).
Definition rfx_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 96 0 0
  (map (fun i => YP09.mkChunk (8 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 11));
  YP09.mkRegion (Some (A_HI 9)) 868 872 868 872 [];
  YP09.mkRegion (Some (A_HI 11)) (-1208) (-1204) (-1208) (-1204) [];
  YP09.mkRegion (Some (A_HI 12)) (-1252) (-1248) (-1252) (-1248) [] ].
Definition rfx_facts : facts :=
mkFacts [ (20%nat, mkAF 4096 140737479966720 5);
  (A_HI 9, mkAF 0xf000 0x5fc000 0); (A_HI 11, mkAF 0xf000 0x5fc000 0); (A_HI 12, mkAF 0xf000 0x5fc000 0) ] [] [].
Definition ss_rfx : sstate := mkSS A_rf_tail rfx_sr rfx_regions None rfx_facts.
Definition BxX : sv := SOff 19 0.
Lemma rfx_entry : forall (W : world SEGS) regsX memX regsE F fl,
alloc_ceiling <= spZ regsX -> spZ regsX + 96 <= 2 ^ 47 -> spZ regsX mod 16 = 0 ->
getr regsX 8 = w64 (spZ regsX + 96) -> getr regsX 18 = w64 F -> getr regsX 20 = w64 F ->
getr regsX 22 = w64 (VAL (A_HI 9)) ->
4096 <= F -> F + 64 <= alloc_ceiling -> F mod 32 = 0 ->
rf_saved W memX (spZ regsX + 96) regsE ->
awr W memX (rg_nsrc RG) 4 -> awr W memX (rg_client RG) 4 -> awr W memX GL 4 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (rfx_extra regsE fl))) ss_rfx
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE F fl Hceil Htop Hal HR8 HR18 HR20 HR22 HF1 HF2 HF3 HSV HW1 HW2 HW3.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (rfx_extra regsE fl))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U20 : bv_unsigned (ew E 20) = F) by (rewrite (EE 20%nat 20%bv eq_refl), HR20; apply unsigned_lit_small; lia).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
pose proof (UH 9%nat ltac:(lia)) as U9. pose proof (UH 11%nat ltac:(lia)) as U11. pose proof (UH 12%nat ltac:(lia)) as U12.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as Bn.
pose proof (proj1 (Forall_forall _ _) HIG (rg_client RG, 4) ltac:(do 5 right; left; reflexivity)) as Bc.
pose proof (proj1 (Forall_forall _ _) HIG (GL, 4) ltac:(do 6 right; left; reflexivity)) as Bg.
cbn [fst snd] in Bn, Bc, Bg.
unfold ss_rfx. apply pa_entry_st_ok_full.
- unfold rfx_sr.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
  | intros X; discriminate X |] | intros X; discriminate X |].
  + cbn [sv_denot]. rewrite Usp, HR8. reflexivity.
  + cbn [sv_denot]. rewrite U20, HR18, Z.add_0_r. reflexivity.
  + cbn [sv_denot]. rewrite U9, HR22, Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold rfx_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
    apply (chunk_ok_val SEGS E _ (spZ regsX) (8 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i RF_SAVED 0%bv)))).
    * cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite ew_Ereg_extra, nth_rfx_extra by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (getr regsE (nth i RF_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
    * zside.
    * replace (spZ regsX + (8 + 8 * Z.of_nat i)) with (spZ regsX + 96 - 88 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 9) + o) with (rg_nsrc RG + (o - 868)) by lia. exact (HW1 (o - 868) ltac:(lia)).
  + rewrite U11. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 11) + o) with (rg_client RG + (o + 1208)) by lia. exact (HW2 (o + 1208) ltac:(lia)).
  + rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (VAL (A_HI 12) + o) with (GL + (o + 1252)) by lia. exact (HW3 (o + 1252) ltac:(lia)).
- unfold rfx_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9, U11, U12.
  zsep_pick HSEPO 1%nat 2%nat D12. zsep_pick HSEPO 1%nat 3%nat D13. zsep_pick HSEPO 2%nat 3%nat D23.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rfx_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U20, U9, U11, U12. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
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
intros regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16704) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HX as (kX & outX & HJX & ((ch & HPRE0) & HPERM0 & HG1 & HG2 & HG3) & HKP & HF0 & HSV & HFLv & HNS & HDONE & HLK
  & HAO & HPERM & HGLv & HGLw & HPRES & HMO & HRMX).
pose proof HPRE0 as (_ & Hra & _ & Hgp & Htp & _). clear HPRE0 HPERM0.
destruct HKP as (KSP & K3 & K4 & K26 & K27 & K8 & K18 & K19 & K20 & K21 & K22).
pose proof HJX as (HSTK & HXO & (memS & HJi & HAG) & HOUT).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARx & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Hfin : In (0, fpos) (frames SX)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyX 0 fpos = frame_addr ly 0 fpos)
by (unfold frame_addr; pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _); rewrite HlyF; reflexivity).
assert (EFL : flag_addr lyX 0 fpos = flag_addr ly 0 fpos)
by (unfold flag_addr; pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _); rewrite HlyF; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARx Hfin) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARx Hfin) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARx Hfin) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARx Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
rewrite EFA in HF4096, HFceil, HFhigh, HFal, HFapp, HFpres, HFSpres, HFimg.
rewrite EFL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
(* the file's lia does not turn div / mod into equations: F / 8 enters as an atom with these facts *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as Dq; rewrite HFal in Dq; lia).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as Dm. rewrite HFal, Z.add_0_r in Dm. rewrite Dm at 1.
  replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592184995840) by (apply Z.div_lt_upper_bound; lia).
pose proof (rfx_entry WX regsX memX regs F FL
  ltac:(rewrite KSP; rewrite WS in Hslo; lia) ltac:(rewrite KSP; lia)
  ltac:(rewrite KSP, Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite K8, KSP; f_equal; lia) K18 K20 K22 HF4096 HFceil HFal
  ltac:(replace (spZ regsX + 96) with (spZ regs) by lia; exact HSV)
  (proj1 HDONE) ltac:(pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _); exact Hw) HGLw) as HS.
remember (Eimg (Ereg regsX (rfx_extra regs FL))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 11)%nat -> ew E (32 + i) = getr regs (nth i RF_SAVED 0%bv))
by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact (nth_rfx_extra regs FL i Hi)).
assert (E43 : ew E 43 = Z_to_bv 64 FL)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX (rfx_extra regs FL) 11)).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
assert (U9 : bv_unsigned (ew E 289%nat) = VAL (A_HI 9)) by exact (UH 9%nat ltac:(lia)).
assert (U11 : bv_unsigned (ew E 291%nat) = VAL (A_HI 11)) by exact (UH 11%nat ltac:(lia)).
assert (U12 : bv_unsigned (ew E 292%nat) = VAL (A_HI 12)) by exact (UH 12%nat ltac:(lia)).
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
(* ---- the three stores: g_nsrc = 0, g_client = -1, g_listen = -1; a0 = &g_lock; up to the unlock ---- *)
paj_run_tok_x RUN HS HJX SHOK Bspan.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U11, ?U12 in Hr;
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
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U11, ?U12 in Hr; lia | ]).
  destruct Hin. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E _ (w_H WX) memX (ms_mem ms) HFr1 a Ha (NWA a N1 N2 N3))).
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HRn.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HRc.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HRg.
cbn [ms_mem restrict] in HRn, HRc, HRg.
pose proof (field_of_region E _ 289%nat _ _ _ _ _ _ 868 4%N (SLit 0) 0 HRn U9 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as VNS1.
rewrite HH9 in VNS1. change (N.to_nat 4) with 4%nat in VNS1.
pose proof HRc as (_ & _ & _ & HCc). cbn [YP09.r_chunks YP09.r_base base_val] in HCc. apply Forall_inv in HCc.
pose proof (rfx_m1_val E _ _ _ HCc) as VCL1. rewrite U11, HH11 in VCL1.
pose proof HRg as (_ & _ & _ & HCg). cbn [YP09.r_chunks YP09.r_base base_val] in HCg. apply Forall_inv in HCg.
pose proof (rfx_m1_val E _ _ _ HCg) as VGL1. rewrite U12, HH12 in VGL1.
clear HRn HRc HRg HCc HCg.
(* ---- the unlock (a PCall to pthread_mutex_unlock, a0 = &g_lock = VAL (A_OBJ 6)) ---- *)
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
prreg HS (10%bv : bv 5) Q10.
assert (HSPc : spZ (ms_regs ms) = spZ regs + -96) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (QA0 : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 247%nat with (A_OBJ 6).
  rewrite (img_env_atomP E (A_OBJ 6) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), HV6. reflexivity. }
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR1.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B lyX SX a).
{ intros a Ha Ho. destruct (HG a (INL a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho). }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H WX) mem') (rg_lock RG + 4) 4 0)
    WX (ms_regs ms) (ms_mem ms) RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), K3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), K4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
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
      * rewrite HSPc. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. exact (LKW1 (a - rg_lock RG) ltac:(lia)).
      * apply HNOWN. lia.
      * rewrite HSPc. lia.
    + intros a Ha HK. exact (proj2 (proj2 (HG a (INL a ltac:(lia)))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK43) & Hfr3 & Hpres3).
(* the frame region survives the unlock (the callee writes only the lock word and its scratch below sp) *)
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H WX) mem3) HP3 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_aview E (w_H WX) (ms_mem ms) mem3 2%nat (spZ regsX)); [exact Usp | | exact Hpres3].
  intros a Ha. apply Hfr3; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- the fake frame's release: the header word, the shadow (0xf5 x 8), the flag byte; then the epilogue ---- *)
remember (havoc E 66 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 66)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (U2a : bv_unsigned (ew Ea 2) = spZ regsX) by (rewrite OLDa by lia; exact Usp).
assert (U20a : bv_unsigned (ew Ea 20) = F)
by (rewrite OLDa, (EE 20%nat 20%bv eq_refl), K20 by lia; apply unsigned_lit_small; lia).
assert (U21a : bv_unsigned (ew Ea 21) = SB + F / 8)
by (rewrite OLDa, (EE 21%nat 21%bv eq_refl), K21 by lia; apply unsigned_lit_small; unfold SB; lia).
assert (U43a : bv_unsigned (ew Ea 43) = FL) by (rewrite OLDa, E43 by lia; apply unsigned_lit_small; lia).
assert (PR2 : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) mem3 a)
by (intros a Ha; apply Hpres3; exact (apresent_grows (w_H WX) memX (ms_mem ms) a MG1 Ha)).
assert (FLV2 : val_mem SEGS (mrestrict (w_H WX) mem3) (F + 56) 8 FL).
{ apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX mem3 _ 8 FL); [|exact HFLv].
  intros k Hk. cbn in Hk. unfold off_img in HFimg.
  rewrite (Hfr3 (F + 56 + k) ltac:(lia) ltac:(lia) ltac:(lia)). apply KA; lia. }
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 20%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 43 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U20a; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply PR2; exact (proj1 (HFpres (F + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ea _ F 56 8 _ FL);
      [cbn [sv_denot]; rewrite U43a, Z.add_0_r; reflexivity | zside | zside | exact FLV2] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U20a, U2a; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 21%nat) 0 8 0 8 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U21a; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply PR2;
    unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; exact (proj1 (HFSpres o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U21a, U20a, U2a; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold SB;
    repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 43%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U43a; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply PR2; replace (FL + o) with FL by lia; exact HFLp)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U43a, U21a, U20a, U2a; repeat split;
    [ unfold zone2, off_img in HFLz; unfold SB; lia
    | destruct (Z_lt_ge_dec FL F) as [Hlt | Hge]; [left; lia|];
      destruct (Z_lt_ge_dec FL (F + 64)) as [Hlt2 | Hge2]; [exfalso; exact (proj2 (HFpres FL ltac:(lia)) HFLo) | right; lia]
    | lia ])) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the plain runner on the donor journal inside ajournal_gx (own = [(0, fpos)]): unpack, run, repack below *)
destruct HJX3 as (_ & _ & (memS3 & HJi3 & HAG3) & _). rewrite !Z.add_0_r in HJi3.
paj_run_flag_sh_x RUNF HS HJi3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. rewrite EFL.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2a, ?U20a, ?U21a, ?U43a in Hr;
    first [ lia
    | right; lia
    | left; right; right; right; exists 0, fpos; split; [left; reflexivity|]; rewrite EFA; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
            | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ] | ]).
  destruct Hin. }
{ intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U43a
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
match goal with Hx : mem_grows _ _ |- _ => lazymatch Hx with MG1 => fail | _ => rename Hx into MG3 end end.
match goal with Hx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  lazymatch Hx with HFr1 => fail | _ => rename Hx into HFrC end end.
cbn [ms_mem mkst] in MG3, HFrC.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msf end.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
(* ---- the return: ret to the entry's ra (restored from the frame), sp back to sp0 ---- *)
eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (E32 : ew E 32 = getr regs 25) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 24) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 23) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 22) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs 21) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs 20) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs 19) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = getr regs 9) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = getr regs 8) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = getr regs 1) by exact (EX 10%nat ltac:(lia)).
pose proof HJi3 as (HARf & _ & _ & _ & _ & Hfrf & _).
assert (EabF : ablocks B lyX (stack_free_state 0 fpos SX) = ablocks B lyX SX)
by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
(* presence and writability, from the cut to the return *)
assert (PRf : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) (ms_mem msf) a)
by (intros a Ha; exact (apresent_grows (w_H WX) mem3 (ms_mem msf) a MG3 (PR2 a Ha))).
assert (WKf : forall x, writable_at SEGS (arm WX memX) x -> writable_at SEGS (arm WX (ms_mem msf)) x)
by (intros x Hx; exact (writable_kept (w_H WX) memX (ms_mem msf) x (PRf x) Hx)).
(* the release's windows: the fake frame, its shadow and the flag byte *)
assert (KC : forall x, 0 <= x < 2 ^ 64 -> ~ (F <= x < F + 64) -> ~ (SB + F / 8 <= x < SB + F / 8 + 8) -> x <> FL ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) mem3 x).
{ intros x Hx N1 N2 N3. apply (aview_kept_out Ea _ (w_H WX) mem3 (ms_mem msf) HFrC x Hx).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2a, ?U20a, ?U21a, ?U43a in Hr; lia | ]).
  destruct Hin. }
pose proof pa_img_range as Himg.
(* an image-band byte off the lock word keeps its view from after the stores to the return *)
assert (KIMG : forall x, 0x10000 <= x < 0x5fb000 -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) (ms_mem ms) x).
{ intros x Hx Nl. unfold off_img in HFimg. unfold zone2, off_img in HFLz.
  rewrite (KC x ltac:(lia) ltac:(lia) ltac:(unfold SB; lia) ltac:(lia)).
  apply Hfr3; lia. }
(* ... and from the cut, when it is none of the three stored cells *)
assert (KALL : forall x, 0x10000 <= x < 0x5fb000 -> ~ (rg_nsrc RG <= x < rg_nsrc RG + 4) ->
  ~ (rg_client RG <= x < rg_client RG + 4) -> ~ (GL <= x < GL + 4) -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x)
by (intros x Hx N1 N2 N3 N4; rewrite (KIMG x Hx N4); apply KA; [lia | exact N1 | exact N2 | exact N3]).
(* a byte of a live block keeps its view from the cut to the return *)
assert (KBLK : forall p n x, In (p, n) (ablocks B lyX SX) -> p <= x < p + req_size n ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros p n x Hin Hx.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARx Hin) as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _).
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n x HARx Hin Hx) as Hxn.
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 0 fpos HARx Hin Hfin) as Hsep.
  rewrite EFA in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep.
  assert (Nc : forall i lo m, nth_error rf_cells i = Some (lo, m) -> ~ (lo <= x < lo + m)).
  { intros i lo m Hn Hr. exact (Hxn (proj1 (HPLAIN x (in_rf_cell i lo m x Hn Hr)))). }
  rewrite (KC x ltac:(lia) ltac:(lia)
    ltac:(intros Hs; exact (fshadow_not_app F 8 p (req_size n) x ltac:(lia) ltac:(lia) Hpapp ltac:(unfold SB in Hs; lia) Hx))
    ltac:(intros ->; exact (proj2 (Hppres FL Hx) HFLo))).
  rewrite (Hfr3 x ltac:(lia) ltac:(intros Hl; apply (Nc 1%nat (rg_lock RG) 12); [reflexivity | lia]) ltac:(lia)).
  apply KA; [lia | apply (Nc 2%nat); reflexivity | apply (Nc 5%nat); reflexivity | apply (Nc 6%nat); reflexivity]. }
(* the values the tail stored, at the return *)
assert (VNSf : val_mem SEGS (arm WX (ms_mem msf)) (rg_nsrc RG) 4 0).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 0); [|exact VNS1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 1%nat S01. apply KIMG; lia. }
assert (VCLf : val_mem SEGS (arm WX (ms_mem msf)) (rg_client RG) 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VCL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 2%nat S02. apply KIMG; lia. }
assert (VGLf : val_mem SEGS (arm WX (ms_mem msf)) GL 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VGL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 3%nat S03. apply KIMG; lia. }
(* the lock: released (word 4 by the unlock), type and waiter words kept *)
assert (LKF : alock_at RG WX (ms_mem msf) false).
{ unfold alock_at, arm. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK0]. intros k Hk. cbn in Hk. apply KALL; lia.
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) mem3 _ _ 4 0); [|exact HLK43]. intros k Hk. cbn in Hk.
    unfold off_img in HFimg. unfold zone2, off_img in HFLz.
    apply KC; [lia | lia | unfold SB; lia | lia].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK8]. intros k Hk. cbn in Hk. apply KALL; lia.
  - intros i Hi. apply WKf. exact (LKW i Hi). }
(* the controller's cells (all but g_client) and the g_out block, from the cut *)
assert (AK : akept WX memX WX (ms_mem msf) (rfx_aout_fp (gse_cap (rf_run c O mx no cap es)) outX)).
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
  - assert (Hb : 0x10000 <= a < 0x5fb000).
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
assert (KSRC : forall x, rg_src RG <= x < rg_src RG + 8 -> aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 5%nat 7%nat T1. zsep_pick HSEPG 6%nat 7%nat T2. zsep_pick HSEPG 7%nat 9%nat T3. zsep_pick HSEPG 7%nat 10%nat T4.
  apply KALL; lia. }
assert (KCAP : forall x, rg_capsrc RG <= x < rg_capsrc RG + 4 -> aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 5%nat 8%nat T1. zsep_pick HSEPG 6%nat 8%nat T2. zsep_pick HSEPG 8%nat 9%nat T3. zsep_pick HSEPG 8%nat 10%nat T4.
  apply KALL; lia. }
(* ---- the post ---- *)
unfold rf_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists lyX, (stack_free_state 0 fpos SX), HpX, r, m, d, kX, outX end.
split; [rewrite R1, OLDa, E42, Hra by lia; reflexivity|].
split.
{ eapply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []).
  all: [> lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs); exact HJi3 | exact HAG3 | intros a Ha; lia]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, U2a, KSP.
    replace (spZ regs - 96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact K3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact K4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8, OLDa by lia. exact E41.
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9, OLDa by lia. exact E40.
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18, OLDa by lia. exact E39.
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19, OLDa by lia. exact E38.
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20, OLDa by lia. exact E37.
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21, OLDa by lia. exact E36.
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22, OLDa by lia. exact E35.
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23, OLDa by lia. exact E34.
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24, OLDa by lia. exact E33.
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25, OLDa by lia. exact E32.
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26, OLDa, (EE 26%nat 26%bv eq_refl) by lia. exact K26.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27, OLDa, (EE 27%nat 27%bv eq_refl) by lia. exact K27. }
split. { intros a Hi Ho He Hpr. exact (PRf a (HPRES a Hi Ho He Hpr)). }
split. { cbn [app] in Hfrf. exact Hfrf. }
split.
{ assert (HMF : mo_le MT SX (stack_free_state 0 fpos SX) 0) by (unfold stack_free_state; exact (MO_FR SX _)).
  pose proof (mle_station MT S SX _ _ 0 MLAW HMO HMF) as HM. rewrite Z.add_0_r in HM. exact HM. }
(* the room round: the release's state is a set_fs of SX (YG01.v stack_free_state), so rp_RPF carries RFX's room *)
split. { unfold stack_free_state. exact (rp_RPF RP _ _ _ HRMX). }
split. { rewrite EabF. exact HPERM. }
split.
{ apply (rfx_aout_m1 lyX SX WX memX _ _ WX _ _ _ mx _ _ outX HAO AK WKf VCLf).
  intros b Hb. rewrite EabF. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
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
    assert (HTin' : In (T, ATABLE) (ablocks B lyX (stack_free_state 0 fpos SX))) by (rewrite EabF; exact HTin).
    split; [exact HTin'|].
    (* the empty table: aentry_ok, NoDup and (W8's twelfth conjunct) no entry block is the table, all over [] *)
    split; [|split; [constructor | split; [constructor | constructor]]].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HARf HTin') as (_ & _ & _ & _ & HTp & _).
    destruct (garr8_of_present SEGS (arm WX (ms_mem msf)) T 896) as (l & Hl & Hg).
    { intros a Ha. destruct (HTp a ltac:(unfold req_size, ATABLE; cbn in Ha |- *; lia)) as ((Hh & b & Hb) & _).
      exists b. unfold arm, mrestrict. rewrite Hh. exact Hb. }
    exists (map (Z_to_bv 8) l). unfold atable_at. cbn [length map concat app].
    rewrite (rfx_bzs_map l (garr8_bytes_ok SEGS _ _ _ Hg)), length_map, Hl.
    unfold ATABLE, AENT. split; [cbn; lia|]. split; [cbn; lia|]. exact Hg. }
split; [exact VGLf|].
intros i Hi. apply WKf. exact (HGLw i Hi).
Qed.
(* RF-TAIL-END *)
(* RF-LOOP-BEGIN *)
(* ---- THE LOOP L at 0x82454 (offset 0x168), by induction on the entries left, in the form of
   W_check_bounded.v cb_loopX.  One round: the shadow check of &s->buf and the load of s->buf (one token run),
   free (s->buf) (afree_cf_rule / afree_null_cf_rule on the inner journal, W_source_reset.v's form), the internal
   call gestures_end (s) (gse_spec, composed with ajournal_gx_G_mono and ajournal_gx_sub, W_relay_event.v's form),
   the reload of g_nsrc and the blt.  The two defects of the OLD unit model's walk (a Theorem Labs lane 2026-10-29) are
   avoided here as follows: (1) the round re-establishes RFI at i + 1, which speaks only of skipn (i + 1) es:
   nothing is ever claimed about the entries already freed; (2) the g_out block is carried only through aout_at
   (whose block clause is the disjunction on cap = 0) and through aout_blks, which is [] when cap = 0: no claim
   about a g_out block is made when there is none. ---- *)
(* the model's list helpers *)
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
(* the room and the cost of the remaining entries *)
Lemma rfl_gse_room_mono : forall xs bb bb' c mx no cap, bb' <= bb ->
gse_room MMAX bb c mx no cap xs -> gse_room MMAX bb' c mx no cap xs.
Proof.
induction xs as [|x xs IH]; intros bb bb' c mx no cap Hb H; cbn [gse_room] in *; [exact I|].
destruct H as ((H1 & H2) & H4). split; [unfold ge_room in *; split; lia|].
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
(* the symbolic state at the loop head: s3 = SB (atom 19), atom 32 = T (g_src), 33 = T + 16 + 56 i (&s->buf),
   34 = s->buf, 35 = |es| (g_nsrc); s9 and s6 pinned to the two auipc atoms the PLdHi slots test *)
Definition rfl_Bx : sv := SOff 19 0.
Definition rfl_sr : list sv := sr_set (sr_set sr_atoms 25 (SOff (A_HI 10) 0)) 22 (SOff (A_HI 9) 0).
Definition rfl_regions : smem :=
[ YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition rfl_facts : facts :=
mkFacts [ (19%nat, mkAF SB SB 0); (32%nat, HPTR 4); (33%nat, HPTR 3); (34%nat, mkAF 0 (2 ^ 64 - 1) 0);
  (35%nat, mkAF 0 16 0) ] [] [(SAlu ALU_ADD (SOff 32 0) (SOff 24 0), SOff 33 0)].
Definition ss_rfl : sstate := mkSS A_rf_loop rfl_sr rfl_regions None rfl_facts.
Definition rfl_SH : list shent := [ mkSHE 33 0 8 ].
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
(* a byte that stays present stays writable (W_relay_event.v re_wr_pres2) *)
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
(* the held part of a table entry survives a step that keeps its blocks and their bytes (W_rep.v aentry_ok_kept) *)
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
(* the g_out block's bytes are exactly its capacity (aout_blks is [] at cap 0): the room round's `- cap` threading
   of rf_room charges the round only the growth gse_cap r - cap, because the old g_out block is freed *)
Lemma rfl_bsum_aout_eq : forall cap out, bsum (aout_blks cap out) = cap.
Proof. intros cap out. unfold aout_blks. destruct (Z.eqb_spec cap 0) as [-> | _]; unfold bsum; cbn [fold_right fst snd]; lia. Qed.
(* a cell apart from each of G_SL's six cells is not a byte of G_SL; one separation per case, picked from the
   zseps by index and given to lia alone (never every disjunction at once) *)
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
(* a callee's frame-pointer chain at a call of the round: sp = sp0 - 96 and s0 = sp0, the record (sp0, ra, s0) of
   the prologue's saved words, then the entry's chain from s0 (achain_push); or no chain when sp0 is the top *)
Lemma rfl_chain_call : forall ly (rd0 rd : reader) sp0 v ch ra,
achain ly rd0 sp0 v ch -> alloc_ceiling <= sp0 -> sp0 mod 16 = 0 -> ly_top ly <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
exists ch', achain ly rd (sp0 - 96) sp0 ch'.
Proof.
intros ly rd0 rd sp0 v ch ra Hc Hceil Hal Htop Hk H8 H16 Hra.
destruct (Z_lt_ge_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch).
  assert (Hal8 : sp0 mod 8 = 0).
  { pose proof (Z.div_mod sp0 16 ltac:(discriminate)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
    replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (Hsp' : sp0 - 96 + 16 <= sp0) by lia.
  exact (achain_push ly rd0 rd sp0 v ra ch (sp0 - 96) Hc Htop Hk H8 H16 Hra Hceil Hal8 Hlt Hsp').
- exists []. left. split; [right; left; apply Z.ge_le; exact Hge | reflexivity].
Qed.
(* the same at the room rf_ctx gives (sp0 + 16 < ly_top ly): the chain is exactly the record (sp0, ra, s0) pushed
   on the entry's, so its spine is ra :: spine ch - the no-chain case, whose trace would be the free's return
   address alone, is refuted *)
Lemma rfl_chain_call_top : forall ly (rd0 rd : reader) sp0 v ch ra,
achain ly rd0 sp0 v ch -> alloc_ceiling <= sp0 -> sp0 mod 16 = 0 -> ly_top ly <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra -> sp0 + 16 < ly_top ly ->
achain ly rd (sp0 - 96) sp0 ((sp0, ra, v) :: ch).
Proof.
intros ly rd0 rd sp0 v ch ra Hc Hceil Hal Htop Hk H8 H16 Hra Hroom.
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(discriminate)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
  replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
assert (Hsp' : sp0 - 96 + 16 <= sp0) by lia.
exact (achain_push ly rd0 rd sp0 v ra ch (sp0 - 96) Hc Htop Hk H8 H16 Hra Hceil Hal8 ltac:(lia) Hsp').
Qed.
(* END5's five bytes are read-only image bytes: two memories with the read-only view agree on them *)
Lemma rfl_end5_kept : forall (W W' : world SEGS) m m', rom_view SEGS W m -> rom_view SEGS W' m' ->
garr8 SEGS (arm W m) (VAL A_lit_end5) (bzs END5) -> garr8 SEGS (arm W' m') (VAL A_lit_end5) (bzs END5).
Proof.
intros W W' m m' R R' Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') _ _ Hg).
intros x Hx. unfold bzs in Hx. rewrite length_map in Hx. unfold arm. apply (mbyte_of_aview SEGS).
pose proof (HE5R x Hx) as Hr. rewrite (R' x Hr), (R x Hr). reflexivity.
Qed.
Lemma rf_loop : rf_tail_stmt -> rf_loop_stmt.
Proof.
intros TAIL. unfold rf_loop_stmt.
induction k as [|k IH]; intros regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr Hk HCTXF HCNT0 HRFI.
{ exfalso. destruct HRFI as (kL & outL & spent & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRFI as (kL & outL & spent & HJ & HEF & HKP & HF0 & H23 & H24 & H25 & HSV & HFLG & Hi & Hn16 & HT0 &
  HNS & HNSw & HSRC & HSRCw & HCAP & HCAPw & HTB & HENT & HLK & HOUT & HPERM & HGLv & HGLw & HEND5 & HROM & HPK &
  HROOM & HMLE & HSP & HMOK & HRML).
set (F := frame_addr ly 0 fpos) in *. set (sp0 := spZ regs) in *.
set (e := nth i es rf_e0).
destruct (HENT i ltac:(lia)) as (HG8 & HAW & HHELD & HBUF). fold e in HG8, HAW, HHELD, HBUF.
change (rfl_bufok lyL SL e) in HBUF.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARL.
destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL T ATABLE HARL HTB) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTapp, HTpres.
assert (Rb : 0 <= re_buf e < 2 ^ 64).
{ destruct HBUF as [(_ & ->) | (Hc & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL _ _ HARL Hin) as (_ & Hb4096 & Hbceil & _). pose proof (req_size_pos (re_cap e) ltac:(lia)). lia. }
set (p := T + 16 + 56 * Z.of_nat i).
set (n := Z.of_nat (length es)).
assert (HVB : val_mem SEGS (mrestrict (w_H WL) memL) p 8 (re_buf e)).
{ pose proof HHELD as (Hp1 & _). pose proof (rfl_buf_field _ _ e Hp1 Rb HG8) as H. unfold p, AENT in *.
  replace (T + 16 + 56 * Z.of_nat i) with (T + 56 * Z.of_nat i + 16) by lia. exact H. }
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
pose proof HKP as (Ksp & K3 & K4 & K26 & K27 & K8 & K18 & K19 & K20 & K21 & K22).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact K19).
assert (E24 : ew E 24 = Z_to_bv 64 (16 + 56 * Z.of_nat i)) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (EO : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j)) by (intros j Hj; subst E; apply Eimg_img; exact Hj).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsrc : forall x, rg_src RG <= x < rg_src RG + 8 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 3%nat _ 8 x eq_refl Hx)).
assert (Hnsrc : forall x, rg_nsrc RG <= x < rg_nsrc RG + 4 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 2%nat _ 4 x eq_refl Hx)).
assert (HTni : forall x, T <= x < T + 896 -> ~ in_img SEGS x)
by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL memL mdL T ATABLE x HARL HTB ltac:(change (req_size ATABLE) with 896; lia))).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb. cbn [fst snd] in HNSb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as HSRb. cbn [fst snd] in HSRb.
assert (Hp8 : p mod 8 = 0).
{ unfold p. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 16 + 56 * Z.of_nat i) with ((2 * (T / 16) + 2 + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
assert (HS : st_ok_pi SEGS VAL E ss_rfl (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rfl. apply pa_entry_st_ok_full.
  - unfold rfl_sr. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    + cbn [sv_denot]. rewrite (EO (A_HI 10) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact H25.
    + cbn [sv_denot]. rewrite (EO (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact K22.
  - vm_compute. reflexivity.
  - unfold rfl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 8) _ (EO (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 8))), HV8.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) T);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HSRC.
    + rewrite (VB (A_OBJ 7) _ (EO (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 7))), HV7.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold n; zside | zside |].
      rewrite Z.add_0_r. exact HNS.
    + rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
      split; [unfold p; lia|]. split; [unfold p; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 8 (SOff 34 0) (re_buf e));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HVB.
  - apply pairwise_disjoint_of_extents. unfold rfl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 8) _ (EO (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 8))), HV8.
    rewrite (VB (A_OBJ 7) _ (EO (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 7))), HV7.
    rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    zsep_pick HSEPG 6%nat 7%nat D67.
    split; [split; [lia | split; [|exact I]] | split; [split; [|exact I] | split; exact I]].
    + rewrite !Z.add_0_r. apply rfl_apart; [lia | lia|]. intros x Hx1 Hx2.
      apply (HTni x ltac:(unfold p in Hx2; lia)). exact (proj1 (HPLAIN x (Hsrc x ltac:(lia)))).
    + rewrite !Z.add_0_r. apply rfl_apart; [lia | lia|]. intros x Hx1 Hx2.
      apply (HTni x ltac:(unfold p in Hx2; lia)). exact (proj1 (HPLAIN x (Hnsrc x ltac:(lia)))).
  - split; [|split; [exact I|]].
    + cbn [rfl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, p, n; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold n. revert HT16 HT4096 HTceil Hp8 Rb Hn16 Hi C1. clear. unfold p, SB. intros.
      repeat match goal with |- _ /\ _ => split end; lia.
    + cbn [rfl_facts f_alias alias_ok]. split; [|exact I]. apply bv_eq.
      fold (U E (SAlu ALU_ADD (SOff 32 0) (SOff 24 0))). fold (U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 T E32), (U_atom E 24 _ E24), (U_atom E 33 p E33) by (unfold p; lia).
      cbn [zalu_raw]. unfold zcanon, M64. unfold p. rewrite Z.mod_small by lia. lia. }
clear HE.
assert (HBx : U E rfl_Bx = SHADOW_OFF) by (unfold rfl_Bx; rewrite (U_atom E 19 SB E19) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS rfl_Bx rfl_SH E (mrestrict (w_H WL) memL)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyL SL HpL WL memL mdL T ATABLE p 8 HARL HTB); unfold p;
    change (req_size ATABLE) with 896; lia.
  - exact HBx.
  - rewrite (U_atom E 33 p E33) by (unfold p; lia). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold p, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold A_rf_loop.
paj_run_tok_x RUN HS HJ SHOK Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. }
(* ---- free (s->buf).  The run wrote nothing: the memory at the call is memL as the walk sees it. ---- *)
assert (MEQ1 : forall x, mrestrict (w_H WL) (ms_mem ms) x = mrestrict (w_H WL) memL x).
{ intros x. apply HFr. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
assert (AV1 : forall a, aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H WL) memL a)
by (intros a; apply aview_eq_of; apply MEQ1).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
(* the entry chain che is rf_ctx's, so that its trace is in CTX; rf_entry_facts' own afn_pre is not needed here *)
pose proof HEF as (_ & HPERM0 & HRFG & HSLG & HRFGe).
(* the room round: every class's live count at this round's loop head is at most the entry's plus one *)
assert (HCL : forall P, (ReplyCnt.acnt P (ablocks B lyL SL) <= ReplyCnt.acnt P (ablocks B ly S) + 1)%nat).
{ intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPERM0). apply rfl_acnt_round. }
pose proof HCTXF as (HTOPR & che & (HARe & Hrae & Hra4e & HGP0 & HTP0 & HstkE & HpresE & HchE & HQTE) & HCTXE).
change (spZ regs) with sp0 in HstkE, HpresE, HchE, HTOPR.
pose proof HstkE as (HalE & HstkE0 & HceilE & HsloE & HshiE & H47E & HbotE & HtopE & Htop2E).
assert (RSTK0 : 96 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (HceilS : alloc_ceiling <= sp0) by (unfold ASTACK in RSTK0; lia).
assert (HtopS : ly_top ly <= 2 ^ 64) by lia.
(* the stack at and above sp0 is the entry's, as the walk sees it: the journal (now at the run's memory) keeps it,
   and it is no G byte *)
assert (KST : forall a, sp0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ pose proof (ajournal_gx_inner_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJ0 & Hag0).
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & HJ0k & _).
  intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (unfold ASTACK in RSTK0; lia).
  rewrite (HJ0k a Hac ltac:(lia)). apply Hag0. rewrite unsigned_lit_small by lia. intros Hg.
  destruct (HG a Hg) as [Hi1 _]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (EtopL : ly_top lyL = ly_top ly).
{ pose proof (ajournal_gx_inner_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJ0 & _).
  pose proof HJ0 as (_ & HlyL0 & _). pose proof HlyL0 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _). exact Et. }
(* the prologue's saved ra and s0, at sp0 - 8 and sp0 - 16, read through any reader that agrees there with L's *)
assert (RDW : forall rd : reader, (forall a, sp0 - 16 <= a < sp0 -> rd a = aview SEGS (w_H WL) memL a) ->
  rdword rd (sp0 - 8) = Some (raZ regs) /\ rdword rd (sp0 - 16) = Some (s0Z regs)).
{ intros rd Hrd. pose proof (HSV 10%nat ltac:(lia)) as V10. pose proof (HSV 9%nat ltac:(lia)) as V9.
  change (nth 10 RF_SAVED 0%bv) with (1%bv : bv 5) in V10. change (nth 9 RF_SAVED 0%bv) with (8%bv : bv 5) in V9.
  change (Z.of_nat 10) with 10 in V10. change (Z.of_nat 9) with 9 in V9.
  replace (sp0 - 88 + 8 * 10) with (sp0 - 8) in V10 by lia. replace (sp0 - 88 + 8 * 9) with (sp0 - 16) in V9 by lia.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R1. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8.
  change (bv_modulus 64) with (2 ^ 64) in R1, R8.
  split.
  - rewrite (rdword_ext (aview SEGS (w_H WL) memL) rd (sp0 - 8)) by (intros k0 Hk0; apply Hrd; lia).
    exact (rdword_of_val_mem SEGS (w_H WL) memL (sp0 - 8) (raZ regs) V10 R1).
  - rewrite (rdword_ext (aview SEGS (w_H WL) memL) rd (sp0 - 16)) by (intros k0 Hk0; apply Hrd; lia).
    exact (rdword_of_val_mem SEGS (w_H WL) memL (sp0 - 16) (s0Z regs) V9 R8). }
assert (Usp1 : spZ (ms_regs ms) = sp0 + -96) by (unfold spZ in Ksp |- *; rewrite Q2, (EE 2%nat 2%bv eq_refl); lia).
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), K3; exact HGP0).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), K4; exact HTP0).
assert (Q10' : getr (ms_regs ms) 10 = w64 (re_buf e)) by (rewrite Q10, E34; reflexivity).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the free's chain: relay_finish's record pushed on the entry's (rf_ctx's room refutes the no-chain case), so
   its trace - the free's return address pc + 392, then raZ regs, then the caller chain's - is rf_ctx's *)
assert (HRA1 : raZ (ms_regs ms) = A_relay_finishP + 392).
{ unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold A_relay_finishP, A_relay_finish, A_rf_loop, AF_fr_relay_finish. lia. }
assert (HCH : exists ch, chain_pre lyL (aview SEGS (w_H WL) (ms_mem ms)) (ms_regs ms) ch /\
  In (raZ (ms_regs ms) :: spine ch) CTX).
{ destruct (RDW (aview SEGS (w_H WL) (ms_mem ms)) ltac:(intros a _; apply AV1)) as [R8 R16].
  pose proof (rfl_chain_call_top ly (aview SEGS (w_H W) mem) (aview SEGS (w_H WL) (ms_mem ms)) sp0 (s0Z regs) che (raZ regs)
    HchE HceilS HalE HtopS ltac:(intros a Ha; apply KST; exact Ha)
    R8 R16 Hra4e HTOPR) as Hch'.
  exists ((sp0, raZ regs, s0Z regs) :: che). split.
  - apply (achain_chain_pre lyL _ (sp0 - 96) sp0 _ (ms_regs ms)).
    + exact (achain_ly_top ly lyL _ _ _ _ EtopL Hch').
    + rewrite Usp1. unfold ASTACK in RSTK0. lia.
    + unfold s0Z. rewrite Q8, (EE 8%nat 8%bv eq_refl), K8. unfold w64. apply unsigned_lit_small. unfold ASTACK in RSTK0. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite HRA1. exact HCTXE. }
destruct HCH as (ch & HCH & HCTXc).
set (r0 := rf_run c O mx no cap (firstn i es)) in *.
assert (Hcap0 : 0 <= gse_cap r0).
{ destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  destruct H26 as [(Hc & _) | (Hc & _)]; lia. }
rewrite (rfl_skipn_S es i Hi) in HSP, HROOM, HPERM, HRML. cbn [rf_cost rf_room rf_eblks concat map] in HSP, HROOM, HPERM, HRML.
fold e in HSP, HROOM, HPERM, HRML.
set (r1 := gse_run (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) in *.
destruct (rfl_gse_nonneg MT MLAW (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0) as [Hgc0 Hgk0].
fold r1 in Hgk0.
pose proof (rfl_cost_nonneg MT MLAW (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0) as Hrc0.
(* the room round: the room this round charges - the free's 1, then gestures_end's - and what the rounds after it
   and rf_post are owed (kr4), split exactly: MT_rk's costs are nonnegative *)
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
assert (HRFS : ASTACK - -96 <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
(* the room round: the free's stack room, from the round's inner journal (aj_stack_room_x) *)
assert (HSR : ly_bot lyL + ACALL_PREFIX < spZ (ms_regs ms))
by (eapply aj_stack_room_x; [exact HJi | exact Usp1 | exact HRFS]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply SRr_bind with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_x (SK := SK) SEGS B PST ARx RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)]
    ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  Permutation (ablocks B lyL SL) (rfl_bblk e ++ ablocks B ly4 S4) /\
  frames S4 = frames SL /\
  acall_kept SEGS B lyL SL WL mm W4 mem4 (sp0 + -96 - ASTACK) (sp0 + -96) (rfl_bex e) /\
  mo_le MT SL S4 (mo_free MT) /\
  rp_RM RP S4 kr4 /\
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + j) = aview SEGS (w_H WL) mm (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H WL) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct HBUF as [(Hc0 & Hb0) | (Hc0 & Hin0)].
  - eapply SRr_mono.
    { exact (AFREE0 WL (ms_regs ms) (ms_mem ms) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)] lyL SL HpL _ _
        (-96) (getr (ms_regs ms) 1) ch kr4 HJi ltac:(rewrite Q10', Hb0; reflexivity) Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXc HRMf HCNTf HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_eq _ 0) Hc0); exact (Permutation_sym HPm)|].
    split; [exact HFr4|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a []|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He Hpr).
  - eapply SRr_mono.
    { exact (AFREE WL (ms_regs ms) (ms_mem ms) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)] lyL SL HpL _ _
        (re_buf e) (re_cap e) (-96) (getr (ms_regs ms) 1) ch kr4 HJi Hin0 Q10' Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXc HRMf HCNTf
        (HFPof Hc0) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)), Eb1, Eb2; cbn [app];
      exact (Permutation_sym (Permutation_middle l1 l2 _))|].
    split; [exact HFr4|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a Ha; unfold rfl_bex; split; [lia | exact Ha]|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He); [|exact Hpr].
    intros Hblk. exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL (ms_mem ms) _ (re_buf e) (re_cap e) a HARc Hin0 Hblk Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HFR4 & HK4 & HML4 & HRM4 & HERR4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK sp0 (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] RF_STK sp0 _ ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem4 md4 kk4 memS HSTK HXO);
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
  - apply (region_kept_val_at E _ _ 249%nat (rg_src RG) 8 T);
    [change 249%nat with (A_OBJ 8); rewrite <- HV8; exact (HEI (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem ms)); [intros q _; apply AV1 | exact HSRC]
    | exact VS4 | lia].
  - apply (region_kept_val_at E _ _ 248%nat (rg_nsrc RG) 4 n);
    [change 248%nat with (A_OBJ 7); rewrite <- HV7; exact (HEI (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem ms)); [intros q _; apply AV1 | exact HNS]
    | exact VN4 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 36 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOK4 : sh_ok SEGS rfl_Bx [] Ea (mrestrict (w_H W4) mem4)) by constructor.
paj_run_to_tok_x RUNTO HS HJ4 SHOK4 Bspan AF_fr_gestures_end.
{ apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
(* ---- the call gestures_end (s), s = T + 56 i = SA.  The run wrote nothing. ---- *)
lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms0)) |- _ => rename Hx into HFr2 end.
lazymatch goal with Hx : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms0)) |- _ => rename Hx into MG2 end.
assert (MEQ2 : forall x, mrestrict (w_H W4) (ms_mem ms0) x = mrestrict (w_H W4) mem4 x).
{ intros x. apply HFr2. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
assert (AV2 : forall a, aview SEGS (w_H W4) (ms_mem ms0) a = aview SEGS (w_H W4) mem4 a) by (intros a; apply aview_eq_of; apply MEQ2).
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
  aview SEGS (w_H W4) (ms_mem ms0) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hx. rewrite AV2.
  assert (Hin1 : In (b, m) (ablocks B lyL SL)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM'|];
    destruct Hin as [<- | Hin]; [left; reflexivity | right; apply in_or_app; right; exact Hin]).
  replace x with (b + (x - b)) by lia. rewrite (KF2 b m (x - b) Hin1 ltac:(lia)); [apply AV1|].
  intros (Hc & Hx2). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
  assert (Hne : (b, m) <> (re_buf e, re_cap e)) by (intros Heq; apply (BUFNOT Hc); rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x SEGS B ARx LAWS lyL SL _ WL memL mdL b m _ _ HARL Hin1 Hin0 Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (PR2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H WL) memL a -> apresent (w_H W4) (ms_mem ms0) a).
{ intros a Ha Ho He [Hh [b Hb]]. apply (apresent_grows (w_H W4) mem4 (ms_mem ms0) a MG2). apply (HPR4 a Ha Ho He).
  split; [exact Hh|]. exists b. pose proof (MEQ1 (Z_to_bv 64 a)) as E1. unfold mrestrict in E1. rewrite Hh in E1.
  rewrite E1. exact Hb. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept WL memL W4 (ms_mem ms0) a).
{ intros a Ha Ho He. split; [rewrite AV2, (KF3 a Ha Ho He); apply AV1|].
  apply rfl_wr_pres2. exact (PR2 a Ha Ho He). }
assert (HTB4 : In (T, ATABLE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | left; reflexivity]).
assert (HX4 : forall b, In b X -> In b (ablocks B ly4 S4)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | right; exact Hb]).
set (SA := T + 56 * Z.of_nat i).
assert (T10' : getr (ms_regs ms0) 10 = w64 SA).
{ rewrite T10, OLDa, E33 by lia. rewrite unsigned_lit_small by (unfold p; lia). unfold SA, p, w64. f_equal. lia. }
assert (HSA8 : SA mod 8 = 0).
{ unfold SA. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 56 * Z.of_nat i) with ((2 * (T / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
pose proof HHELD as (Hpd1 & Hpd2 & _).
assert (HrqG : forall m, m <= req_size m) by (intros m; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (GX : forall b, In b (gse_blks e) -> In b X) by (intros b Hb; unfold X; apply in_or_app; left; exact Hb).
assert (OX : forall b, In b (aout_blks (gse_cap r0) outL) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (GA5 : garr8 SEGS (arm W4 (ms_mem ms0)) SA (bzs (entry_bytes e))).
{ apply (garr8_frame SEGS (arm WL memL) (arm W4 (ms_mem ms0)) SA _); [unfold SA; unfold AENT in HG8; exact HG8|].
  intros x Hx. rewrite (rfl_len_entry e Hpd1 Hpd2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
  apply (KB T ATABLE x (or_introl eq_refl)). change (req_size ATABLE) with 896. unfold SA in Hx. lia. }
assert (AW5 : awr W4 (ms_mem ms0) SA AENT).
{ intros j Hj. apply (apresent_writable SEGS).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ T ATABLE HAR5 HTB4) as (_ & _ & _ & _ & HP & _).
  change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (SA + j) ltac:(unfold SA, AENT in *; lia))). }
assert (HELD5 : aheld_ok B ly4 S4 W4 (ms_mem ms0) e).
{ apply (rfl_aheld_ok_kept lyL SL WL memL ly4 S4 W4 (ms_mem ms0) e HHELD).
  - intros b Hb. exact (HX4 b (GX b Hb)).
  - intros b m x Hb Hx. apply (KB b m x (or_intror (GX _ Hb))). pose proof (HrqG m). lia. }
assert (AK5 : akept WL memL W4 (ms_mem ms0) (aout_fp B RG (gse_cap r0) outL)).
{ assert (GSL : forall a, inG (G_SL B RG) a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (intros a Ha; exact (conj (proj1 (HG a (HSLG a Ha))) (proj1 (proj2 (HG a (HSLG a Ha)))))).
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
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia]))) as [Hi1 _].
    unfold arm. apply rf_writable_of_seg; [|exact (HWSEGE a Har)].
    apply (hidden_not_img SEGS W4). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia.
  - destruct (Z.eqb_spec (gse_cap r0) 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Har.
    assert (HobX : In (outL, gse_cap r0) X)
    by (apply OX; unfold aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); left; reflexivity).
    assert (Hrq : req_size (gse_cap r0) = gse_cap r0) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); reflexivity).
    split; [apply (KB outL (gse_cap r0) a (or_intror HobX)); lia|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ outL (gse_cap r0) HAR5 (HX4 _ HobX)) as (_ & _ & _ & _ & HP & _).
    exact (proj1 (HP a ltac:(lia))). }
assert (AOUT5 : aout_at B RG ly4 S4 W4 (ms_mem ms0) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL)
by (exact (aout_at_kept B RG lyL SL WL memL ly4 S4 W4 (ms_mem ms0) _ _ mx _ _ outL HOUT AK5 (fun b Hb => HX4 b (OX b Hb)))).
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
(* rf_spec_x's peak is rf_pk = 5 (W8Entry-2's composed constant): gestures_end's own premise constant gse_pk = 4,
   plus the +1 an earlier send round leaves in g_out's class; 5 is the stronger premise, so this narrows it by
   cnt_ok_pk_mono *)
(* the room round: at S4 the free only removed a block and the loop head is at most one above the entry (HCL), so
   every callee peak up to 4 fits under the entry's 5 (HCNT5g); gestures_end's gse_pk = 4 is the tight instance *)
assert (HCNT5g : forall pk : (Z -> bool) -> nat, (forall P, (pk P <= 4)%nat) -> cnt_ok_pk RP pk (ablocks B ly4 S4)).
{ intros pk Hpk. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P) as H1. pose proof (ReplyCnt.acnt_perm P _ _ HPM4) as H2. rewrite ReplyCnt.acnt_app in H2.
  pose proof (Hpk P) as H3. unfold rf_pk. cbv beta. lia. }
assert (HCNT5 : cnt_ok_pk RP gse_pk (ablocks B ly4 S4)) by (apply HCNT5g; intros P; unfold gse_pk; lia).
pose proof (ajournal_gx_inner_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (memS5 & HJin5 & HagS5).
assert (Usp5 : spZ (ms_regs ms0) = sp0 + -96) by (unfold spZ in Ksp |- *; rewrite T2, OLDa, (EE 2%nat 2%bv eq_refl) by lia; lia).
assert (T3' : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite T3, OLDa, (EE 3%nat 3%bv eq_refl), K3 by lia; exact HGP0).
assert (T4' : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite T4, OLDa, (EE 4%nat 4%bv eq_refl), K4 by lia; exact HTP0).
assert (HCH5 : exists ch1, achain ly4 (aview SEGS (w_H W4) (ms_mem ms0)) (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) ch1).
{ assert (K4S : forall a, sp0 - 96 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem ms0) a = aview SEGS (w_H WL) (ms_mem ms) a).
  { intros a Ha. rewrite AV2. exact (KF1 a ltac:(unfold ASTACK in RSTK0; lia) ltac:(lia)). }
  destruct (RDW (aview SEGS (w_H W4) (ms_mem ms0)) ltac:(intros a Ha; rewrite K4S by lia; apply AV1)) as [R8 R16].
  pose proof HJi4 as (_ & Hly4' & _). pose proof Hly4' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
  destruct (rfl_chain_call ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W4) (ms_mem ms0)) sp0 (s0Z regs) che (raZ regs)
    HchE HceilS HalE HtopS ltac:(intros a Ha; rewrite K4S by lia; apply KST; exact Ha)
    R8 R16 Hra4e) as [ch' Hch'].
  exists ch'. rewrite Usp5.
  replace (s0Z (ms_regs ms0)) with sp0.
  - replace (sp0 + -96) with (sp0 - 96) by lia. exact (achain_ly_top ly ly4 _ _ _ _ Etop4 Hch').
  - unfold s0Z. rewrite T8, OLDa, (EE 8%nat 8%bv eq_refl), K8 by lia. unfold w64.
    rewrite unsigned_lit_small by (unfold ASTACK in RSTK0; lia). reflexivity. }
destruct HCH5 as [ch1 HCH5].
eassert (HPRE5 : afn_pre_x SEGS B ARx GSE_STK ly4 S4 Hp4 W4 (ms_regs ms0) (ms_mem ms0) _ ch1).
{ eapply (afn_pre_x_at SEGS B PST ARx (RF_STK + 0) (sp0 + 0) (rf_FP T es cap out) ly S Hp W memS5 md [(0, fpos)]
    ly4 S4 Hp4 W4 (ms_mem ms0) _ _ (ms_regs ms0) GSE_STK (-96) ch1 HJin5).
  - rewrite Usp5. lia.
  - reflexivity.
  - lia.
  - unfold GSE_STK, GSE_FRAME. pose proof (Z.le_max_r GE_STK ASTACK). unfold ASTACK in *. lia.
  - unfold RF_STK, RF_FRAME. pose proof (Z.le_max_l GSE_STK ASTACK). lia.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1, unsigned_lit_small by lia. lia.
  - exact T3'.
  - exact T4'.
  - exact HCH5. }
assert (ROM4 : rom_view SEGS W4 mem4).
{ apply (acall_kept_rom_view_x SEGS B ARx LAWS lyL SL WL (ms_mem ms) W4 mem4 _ _ (rfl_bex e) ly4 S4 Hp4 md4
    (proj1 HJi4) (conj KF1 (conj KF2 (conj KF3 (conj KF4 (conj KF5 KF6)))))).
  - intros a Ha. destruct (HROMO a Ha) as (_ & H2 & H3 & _). split; [exact H3 | exact H2].
  - intros a Ha. rewrite AV1. exact (HROM a Ha). }
assert (ROM5 : rom_view SEGS W4 (ms_mem ms0)) by (intros a Ha; rewrite AV2; exact (ROM4 a Ha)).
assert (END5' : garr8 SEGS (arm W4 (ms_mem ms0)) (VAL A_lit_end5) (bzs END5))
by (exact (rfl_end5_kept WL W4 memL (ms_mem ms0) HROM ROM5 HEND5)).
eapply SRr_bind.
{ exact (GSE W4 ly4 S4 Hp4 (ms_regs ms0) (ms_mem ms0) _ ch1 SA T e (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL
    (rf_eblks (skipn (Datatypes.S i) es) ++ rest) HPRE5 T10' HTB4 ltac:(unfold SA; lia) ltac:(unfold SA, AENT, ATABLE; lia) HSA8
    GA5 AW5 HELD5 AOUT5 HPG5 END5' ROM5 ROOM5 MO5 kr5 HRM4 HCNT5). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & out5 & -> & HJsl & HPsl & HPKsl & HMOsl & HRMsl & HPERMsl & HAOsl & HGAsl & HAWsl).
rewrite T1. fold r1 in HPERMsl, HAOsl.
(* ---- back from gestures_end: its journal (at G_SL) lifted to G and composed into the round's ---- *)
pose proof (ajournal_gx_G_mono_x SEGS B PST ARx (G_SL B RG) G 0 [] GSE_STK (spZ (ms_regs ms0)) _ ly4 S4 Hp4 W4 (ms_mem ms0) _ []
  ly5 S5 Hp5 W5 mem5 md5 k5 HSLG HJsl) as HJslG.
assert (FPC : forall a, inFP ((SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL)) a ->
  (inFP (rf_FP T es cap out) a /\ exists b n, In (b, n) (ablocks B ly4 S4) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly4 S4) a).
{ intros a Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
  - left. split.
    + replace a with (T + (a - T)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ T ATABLE (a - T));
      [apply in_or_app; left; unfold rf_tblk; rewrite (proj2 (Z.eqb_neq T 0) HT0); left; reflexivity
      | change (req_size ATABLE) with 896; unfold SA in Hf; lia].
    + exists T, ATABLE. split; [exact HTB4 | change (req_size ATABLE) with 896; unfold SA in Hf; lia].
  - destruct (inFP_ablocks_fp_inv _ a Hf) as (b & m & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. split.
      * replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [|lia].
        apply in_or_app; right; apply in_or_app; left. unfold rf_eblks. apply in_concat. exists (aentry_blks e).
        split; [apply in_map, nth_In; lia|]. change (aentry_blks e) with (rfl_bblk e ++ gse_blks e).
        apply in_or_app; right; exact Hin.
      * exists b, m. split; [exact (HX4 _ (GX _ Hin)) | exact Hr].
    + destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly S)) as [Hin0 | Hnin0].
      * left. split; [|exists b, m; split; [exact (HX4 _ (OX _ Hin)) | exact Hr]].
        (* a start block: the entry's permutation puts it in rf_FP, as `rest` cannot hold it beside the current
           g_out block (no live block is listed twice) *)
        assert (Hin1 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest))
        by (eapply Permutation_in; [exact HPERM0 | exact Hin0]).
        assert (Hin2 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
        { rewrite !app_assoc in Hin1. rewrite !app_assoc. apply in_app_or in Hin1. destruct Hin1 as [H1 | H1]; [exact H1|].
          exfalso. pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HNf.
          inversion HNf as [|y0 l0 _ HNXf]; subst y0 l0.
          exact (rfl_nodup_app_r _ _ (b, m) (rfl_nodup_tl _ _ (rfl_nodup_tl _ _ HNXf)) Hin H1). }
        replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [exact Hin2 | lia].
      * right. exists b, m. split; [exact (HX4 _ (OX _ Hin)) | split; [exact Hnin0 | exact Hr]]. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G RF_STK sp0 0 [] (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  ly4 S4 Hp4 W4 (ms_mem ms0) _ _ GSE_STK (spZ (ms_regs ms0)) 0 [] _ [] ly5 S5 Hp5 W5 mem5 md5 k5 HJ4 HJslG
  ltac:(rewrite Usp5; unfold RF_STK, RF_FRAME; pose proof (Z.le_max_l GSE_STK ASTACK); lia)
  ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia)
  ltac:(intros a Hf; exfalso; exact (inFP_nil a Hf)) HG FPC) as HJ6.
cbn [app] in HJ6.
(* what gestures_end kept: every image byte outside G_SL (its journal's image clause), and live blocks' bytes
   outside its footprint *)
pose proof (ajournal_gx_inner_x SEGS B PST ARx (G_SL B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS6 & HJin6 & HagS6).
pose proof HJin6 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (HFPC1 : ~ YI16.sink_open_fp ((SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL))).
{ apply sink_closed_pos. constructor; [cbn [fst]; unfold SA; lia|]. unfold ablocks_fp. apply Forall_map.
  apply Forall_forall. intros [b m] Hb. cbn [fst].
  assert (Hb4 : In (b, m) (ablocks B ly4 S4))
  by (apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [exact (HX4 _ (GX _ Hb)) | exact (HX4 _ (OX _ Hb))]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m HAR5 Hb4) as (_ & H4096 & _). lia. }
assert (KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem ms0) a).
{ intros a Ha Ho He Hps Hg. rewrite (G3 a Ha Ho He Hps (fp_spares_closed _ a HFPC1)).
  apply HagS6. rewrite unsigned_lit_small; [exact Hg|]. pose proof (Hsegs a Ha). unfold kLowMemEnd in *. lia. }
assert (NGN : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 1%nat).
assert (VN5a : val_mem SEGS (mrestrict (w_H W4) (ms_mem ms0)) (rg_nsrc RG) 4 n)
by (apply (val_mem_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem ms0)); [intros q _; apply AV2 | exact VN4]).
assert (VN5 : val_mem SEGS (mrestrict (w_H W5) mem5) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H W4) (w_H W5) (ms_mem ms0) mem5); [|exact VN5a].
  intros q Hq. destruct (HPLAIN (rg_nsrc RG + q) (Hnsrc (rg_nsrc RG + q) ltac:(lia))) as (Hq1 & Hq2 & Hq3).
  exact (KG _ Hq1 Hq2 Hq3 (PSTC _ (Hnsrc (rg_nsrc RG + q) ltac:(lia))) (NGN (rg_nsrc RG + q) ltac:(lia))). }
jafter_call_keep_pi HS 52%nat regs5 (mrestrict (w_H W5) mem5) HPsl [1]%nat HS6.
match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  apply (region_kept_val_at Ea _ _ 248%nat (rg_nsrc RG) 4 n);
  [change 248%nat with (A_OBJ 7); rewrite <- HV7; exact (HEIa (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | exact VN5a | exact VN5 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc Ea 52 (map (getr regs5) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (SHOK6 : sh_ok SEGS rfl_Bx [] Eb (mrestrict (w_H W5) mem5)) by constructor.
paj_run_tok_x RUN HS HJ6 SHOK6 Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. }
(* ---- the round's end state N (the last run wrote nothing): what RFI at i + 1 and RFX need ---- *)
lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem ms1)) |- _ => rename Hx into HFr3 end.
lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem ms1)) |- _ => rename Hx into MG3 end.
assert (MEQ3 : forall x, mrestrict (w_H W5) (ms_mem ms1) x = mrestrict (w_H W5) mem5 x).
{ intros x. apply HFr3. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
assert (AV3 : forall a, aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W5) mem5 a) by (intros a; apply aview_eq_of; apply MEQ3).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
(* the read-only view after gestures_end: its journal at G_SL keeps it (rom_out of G_SL) *)
assert (ROM6 : rom_view SEGS W5 mem5).
{ eapply (ajournal_gx_rom_view_x SEGS B PST ARx). all: first [exact LAWS | exact Hsegs | exact HJsl | exact HROMO | exact PSTR | exact ROM5]. }
assert (ROMN : rom_view SEGS W5 (ms_mem ms1)) by (intros a Ha; rewrite AV3; exact (ROM6 a Ha)).
assert (KNI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha Ho He Hps Hg. rewrite AV3, (KG a Ha Ho He Hps Hg), AV2, (KF3 a Ha Ho He). apply AV1. }
assert (RFW : forall a, inG rf_cells a -> writable_at SEGS (arm W5 (ms_mem ms1)) a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
  apply (hidden_not_img SEGS W5). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (KCELL : forall lo len, (forall x, lo <= x < lo + len -> inG rf_cells x /\ ~ inG (G_SL B RG) x) ->
  forall q, lo <= q < lo + len -> abyte_kept WL memL W5 (ms_mem ms1) q).
{ intros lo len Hc q Hq. destruct (Hc q Hq) as [Hq1 Hq2]. destruct (HPLAIN q Hq1) as (Hi1 & Ho1 & He1).
  split; [exact (KNI q Hi1 Ho1 He1 (PSTC q Hq1) Hq2) | intros _; exact (RFW q Hq1)]. }
assert (NGL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 0%nat).
assert (NGG : forall a, GL <= a < GL + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 3%nat).
assert (NGS : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 12%nat).
assert (NGC : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 13%nat).
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 1%nat _ 12 a eq_refl Ha)).
assert (ICS : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 4%nat _ 4 a eq_refl Ha)).
assert (IGL : forall a, GL <= a < GL + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 6%nat _ 4 a eq_refl Ha)).
assert (VNN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HNS]. intros q Hq.
  exact (proj1 (KCELL (rg_nsrc RG) 4 (fun x Hx => conj (Hnsrc x Hx) (NGN x Hx)) (rg_nsrc RG + q) ltac:(lia))). }
assert (VSN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HSRC]. intros q Hq.
  exact (proj1 (KCELL (rg_src RG) 8 (fun x Hx => conj (Hsrc x Hx) (NGS x Hx)) (rg_src RG + q) ltac:(lia))). }
assert (VCN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_capsrc RG) 4 16).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HCAP]. intros q Hq.
  exact (proj1 (KCELL (rg_capsrc RG) 4 (fun x Hx => conj (ICS x Hx) (NGC x Hx)) (rg_capsrc RG + q) ltac:(lia))). }
assert (WNN : awr W5 (ms_mem ms1) (rg_nsrc RG) 4) by (intros j Hj; exact (RFW _ (Hnsrc (rg_nsrc RG + j) ltac:(lia)))).
assert (WSN : awr W5 (ms_mem ms1) (rg_src RG) 8) by (intros j Hj; exact (RFW _ (Hsrc (rg_src RG + j) ltac:(lia)))).
assert (WCN : awr W5 (ms_mem ms1) (rg_capsrc RG) 4) by (intros j Hj; exact (RFW _ (ICS (rg_capsrc RG + j) ltac:(lia)))).
assert (LKN : alock_at RG W5 (ms_mem ms1) true).
{ apply (alock_at_kept RG WL memL W5 (ms_mem ms1) true HLK). intros r [<- | []] a Har. cbn [fst snd] in Har.
  exact (KCELL (rg_lock RG) 12 (fun x Hx => conj (ILK x Hx) (NGL x Hx)) a Har). }
assert (GLN : exists lst, val_mem SEGS (arm W5 (ms_mem ms1)) GL 4 lst).
{ destruct HGLv as [lst Hl]. exists lst. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact Hl].
  intros q Hq. exact (proj1 (KCELL GL 4 (fun x Hx => conj (IGL x Hx) (NGG x Hx)) (GL + q) ltac:(lia))). }
assert (GLW : awr W5 (ms_mem ms1) GL 4) by (intros j Hj; exact (RFW _ (IGL (GL + j) ltac:(lia)))).
assert (HTBN : In (T, ATABLE) (ablocks B ly5 S5)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | left; reflexivity]).
(* the round's own stack frame [sp0 - 96, sp0) and the fake frame [F, F + 64) are kept: the callees run below
   sp0 - 96, and their journals keep every frame byte outside their footprints *)
pose proof HJi as (_ & HlyL & _ & _ & _ & HfrL & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJi4 as (_ & Hly4 & _).
assert (EFL : frame_addr lyL 0 fpos = F).
{ destruct HlyL as (_ & _ & _ & _ & _ & EF & _). unfold F, frame_addr. first [rewrite EF | rewrite <- EF]; reflexivity. }
assert (EF4 : frame_addr ly4 0 fpos = F).
{ destruct Hly4 as (_ & _ & _ & _ & _ & EF & _). unfold F, frame_addr. first [rewrite EF | rewrite <- EF]; reflexivity. }
assert (HfinL : In (0, fpos) (frames SL)) by (rewrite HfrL; left; reflexivity).
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite HFR4; exact HfinL).
assert (RSTK : 96 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (KNF : forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (unfold ASTACK in RSTK; lia).
  rewrite AV3. rewrite (G1 a Hac ltac:(rewrite Usp5; lia)).
  rewrite HagS6; [rewrite AV2, (KF1 a Hac ltac:(lia)); apply AV1|].
  rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi1 _]. pose proof (Hsegs a Hi1).
  unfold kLowMemEnd in *. lia. }
assert (RSV : rf_saved W5 (ms_mem ms1) sp0 regs).
{ intros k0 Hk0. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact (HSV k0 Hk0)].
  intros q Hq. apply KNF. lia. }
pose proof (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARL HfinL) as (Fa & Fb & _). rewrite EFL in Fa, Fb.
change (fs_frame_bytes 0) with 64 in Fb.
assert (KNK : forall a, F <= a < F + 64 -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha.
  assert (Hfr4 : in_zr a (frame_rng ly4 (0, fpos))) by (unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF4; change (fs_frame_bytes 0) with 64; lia).
  assert (HfrL' : in_zr a (frame_rng lyL (0, fpos))) by (unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFL; change (fs_frame_bytes 0) with 64; lia).
  rewrite AV3. rewrite (G4 0 fpos a Hfin4 (or_introl Hfr4)).
  - rewrite HagS6.
    + rewrite AV2. rewrite (KF4 0 fpos a HfinL (or_introl HfrL')); [apply AV1|].
      intros (Hc & Hr). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyL SL _ WL memL mdL _ _ 0 fpos HARL Hin0 HfinL) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFL in D. change (fs_frame_bytes 0) with 64 in D. lia.
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi1 _].
      exact (frm_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ 0 fpos a HAR5 Hfin4 ltac:(rewrite EF4; change (fs_frame_bytes 0) with 64; lia) Hi1).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
    + pose proof (sep_block_frame_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ T ATABLE 0 fpos HAR5 HTB4 Hfin4) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF4 in D. change (req_size ATABLE) with 896 in D.
      change (fs_frame_bytes 0) with 64 in D. unfold SA in Hf. lia.
    + destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
      assert (Hin4' : In (b', m') (ablocks B ly4 S4))
      by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b' m' 0 fpos HAR5 Hin4' Hfin4) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF4 in D. change (fs_frame_bytes 0) with 64 in D. lia. }
assert (FLG : val_mem SEGS (arm W5 (ms_mem ms1)) (F + 56) 8 (flag_addr ly 0 fpos)).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HFLG]. intros q Hq. apply KNK. lia. }
(* the entries the loop has not reached keep their bytes and blocks: none of them is in gestures_end's footprint *)
pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HND4.
assert (HRN : forall b, In b (rf_eblks (skipn (Datatypes.S i) es) ++ rest) -> In b (ablocks B ly5 S5))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; right; exact Hb]).
assert (EX : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (KR : forall b m x, In (b, m) ((T, ATABLE) :: X) -> In (b, m) (ablocks B ly5 S5) ->
  ~ In (b, m) (gse_blks e ++ aout_blks (gse_cap r0) outL) -> b <= x < b + req_size m -> ~ (SA + 40 <= x < SA + 52) ->
  aview SEGS (w_H W5) (ms_mem ms1) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hin5 Hng Hx Hs. rewrite AV3.
  assert (Hin4 : In (b, m) (ablocks B ly4 S4)) by (destruct Hin as [<- | Hin]; [exact HTB4 | exact (HX4 _ Hin)]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m HAR5 Hin4) as (_ & Hb4096 & Hbceil & _).
  replace x with (b + (x - b)) by lia. rewrite (G2 b m (x - b) Hin4 Hin5 ltac:(lia)).
  - rewrite HagS6.
    + replace (b + (x - b)) with x by lia. exact (KB b m x Hin Hx).
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi2 _].
      exact (blk_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m (b + (x - b)) HAR5 Hin4 ltac:(lia) Hi2).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia|].
    destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
    assert (Hin4' : In (b', m') (ablocks B ly4 S4))
    by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
    assert (Hne : (b, m) <> (b', m')) by (intros Heq; apply Hng; rewrite Heq; exact Hin').
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m b' m' HAR5 Hin4 Hin4' Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ENTN : forall j, (Datatypes.S i <= j < length es)%nat ->
  garr8 SEGS (arm W5 (ms_mem ms1)) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
  awr W5 (ms_mem ms1) (T + AENT * Z.of_nat j) AENT /\
  aheld_ok B ly5 S5 W5 (ms_mem ms1) (nth j es rf_e0) /\
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
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m T ATABLE HAR5 (HX4 _ (EX _ Hb)) HTB4 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D. lia. }
  split; [|split; [|split]].
  - apply (garr8_frame SEGS (arm WL memL) (arm W5 (ms_mem ms1)) _ _ Gj). intros x Hx.
    rewrite (rfl_len_entry _ Pj1 Pj2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
    apply (KR T ATABLE x (or_introl eq_refl) HTBN NGT); [change (req_size ATABLE) with 896; unfold AENT in Hx; lia | unfold SA, AENT in *; lia].
  - intros q Hq. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly5 S5 _ W5 (ms_mem ms1) _ T ATABLE HAR6 HTBN) as (_ & _ & _ & _ & HP & _).
    change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
  - apply (rfl_aheld_ok_kept lyL SL WL memL ly5 S5 W5 (ms_mem ms1) _ Hj').
    + intros b Hb. apply HRN. apply in_or_app; left. apply EBj.
      change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
      apply in_or_app; right; exact Hb.
    + intros b m x Hb Hx.
      assert (HbE : In (b, m) (rf_eblks (skipn (Datatypes.S i) es))).
      { apply EBj. change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
        apply in_or_app; right; exact Hb. }
      pose proof (HrqG m) as Hm.
      apply (KR b m x (or_intror (EX _ HbE)) (HRN _ (in_or_app _ _ _ (or_introl HbE))) (NGj _ HbE)); [lia|].
      intros Hs. apply (NTj b m x HbE ltac:(lia)). unfold SA in Hs. lia.
  - destruct Bj as [Bj | (Bc & Bin)]; [left; exact Bj | right; split; [exact Bc|]].
    apply HRN. apply in_or_app; left. apply EBj. unfold aentry_blks.
    rewrite (proj2 (Z.eqb_neq (re_cap (nth j es rf_e0)) 0) ltac:(lia)). left; reflexivity. }
(* the stream, the blocks, presence, the meter and the model after round i *)
assert (AOUTN : aout_at B RG ly5 S5 W5 (ms_mem ms1) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5).
{ apply (aout_at_kept B RG ly5 S5 W5 mem5 ly5 S5 W5 (ms_mem ms1) _ _ mx _ _ out5 HAOsl).
  - intros r Hr a Har. split; [apply AV3 | apply (writable_at_grows SEGS _ _ a MG3)].
  - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]. }
assert (PERMN : Permutation (ablocks B ly5 S5)
  (rf_tblk T ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r1) out5 ++ rest)).
{ eapply Permutation_trans; [exact HPERMsl|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0). cbn [app].
  apply perm_skip. apply Permutation_app_swap_app. }
assert (APK : apres_kept B W mem W5 (ms_mem ms1)).
{ intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) mem5 (ms_mem ms1) a MG3). apply (HPKsl a Ha Ho He).
  apply (PR2 a Ha Ho He). exact (HPK a Ha Ho He Hpr). }
assert (MLE : mo_le MT S S5 (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)))
by (exact (mle_station MT S S4 S5 _ _ MLAW (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) HMOsl)).
assert (NNL : forall b, In b (ablocks B lyL SL) -> 0 <= snd b).
{ intros [bb mm] Hb. cbn [snd]. exact (BLKN lyL SL HpL WL memL mdL bb mm HARL Hb). }
assert (INL : forall b, In b ((T, ATABLE) :: rfl_bblk e ++ X) -> In b (ablocks B lyL SL))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM' | exact Hb]).
(* the room round's `- cap` threading (W_contract.v rf_room): the round frees the OLD g_out block (outL, gse_cap r0)
   and holds the new one (out5, gse_cap r1), so the rest's room grows only by gse_cap r1 - gse_cap r0; the old block's
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
assert (U23 : U Eb (SOff 23 1) = Z.of_nat i + 1).
{ apply (U_atom_off Eb 23 (Z.of_nat i) 1); [rewrite OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact H23 | lia | lia]. }
assert (U35 : U Eb (SOff 35 0) = n) by (apply (U_atom Eb 35 n); [rewrite OLDb, OLDa by lia; exact E35 | unfold n; lia]).
assert (RKF : forall regsF : bvmap 5 word,
  (forall r, In r [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv -> getr regsF r = getr regsL r) ->
  getr regsF 22 = ew Eb 289 -> rf_kept regs regsF sp0 F).
{ intros regsF HKN N22. unfold rf_kept.
  split; [unfold spZ in Ksp |- *; rewrite (HKN 2%bv ltac:(cbv; tauto)); exact Ksp|].
  split; [rewrite (HKN 3%bv ltac:(cbv; tauto)); exact K3|].
  split; [rewrite (HKN 4%bv ltac:(cbv; tauto)); exact K4|].
  split; [rewrite (HKN 26%bv ltac:(cbv; tauto)); exact K26|].
  split; [rewrite (HKN 27%bv ltac:(cbv; tauto)); exact K27|].
  split; [rewrite (HKN 8%bv ltac:(cbv; tauto)); exact K8|].
  split; [rewrite (HKN 18%bv ltac:(cbv; tauto)); exact K18|].
  split; [rewrite (HKN 19%bv ltac:(cbv; tauto)); exact K19|].
  split; [rewrite (HKN 20%bv ltac:(cbv; tauto)); exact K20|].
  split; [rewrite (HKN 21%bv ltac:(cbv; tauto)); exact K21|].
  rewrite N22. change 289%nat with (A_HI 9). exact (img_env_atomP Eb (A_HI 9) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)). }
(* the branch and the jump to its target write nothing: every fact above carries to the final memory *)
assert (FIN : forall m, (forall a, aview SEGS (w_H W5) m a = aview SEGS (w_H W5) (ms_mem ms1) a) ->
  mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) m) ->
  rf_saved W5 m sp0 regs /\
  val_mem SEGS (arm W5 m) (F + 56) 8 (flag_addr ly 0 fpos) /\
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
  assert (KF : forall a, abyte_kept W5 (ms_mem ms1) W5 m a)
  by (intros a; split; [apply AVF | apply (writable_at_grows SEGS _ _ a MGF)]).
  split; [intros k0 Hk0; apply (val_mem_kept SEGS (w_H W5) (w_H W5) (ms_mem ms1) m); [intros q _; apply AVF | exact (RSV k0 Hk0)]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact FLG]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VNN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WNN]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VSN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WSN]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VCN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WCN]|].
  split.
  { intros j Hj. destruct (ENTN j Hj) as (G1' & A1' & H1' & B1'). split; [|split; [|split]].
    - apply (akept_garr8 W5 (ms_mem ms1)); [intros x _; apply KF | exact G1'].
    - apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact A1'].
    - exact (rfl_aheld_ok_mem ly5 S5 W5 (ms_mem ms1) W5 m _ H1' AVF).
    - exact B1'. }
  split; [apply (alock_at_kept RG W5 (ms_mem ms1) W5 m true LKN); intros r _ a _; apply KF|].
  split; [apply (aout_at_kept B RG ly5 S5 W5 (ms_mem ms1) ly5 S5 W5 m _ _ mx _ _ out5 AOUTN);
    [intros r _ a _; apply KF
    | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]]|].
  split; [destruct GLN as [lst Hl]; exists lst; apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact Hl]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact GLW]|].
  intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) (ms_mem ms1) m a MGF). exact (APK a Ha Ho He Hpr). }
psrr_branch_tok RUN BR HS SHOK6 Bspan.
- (* i + 1 < |es|: back to the loop head, RFI at i + 1 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U23, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U23, ?U35; unfold n; lia). rewrite U23, U35 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x RUNTO HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 360).
  { apply awr_ok_x_of0. awr_ok_tac. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem ms1) a)
  by (intros a; apply aview_eq_of; apply Hx; intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & FLGF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  assert (ROMF : rom_view SEGS W5 (ms_mem msF)) by (intros a Ha; rewrite AV4; exact (ROMN a Ha));
  assert (E5F : garr8 SEGS (arm W5 (ms_mem msF)) (VAL A_lit_end5) (bzs END5))
  by (exact (rfl_end5_kept WL W5 memL (ms_mem msF) HROM ROMF HEND5));
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25.
  pmkst HS.
  apply (IH regs ly S Hp W mem md T es c O mx no cap out rest fpos (Datatypes.S i) ly5 S5 Hp5 W5); [lia | exact HCTXF | exact HCNT0 |].
  assert (RC : gse_c (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (RO : gse_O (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_cap r1) by (rewrite RUNS; reflexivity).
  refine (ex_intro _ _ (ex_intro _ out5 (ex_intro _ (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) _))).
  rewrite RC, RO, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact (RKF _ HKN2 N22)|].
  split; [exact HF0|].
  split; [rewrite N23, OLDb, OLDa, (EE 23%nat 23%bv eq_refl), H23 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N24, OLDb, OLDa, (EE 24%nat 24%bv eq_refl), H24 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N25; change 290%nat with (A_HI 10); exact (img_env_atomP Eb (A_HI 10) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia))|].
  split; [exact RSVF|]. split; [exact FLGF|].
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
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U23, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U23, ?U35; unfold n; lia). rewrite U23, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Hlast : Datatypes.S i = length es) by (unfold n in Hc; lia).
  paj_run_to_tok_x RUNTO HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 424).
  { apply awr_ok_x_of0. awr_ok_tac. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem ms1) a)
  by (intros a; apply aview_eq_of; apply Hx; intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & FLGF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (22%bv : bv 5) N22.
  pmkst HS.
  assert (SK0 : skipn (Datatypes.S i) es = []) by (rewrite Hlast; apply skipn_all).
  assert (FA : firstn (Datatypes.S i) es = es) by (rewrite Hlast; apply firstn_all).
  rewrite SK0 in HSP, PERMN. cbn [rf_cost rf_eblks concat map app] in HSP, PERMN. rewrite FA in RUNS.
  assert (RC : gse_c (rf_run c O mx no cap es) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (RO : gse_O (rf_run c O mx no cap es) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap es) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap es) = gse_cap r1) by (rewrite RUNS; reflexivity).
  apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest fpos ly5 S5 Hp5 W5).
  refine (ex_intro _ _ (ex_intro _ out5 _)).
  rewrite RC, RO, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact (RKF _ HKN2 N22)|].
  split; [exact HF0|].
  split; [exact RSVF|]. split; [exact FLGF|].
  split; [exact VNF|].
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
(* RF-LOOP-END *)

(* YCbq.v:2602 region_kept_stack_aj over YCbqG.v's journal ajournal_x (no kit twin; the same proof: it reads only
   the journal's stack presence and stack geometry and the call's acall_kept frame clause) *)
Lemma rf_region_kept_stack_aj_x : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; zlia.
- intros _. apply (apresent_writable SEGS). apply Hpres. zlia.
Qed.
(* speed (a Theorem Labs lane): in the three window checks at the blez (the run to it, and the two runs from it) the first
   alternative is exfalso; clear - Hr; lia, which closes the empty-window regions from Hr alone instead of running lia
   over the whole entry-segment context *)
(* The entry segment: from relay_finish's entry through the ASan fake-frame seat, the mutex lock and the blez on
   g_nsrc, to the tail X (no source) or the loop head L at round 0.  The two later segments arrive as hypotheses
   (rf_tail : rf_tail_stmt above; rf_loop : rf_tail_stmt -> rf_loop_stmt), so pb_relay_finish_h is their composition. *)
Lemma rf_entry_seg : rf_tail_stmt -> rf_loop_stmt -> rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX A_relay_finishP.
Proof.
intros TAIL LOOP.
unfold rf_spec_x. intros W ly S Hp regs mem md ch T es c O mx no cap out rest
HPRE Hal32 HCNT HGTU0 HLOCK HREL HGLv HGLw HOUT HPERM HEND5 HROM HG1 HG2 HG3 HROOM HTOPR HCTX HMOK kr HRMe HCNTe.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rf_entry W ly S Hp regs mem md ch HPRE Hal32 HGTU0) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
(* HSEPG stays folded (zseps is opaque to lia); a separation is picked with zsep_pick right where it is used and
   cleared after: every explicit disjunction left in the context multiplies the cost of each later lia. *)
(* every block of the footprint is a live block of the caller, hence positive: the sink's own word is not in it *)
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
assert (WS : RF_STK = 16704) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the prologue writes no global: it runs on the donor's journal from the entry memory, which is packed into the
   ajournal_gx with gagree_refl when the first global is written (W6's form, W_relay_instance_gone.v:346) *)
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RF_STK (rf_FP T es cap out) ly S Hp W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs rf_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rf_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_relay_finishP) with (Z_to_bv 64 A_relay_finishP). unfold A_relay_finishP, A_relay_finish.
paj_run_tok_x RUN0 HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
pose proof (palf_uar_img B TLF) as HuR.
assert (IGTU : forall x, GTU <= x < GTU + 1 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 0%nat GTU 1 x eq_refl Hx)).
pose proof (HPLAIN GTU ltac:(apply IGTU; lia)) as (HGTUi & HGTUo & HGTUe).
pose proof (proj1 (Forall_forall _ _) HIG (GTU, 1) ltac:(left; reflexivity)) as HGTUb. cbn [fst snd] in HGTUb.
(* the g_thread_up byte keeps its value across the prologue run (which writes only the frame) *)
assert (KG1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) GTU 1 0).
{ apply (keep_vm_frame E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) GTU 1 0 HFr ltac:(lia) ltac:(cbn; lia)); [|exact HGTU0].
  intros x Hx (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    revert Hr; unfold RF_FRAME; clear - Hx Hslo Hshi H47 Hceil C1 C3 Hstk0 HGTUb; lia | ]).
  destruct Hin. }
(* the call to __asan_stack_malloc_0 (64): the fake frame *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 0 ASM0 ltac:(lia)
  W rg mm RF_STK (spZ regs)
  (rf_FP T es cap out) ly S Hp W mem md [] ly S Hp _ 0 (-96) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPRS & HKR & HFS).
(* the room round: the seat's state is a set_fs of S, so rp_RPF carries the spec's room to it (the lock keeps it) *)
assert (HRM2 : rp_RM RP S2 (Z.to_nat (rf_cost MT_rk c O mx no cap es) + kr))
by (destruct HFS as (f & ->); exact (rp_RPF RP _ _ _ HRMe)).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (proj1 (proj2 (proj2 HK))) as HK3.
assert (KG2 : val_mem SEGS (mrestrict (w_H W) mem2) GTU 1 0)
by (apply (keep_vm_img W W (ms_mem ms) mem2 GTU 1 0 HK3 IGTU KG1)).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
  - eapply rf_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 3) GTU 1 0);
    [rewrite (HEI (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact HV3 | exact KG1 | exact KG2 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rf_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0's new atom), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 38%nat 33%nat 512%nat 0 F FL HS eq_refl ltac:(vm_compute; reflexivity)
RF' E33a ltac:(lia) ltac:(lia) ltac:(left; reflexivity) HFal ltac:(lia) ltac:(change (fs_frame_bytes 0) with 64; lia)
ltac:(lia)
ltac:(intros a Ha; exact (proj1 (HFpres a ltac:(change (fs_frame_bytes 0) with 64 in Ha; lia))))
ltac:(intros i Hi; unfold shadow_addr; rewrite <- SB_SHADOW_OFF;
exact (proj1 (HFSpres i ltac:(change (fs_frame_bytes 0 / 8) with 8 in Hi; lia))))
ltac:(change (fs_frame_bytes 0) with 64; exact Hflag)
ltac:(change (fs_frame_bytes 0) with 64; exact Hz)) as HS3.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS3.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL)
by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rf_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E33a).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as Dq; rewrite HFal in Dq; lia).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as Dm. rewrite HFal, Z.add_0_r in Dm. rewrite Dm at 1.
  replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by exact (HEIb (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U244 : bv_unsigned (ew Eb 244) = GTU) by (rewrite <- HV3; exact (HEIb (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (U273 : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by exact (HEIb (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 32)).
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFimg, HFapp.
pose proof (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, ff_fregion, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U38, U2b, U241, U242, U244, U273, U32b;
repeat split; lia) ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64;
rewrite U513, U38, U2b, U241, U242, U244, U273, U32b; unfold SB; repeat split; lia)) as HS4.
clear HS HS3. rename HS4 into HS. unfold ff_seated, ff_facts_ss, ff_fregion, ff_sregion in HS. norm_ss HS.
(* the frame header and the shadow poison, the g_thread_up test and the store of the frame pointer: a plain run
   (the token run keeps its windows off the shadow); it ends at the call to pthread_mutex_lock *)
paj_run_shc_x RUNP RUNC HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
    first [ lia
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
(* the call to pthread_mutex_lock (&g_lock) *)
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md
  _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed _ a HFPC)). }
pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a)
by (intros a Ha; exact (in_rf_cell 1%nat (rg_lock RG) 12 a eq_refl Ha)).
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as HLKb. cbn [fst snd] in HLKb.
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
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
assert (LKtb : aview SEGS (w_H W) (ms_mem ms0) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms0) = spZ regs + -96).
{ unfold spZ at 1. rewrite QSP, U2b. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP Eb (A_OBJ 6) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV6. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite QTP, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
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
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ2) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKx. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HKx))).
      apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
(* ---- back in relay_finish, the lock held.  The call wrote only the lock word and its own stack, so every
   region of the state at the call is kept; the state after it is the same one with the caller-saved atoms
   havoc'd (the GUIDE's jafter_call_keep_pi). ---- *)
zsep_pick HSEPG 0%nat 5%nat DL1. zsep_pick HSEPG 1%nat 5%nat DL2. zsep_pick HSEPG 2%nat 5%nat DL3.
zsep_pick HSEPG 3%nat 5%nat DL4. zsep_pick HSEPG 4%nat 5%nat DL5.
assert (KEEP3 : forall a,
  (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (spZ regs - 96 <= a < spZ regs) \/
  (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) \/ (VAL (A_OBJ 32) <= a < VAL (A_OBJ 32) + 8) \/
  (VAL (A_OBJ 1) <= a < VAL (A_OBJ 1) + 8) \/ (as_uar_cell B <= a < as_uar_cell B + 4) \/ (GTU <= a < GTU + 1) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply Hfr3.
  - clear -Ha HF4096 HFceil HFhigh HF8lo HF8hi HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB in *. lia.
  - clear -Ha HLKb DL1 DL2 DL3 DL4 DL5 HFimg HF8lo HF8hi HF4096 HFceil HFhigh Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB in *. lia.
  - clear -Ha HLKb HFapp HF4096 HFceil HFhigh HF8lo HF8hi HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB, ESTACK in *. lia. }
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 513%nat (SB + F / 8));
    [exact U513 | intros a Ha; apply KEEP3; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 38%nat F);
    [exact U38 | intros a Ha; apply KEEP3; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 2%nat (spZ regs));
    [exact U2b | intros a Ha; apply KEEP3; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 241%nat (VAL (A_OBJ 0)));
    [exact U241 | intros a Ha; apply KEEP3; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 273%nat (VAL (A_OBJ 32)));
    [exact U273 | intros a Ha; apply KEEP3; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 242%nat (VAL (A_OBJ 1)));
    [exact U242 | intros a Ha; apply KEEP3; right; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 32%nat (as_uar_cell B));
    [exact U32b | intros a Ha; apply KEEP3; right; right; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 244%nat GTU);
    [exact U244 | intros a Ha; apply KEEP3; right; right; right; right; right; right; right; lia | exact Hpres3]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* The token runner keeps its regions off the shadow span, so drop the fake frame's shadow region (the head of the
   state) for the rest of this segment: nothing from here to either cut point reads or writes it, and what the cut
   points say about it is semantic (W_relay_add.v:1013-1021 drops it the same way). *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 513%nat) _ _ _ _ _ :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx rest HS ltac:(vm_compute; apply submem_drop; apply submem_refl)
    ltac:(vm_compute; reflexivity)) as HS3
end end.
clear HS. rename HS3 into HS. norm_ss HS.
(* ... and the fake frame itself read-only (an empty window): cells_safe_b asks every write window to be apart from
   the shadow span, and the fake frame's atom ranges over the whole app region.  Nothing of this segment writes it
   (W_relay_add.v:1022-1031 does the same before its own token run). *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 38%nat) ?lo ?hi ?wlo ?whi ?cs :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx (YP09.mkRegion (Some 38%nat) lo hi 0 0 cs :: rest) HS
    ltac:(vm_compute; apply submem_keep; [unfold subregion; cbn; split; [reflexivity|]; split; [lia|]; split; [lia|];
          split; [left; lia | auto] | apply submem_refl])
    ltac:(vm_compute; reflexivity)) as HS4
end end.
clear HS. rename HS4 into HS. norm_ss HS.
(* the env after the call: the caller-saved atoms are new, atoms 512 and 513 (the fake frame) are not *)
assert (HCL : length CLOB = 16%nat) by (vm_compute; reflexivity).
remember (YN3v.havoc Eb 66 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 66)%nat -> ew Ec m = ew Eb m)
by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (HIc : forall m, (82 <= m)%nat -> ew Ec m = ew Eb m)
by (intros m Hm; rewrite HEc; apply ew_havoc_above; rewrite length_map, HCL; lia).
assert (HAEc : env_agree 32 (Ereg regs rf_extra) Ec)
by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
(* the relay's count, as the walk finds it: |es| in both arms of ra_rel (T = 0 forces es = []) *)
assert (NS0 : val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr W mem (rg_nsrc RG) 4).
{ destruct HREL as [(HT0 & Hes0 & (_ & _ & Hv & Hw & _)) | (_ & _ & Hv & Hw & _)];
  [rewrite Hes0; cbn [length Z.of_nat]; split; [exact Hv | exact Hw] | split; [exact Hv | exact Hw]]. }
assert (IGB : forall a, inG rf_cells a -> 0x10000 <= a /\ a < 0x5fb000).
{ intros a Ha. unfold inG, rf_cells in Ha. apply Exists_exists in Ha. destruct Ha as ((lo, sz) & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) HIG (lo, sz) Hin) as Hbb. unfold in_zr in Hr.
  cbn [fst snd] in Hbb, Hr. lia. }
assert (KC3 : forall a, inG rf_cells a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnl. destruct (HPLAIN a Ha) as (Hi & Ho & He). destruct (IGB a Ha) as (Hb1 & Hb2).
  rewrite (Hfr3 a ltac:(lia) Hnl ltac:(clear -Hb1 Hb2 Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He (PSTC a Ha)). }
zsep_pick HSEPG 5%nat 6%nat DLN.
assert (NS3 : val_mem SEGS (arm W mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 (Z.of_nat (length es)));
  [intros k Hk; apply KC3; [apply (in_rf_cell 2%nat (rg_nsrc RG) 4 (rg_nsrc RG + k) eq_refl); lia | lia]
  | exact (proj1 NS0)]. }
assert (NSB : (length es <= 16)%nat).
{ destruct HREL as [(_ & Hes0 & _) | (_ & _ & _ & _ & _ & _ & Hle & _)]; [rewrite Hes0; cbn [length]; lia | exact Hle]. }
(* the g_nsrc cell as a region: the lw at 0x82440 reads it through the object atom (HV7) *)
pose proof (st_ok_pi_havoc_hi 514 Ec _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (YN3v.havoc Ec 514 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc_hi; [exact HEIc | cbv; lia]).
assert (OLDd : forall m, (m < 514)%nat -> ew Ed m = ew Ec m)
by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E514 : ew Ed 514 = Z_to_bv 64 (Z.of_nat (length es)))
by (rewrite HEd; exact (ew_havoc_new Ec 514 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rf_extra) Ed)
by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
clear HEd.
assert (U2d : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd, OLDc by lia; exact U2b).
assert (U38d : bv_unsigned (ew Ed 38) = F) by (rewrite OLDd, OLDc by lia; exact U38).
assert (U513d : bv_unsigned (ew Ed 513) = SB + F / 8) by (rewrite OLDd, HIc by lia; exact U513).
assert (U241d : bv_unsigned (ew Ed 241) = VAL (A_OBJ 0)) by (rewrite OLDd, HIc by lia; exact U241).
assert (U242d : bv_unsigned (ew Ed 242) = VAL (A_OBJ 1)) by (rewrite OLDd, HIc by lia; exact U242).
assert (U244d : bv_unsigned (ew Ed 244) = GTU) by (rewrite OLDd, HIc by lia; exact U244).
assert (U273d : bv_unsigned (ew Ed 273) = VAL (A_OBJ 32)) by (rewrite OLDd, HIc by lia; exact U273).
assert (U32d : bv_unsigned (ew Ed 32) = as_uar_cell B) by (rewrite OLDd, OLDc by lia; exact U32b).
assert (U248d : bv_unsigned (ew Ed (A_OBJ 7)) = rg_nsrc RG)
by (rewrite <- HV7; exact (HEId (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB7 : base_val Ed (Some (A_OBJ 7)) = rg_nsrc RG) by (cbn [base_val]; exact U248d).
zsep_pick HSEPG 0%nat 6%nat DN1. zsep_pick HSEPG 1%nat 6%nat DN2. zsep_pick HSEPG 2%nat 6%nat DN3.
zsep_pick HSEPG 3%nat 6%nat DN4. zsep_pick HSEPG 4%nat 6%nat DN5.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb.
cbn [fst snd] in HNSb.
pose proof (st_ok_pi_add_region Ed _ _
  (YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 514 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
        rewrite VB7; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        constructor; [|constructor];
        apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 514 0) (Z.of_nat (length es)));
        [cbn [sv_denot]; rewrite E514, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        rewrite Z.add_0_r; exact NS3)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
        let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U248d, ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d;
        revert DN1 DN2 DN3 DN4 DN5 HNSb HF4096 HFceil HFhigh HFimg HFapp HF8lo HF8hi
               HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; clear; intros;
        unfold SB in *; repeat split; lia)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
(* ---- THE TRANSPORT BLOCK: what both arms of the blez need of the memory, carried from the entry memory to the
   lock's return and from there to either arm's own memory. ---- *)
pose proof pa_img_range as Himg.
(* errno is a byte of G (it is in G_SL), so the image and the allocator's statics are decided for it *)
assert (HERRG : forall a, as_errno B <= a < as_errno B + 4 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros a Ha. destruct (HG a (HG2 a ltac:(unfold G_SL, inG;
    do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))) as (Hei & Heo & _).
  split; [exact Hei | exact Heo]. }
assert (HEO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (as_errno B + i)) (as_owned_static B))
  by (intros i Hi; exact (proj2 (HERRG (as_errno B + i) ltac:(lia)))).
(* ... hence not aowned, before the fake-frame seat and after it: what the seat's RAW frame clause asks *)
assert (HNOWN : forall a, as_errno B <= a < as_errno B + 4 ->
  ~ aowned B ly S a /\ ~ aowned B ly S2 a).
{ intros a Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
  split; [ exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) ly S Hp W (ms_mem ms) _ HARa HEO
                    (a - as_errno B) ltac:(lia))
         | exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) ly S2 Hp W mem2 md2 HARb HEO
                    (a - as_errno B) ltac:(lia)) ]. }
(* an image byte off the lock word keeps its view from the entry to the lock's return *)
assert (KIMGA : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps Hnl. pose proof (Hsegs a Hi) as Hlow.
  rewrite (Hfr3 a ltac:(clear -Hlow C5; lia) Hnl
    ltac:(clear -Hlow Hslo Hceil C1 C5 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He Hps). }
(* errno's four bytes keep their view across the whole prologue.  Across the fake-frame seat that is HKR, the
   seat's RAW frame clause (aj_stack_malloc_pres_at_raw): acall_kept's image clause excepts errno and cannot. *)
assert (KERR : forall a, as_errno B <= a < as_errno B + 4 ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) by
 (intros a Ha;
  pose proof (Himg a (proj1 (HERRG a Ha))) as Hb;
  zsep_pick HSEPG 5%nat 11%nat SE1;
  rewrite (Hfr3 a ltac:(clear -Hb; lia) ltac:(clear -Ha Hb SE1; lia)
    ltac:(clear -Hb Hslo Hceil C1 WS; unfold ESTACK; lia));
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(clear -Hb; lia)
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
        clear -Hr Hb HFimg HF8lo Hslo Hceil C1 WS; unfold SB in *; lia | ]);
      destruct Hin));
  rewrite (HKR a ltac:(clear -Hb; lia) (proj1 (HNOWN a Ha)) (proj2 (HNOWN a Ha))
    ltac:(clear -Hb Hslo Hceil C1 WS; unfold ESTACK; lia));
  apply (aview_kept_out E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) HFr a ltac:(clear -Hb; lia));
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    clear -Hr Hb Hslo Hceil C1 WS; unfold RF_FRAME in *; lia | ]);
  destruct Hin).
(* a byte of a live block keeps its view from the entry to the lock's return: no step of the prologue writes it
   (the runs write only the frame, the fake frame and its shadow; the two calls keep every block byte) *)
assert (KHEAP : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W) mem3 (p + i) = aview SEGS (w_H W) mem (p + i)) by
 (intros p n i Hin Hi;
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & _);
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n (p + i) HAR Hin ltac:(lia)) as Hxn;
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 _ W mem2 md2 p n 0 fpos HARb
    ltac:(rewrite Eab; exact Hin) Hfin2) as Hsep;
  unfold zdisjoint in Hsep; cbn [fst snd] in Hsep;
  change (fs_frame_bytes 0) with 64 in Hsep; fold F in Hsep;
  rewrite (Hfr3 (p + i) ltac:(clear -Hp4096 Hpceil Hi C1; lia)
    ltac:(intros Hl; apply Hxn; exact (proj1 (HPLAIN (p + i) (ILK (p + i) ltac:(lia)))))
    ltac:(clear -Hp4096 Hpceil Hi Hceil Hslo WS C1; unfold ESTACK; lia));
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 (p + i)
    ltac:(clear -Hp4096 Hpceil Hi C1; lia)
    ltac:(intros (r & Hin2 & Hr);
      lazymatch type of Hin2 with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin2 end;
      cbn [In] in Hin2;
      repeat (destruct Hin2 as [<- | Hin2];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
        first
        [ exact (fshadow_not_app F 8 p (req_size n) (p + i) ltac:(clear -HF4096; lia)
            ltac:(clear -HFceil C1; lia) Hpapp ltac:(clear -Hr; unfold SB in Hr; lia)
            ltac:(clear -Hi; lia))
        | clear -Hr Hp4096 Hpceil Hi Hsep Hceil Hslo WS C1; lia ] | ]);
      destruct Hin2));
  rewrite (proj1 (proj2 HK) p n i Hin Hi ltac:(intros []));
  apply (aview_kept_out E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) HFr (p + i)
    ltac:(clear -Hp4096 Hpceil Hi C1; lia));
  intros (r & Hin2 & Hr);
  lazymatch type of Hin2 with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin2 end;
  cbn [In] in Hin2;
  repeat (destruct Hin2 as [<- | Hin2];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    clear -Hr Hp4096 Hpceil Hi Hceil Hslo WS C1; lia | ]);
  destruct Hin2).
(* presence of image bytes, from the entry to the lock's return *)
assert (KPRES : forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a) by
 (intros a Hi Hpr; apply Hpres3; apply (apresent_grows (w_H W) mem2 (ms_mem ms0) a HG4);
  apply HPRS; [exact Hi | exact (apresent_grows (w_H W) mem (ms_mem ms) a HG0 Hpr)]).
(* ---- the carry: any later memory whose only write window is the frame [sp0 - 96, sp0) keeps the four transport
   facts and the rom_view.  Both arms of the blez pass their own run's frame_of and mem_grows here. ---- *)
assert (CARRY : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
  /\ (forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
  /\ (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
       aview SEGS (w_H W) m' (p + i) = aview SEGS (w_H W) mem (p + i))
  /\ (forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m' a)
  /\ rom_view SEGS W m') by
 (intros m' md' CK CG HARm;
  split;
  [ intros a Hi Ho He Hps Hnl; pose proof (Hsegs a Hi) as Hlow;
    rewrite (CK a ltac:(clear -Hlow C5; lia) ltac:(clear -Hlow C5 Hceil Hslo WS C1; lia));
    exact (KIMGA a Hi Ho He Hps Hnl)
  | split;
  [ intros a Ha; pose proof (Himg a (proj1 (HERRG a Ha))) as Hb;
    rewrite (CK a ltac:(clear -Hb; lia) ltac:(clear -Hb Hceil Hslo WS C1; lia));
    exact (KERR a Ha)
  | split;
  [ intros p n i Hin Hi;
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _);
    rewrite (CK (p + i) ltac:(clear -Hp4096 Hpceil Hi C1; lia)
      ltac:(clear -Hp4096 Hpceil Hi Hceil Hslo WS C1; lia));
    exact (KHEAP p n i Hin Hi)
  | split;
  [ intros a Hi Hpr; exact (apresent_grows (w_H W) mem3 m' a CG (KPRES a Hi Hpr))
  | intros a Ha;
    destruct (HROMO a Ha) as (HnG & Hpin & Hne & Hnh);
    assert (Hi : in_img SEGS a)
      by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]);
    assert (Hd : forall r : Z * Z, {in_zr a r} + {~ in_zr a r})
      by (intros r; unfold in_zr;
          destruct (Z_le_gt_dec (fst r) a); destruct (Z_lt_ge_dec a (fst r + snd r));
          [left; lia | right; lia | right; lia | right; lia]);
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno];
    [ exact (rom_pinned_view_x SEGS B ARx LAWS ly S2 Hp W m' md' a HARm (Hpin Hown))
    | pose proof (Hsegs a Hi) as Hlow;
      rewrite (CK a ltac:(clear -Hlow C5; lia) ltac:(clear -Hlow C5 Hceil Hslo WS C1; lia));
      rewrite (KIMGA a Hi Hno Hne (PSTR a Ha)
        ltac:(intros Hl; apply (HROMG a ltac:(left; unfold RF_G, inG; apply Exists_cons_hd;
              unfold in_zr; cbn [fst snd]; lia)); exact Ha));
      exact (HROM a Ha) ] ]]]]).
(* the four relay/listen cells this walk carries: image bytes, not allocator statics, not errno, off the lock word *)
assert (CELLOK : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
   \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) ->
   in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
   /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) by
 (intros a Ha;
  zsep_pick HSEPG 5%nat 6%nat L6; zsep_pick HSEPG 5%nat 7%nat L7;
  zsep_pick HSEPG 5%nat 8%nat L8; zsep_pick HSEPG 5%nat 10%nat L10;
  destruct Ha as [HA1 | [HA1 | [HA1 | HA1]]];
  [ destruct (HPLAIN a (in_rf_cell 2%nat (rg_nsrc RG) 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 3%nat (rg_src RG) 8 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 4%nat (rg_capsrc RG) 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 6%nat GL 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1) ];
  (split; [exact Hi1 | split; [exact Ho1 | split; [exact He1 | clear -HA1 L6 L7 L8 L10; lia]]])).
(* ... and none of them is a byte of the program statics PST (PSTC) *)
assert (CELLPST : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
   \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) -> ~ Exists (in_zr a) PST) by
 (intros a Ha; destruct Ha as [HA1 | [HA1 | [HA1 | HA1]]];
  [ exact (PSTC a (in_rf_cell 2%nat (rg_nsrc RG) 4 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 3%nat (rg_src RG) 8 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 4%nat (rg_capsrc RG) 4 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 6%nat GL 4 a eq_refl HA1)) ]).
(* the controller's cells of aout_at: the same four properties *)
assert (AOUTK : forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8)
   \/ (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8)
   \/ (rg_client RG <= a < rg_client RG + 4)
   \/ (rg_client_broken RG <= a < rg_client_broken RG + 1)
   \/ (rg_send_dead RG <= a < rg_send_dead RG + 1)
   \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
   in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
   /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) by
 (intros a Ha;
  zsep_pick HSEPO 0%nat 2%nat D2; zsep_pick HSEPO 0%nat 4%nat D4; zsep_pick HSEPO 0%nat 5%nat D5;
  zsep_pick HSEPO 0%nat 6%nat D6; zsep_pick HSEPO 0%nat 7%nat D7; zsep_pick HSEPO 0%nat 8%nat D8;
  zsep_pick HSEPO 0%nat 9%nat D9; zsep_pick HSEPO 0%nat 10%nat D10;
  zsep_pick HSEPO 2%nat 11%nat E2; zsep_pick HSEPO 4%nat 11%nat E4; zsep_pick HSEPO 5%nat 11%nat E5;
  zsep_pick HSEPO 6%nat 11%nat E6; zsep_pick HSEPO 7%nat 11%nat E7; zsep_pick HSEPO 8%nat 11%nat E8;
  zsep_pick HSEPO 9%nat 11%nat E9; zsep_pick HSEPO 10%nat 11%nat E10;
  destruct Ha as [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | HA1]]]]]]];
  [ destruct (HPLAINO a ltac:(left; lia)) as (Hi1 & Ho1 & He1)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E5; lia)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 3 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E6; lia)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 4 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E7; lia)
  | destruct (HG a (HG1 a ltac:(unfold RF_G, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4))
      by (exact (HG3 a ltac:(unfold RF_G, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
          unfold in_zr; cbn [fst snd]; lia)))
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E8; lia)
  | destruct (HPLAINO a ltac:(right; lia)) as (Hi1 & Ho1 & He1)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E10; lia) ];
  (split; [exact Hi1 | split; [exact Ho1 | split; [exact He1 |
     clear -HA1 D2 D4 D5 D6 D7 D8 D9 D10; lia]]])).
assert (RFE_EB : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat) by
 (intros e P1 P2; unfold entry_bytes; rewrite !length_app, P1, P2; cbn; reflexivity).
assert (RFE_KP : forall ks, length (key_ptrs ks) = (8 * length ks)%nat) by
 (intros ks; induction ks as [|k ks IH]; [reflexivity|];
  unfold key_ptrs in *; cbn [map concat length]; rewrite length_app, IH; cbn; lia).

assert (RFE_SPLIT : forall (l : list rentry), (forall e, In e l -> length (entry_bytes e) = 56%nat) ->
  forall j, (j < length l)%nat ->
  exists l1 l2, concat (map entry_bytes l) = l1 ++ entry_bytes (nth j l rf_e0) ++ l2 /\
                length l1 = (56 * j)%nat) by
 (induction l as [|e l IH]; intros Hl j Hj; [cbn [length] in Hj; lia|];
  destruct j as [|j];
  [ exists (@nil byte), (concat (map entry_bytes l)); cbn [concat map nth app]; split; reflexivity
  | cbn [length] in Hj;
    destruct (IH ltac:(intros x Hx; apply Hl; right; exact Hx) j ltac:(lia)) as (l1 & l2 & Heq & Hlen);
    exists (entry_bytes e ++ l1), l2; cbn [concat map nth];
    rewrite Heq, !app_assoc; split; [reflexivity|];
    rewrite length_app, Hlen, (Hl e ltac:(left; reflexivity)); lia ]).

assert (RFE_HELD : forall ly1 S1 (W1 : world SEGS) mem1 e,
  aentry_ok B ly1 S1 W1 mem1 e -> aheld_ok B ly1 S1 W1 mem1 e) by
 (intros ly1 S1 W1 mem1 e
    (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15);
  split; [exact Q3|]; split; [exact Q4|]; split; [exact Q11|]; split; [exact Q12|];
  split; [exact Q13|]; split; [exact Q14 | exact Q15]).
(* ---- the memory facts both arms need, at any later memory m' the carry covers ---- *)
assert (FAOUT : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  aout_at B RG ly S2 W m' c O mx no cap out) by
 (intros m' md' CK CG HARm;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (WIM : forall x, in_img SEGS x -> writable_at SEGS (arm W mem) x -> writable_at SEGS (arm W m') x)
    by (intros x Hix Hw; unfold arm in *; exact (writable_kept (w_H W) mem m' x (fun Hpr => KP x Hix Hpr) Hw));
  apply (aout_at_kept B RG ly S W mem ly S2 W m' c O mx no cap out HOUT);
  [ intros r Hr a Ha; unfold aout_fp in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr];
    [ cbn [fst snd] in Ha;
      first
      [ split; [ apply KE; clear -Ha; lia
               | intros Hw; exact (WIM a (proj1 (HERRG a ltac:(clear -Ha; lia))) Hw) ]
      | destruct (AOUTK a ltac:(clear -Ha; lia)) as (Hi1 & Ho1 & He1 & Hl1);
        split; [ exact (KI a Hi1 Ho1 He1 (PSTO a ltac:(clear -Ha; lia)) Hl1) | intros Hw; exact (WIM a Hi1 Hw) ] ] | ]);
    destruct (Z.eq_dec cap 0) as [Hc0 | Hc0];
    [ rewrite (proj2 (Z.eqb_eq cap 0) Hc0) in Hr; destruct Hr
    | rewrite (proj2 (Z.eqb_neq cap 0) Hc0) in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha;
      pose proof HOUT as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HAOB);
      assert (Hrs : req_size cap = cap)
        by (unfold req_size; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity);
      destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [clear -Hc' Hc0; lia|];
      split;
      [ replace a with (out + (a - out)) by (clear -Ha; lia);
        apply (KH out cap (a - out)); [exact HoIn | rewrite Hrs; clear -Ha; lia]
      | intros _; apply (apresent_writable SEGS);
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ out cap HARm ltac:(rewrite Eab; exact HoIn))
          as (_ & _ & _ & _ & Hpp & _);
        exact (proj1 (Hpp a ltac:(rewrite Hrs; clear -Ha; lia))) ] ]
  | intros b Hb; rewrite Eab; eapply Permutation_in; [apply Permutation_sym; exact HPERM|];
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb ]).

assert (FREST : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  alock_at RG W m' true
  /\ rom_view SEGS W m'
  /\ garr8 SEGS (arm W m') (VAL A_lit_end5) (bzs END5)
  /\ val_mem SEGS (arm W m') (rg_nsrc RG) 4 (Z.of_nat (length es))
  /\ (exists lst, val_mem SEGS (arm W m') GL 4 lst)
  /\ awr W m' GL 4
  /\ apres_kept B W mem W m'
  /\ rf_done ly S2 W m' T) by
 (intros m' md' CK CG HARm;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (WIM : forall x, in_img SEGS x -> writable_at SEGS (arm W mem) x -> writable_at SEGS (arm W m') x)
    by (intros x Hix Hw; unfold arm in *; exact (writable_kept (w_H W) mem m' x (fun Hpr => KP x Hix Hpr) Hw));
  assert (KCELL : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
     \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
    by (intros a Ha; destruct (CELLOK a Ha) as (Hi1 & Ho1 & He1 & Hl1); exact (KI a Hi1 Ho1 He1 (CELLPST a Ha) Hl1));
  assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 4 \/ rg_lock RG + 8 <= a < rg_lock RG + 12 ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
    by (intros a Ha; destruct (HPLAIN a (ILK a ltac:(clear -Ha; lia))) as (Hi1 & Ho1 & He1);
        exact (KI a Hi1 Ho1 He1 (PSTC a (ILK a ltac:(clear -Ha; lia))) ltac:(clear -Ha; lia)));
  split;
  [ split;
    [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_lock RG) 4 0);
      [intros k Hk; cbn in Hk; apply KLK; clear -Hk; lia | exact LK0]
    | split;
      [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 m' (rg_lock RG + 4) 4 16);
        [intros k Hk; cbn in Hk; apply CK;
         [clear -Hk HLKb; lia | clear -Hk HLKb Hceil Hslo WS C1; lia] | exact HLK3]
      | split;
        [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_lock RG + 8) 4 0);
          [intros k Hk; cbn in Hk; apply KLK; clear -Hk; lia | exact LK8]
        | intros i Hi; apply WIM;
          [exact (proj1 (HPLAIN (rg_lock RG + i) (ILK (rg_lock RG + i) ltac:(clear -Hi; lia))))
          | exact (LKW i Hi)] ] ] ]
  | split;
    [ exact KR
    | split;
      [ apply (garr8_frame SEGS (arm W mem) (arm W m') (VAL A_lit_end5) (bzs END5) HEND5);
        intros x Hx; unfold bzs in Hx; rewrite length_map in Hx;
        unfold arm; apply (mbyte_of_aview SEGS); rewrite (KR x (HE5R x Hx)); symmetry;
        exact (HROM x (HE5R x Hx))
      | split;
        [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_nsrc RG) 4 (Z.of_nat (length es)));
          [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact (proj1 NS0)]
        | split;
          [ destruct HGLv as (lst & Hlst); exists lst;
            apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' GL 4 lst);
            [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact Hlst]
          | split;
            [ intros i Hi; apply WIM;
              [exact (proj1 (CELLOK (GL + i) ltac:(clear -Hi; lia))) | exact (HGLw i Hi)]
            | split;
              [ intros a Hi1 Ho1 He1 Hpr; exact (KP a Hi1 Hpr)
              | split;
                [ intros i Hi; apply WIM;
                  [exact (proj1 (CELLOK (rg_nsrc RG + i) ltac:(clear -Hi; lia)))
                  | exact (proj2 NS0 i Hi)]
                | destruct HREL as [(HT0 & Hes0 & (VS0 & WS0 & _ & _ & VC0 & WC0)) | HRA];
                  [ left; split; [exact HT0|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_src RG) 8 0);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VS0]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_src RG + i) ltac:(clear -Hi; lia))) | exact (WS0 i Hi)]|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_capsrc RG) 4 0);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VC0]|];
                    intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_capsrc RG + i) ltac:(clear -Hi; lia))) | exact (WC0 i Hi)]
                  | pose proof HRA as (VST & WST & _ & _ & VCT & WCT & _ & HTin & _);
                    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & HT4096 & _);
                    right; split; [clear -HT4096; lia|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_src RG) 8 T);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VST]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_src RG + i) ltac:(clear -Hi; lia))) | exact (WST i Hi)]|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_capsrc RG) 4 16);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VCT]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_capsrc RG + i) ltac:(clear -Hi; lia))) | exact (WCT i Hi)]|];
                    rewrite Eab; exact HTin ] ] ] ] ] ] ] ] ]).
assert (FENT : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  forall j, (j < length es)%nat ->
    garr8 SEGS (arm W m') (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0)))
    /\ awr W m' (T + AENT * Z.of_nat j) AENT
    /\ aheld_ok B ly S2 W m' (nth j es rf_e0)
    /\ ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
        (0 < re_cap (nth j es rf_e0) /\
         In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly S2)))) by
 (intros m' md' CK CG HARm j Hj;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
      abyte_kept W mem W m' a)
    by (intros p n a Hin Hx; split;
        [ replace a with (p + (a - p)) by (clear -Hx; lia);
          apply (KH p n (a - p)); [exact Hin | clear -Hx; lia]
        | intros _; apply (apresent_writable SEGS);
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARm ltac:(rewrite Eab; exact Hin))
            as (_ & _ & _ & _ & Hpp & _);
          exact (proj1 (Hpp a Hx)) ]);
  destruct HREL as [(HT0 & Hes0 & _) | HRA]; [rewrite Hes0 in Hj; cbn [length] in Hj; clear -Hj; lia|];
  pose proof HRA as (_ & _ & _ & _ & _ & _ & Hle16 & HTin & Htabx & Hall & _);
  destruct Htabx as (tail & Htl & Htot & Hg);
  assert (Hlens : forall x, In x es -> length (entry_bytes x) = 56%nat)
    by (intros x Hx; destruct (proj1 (Forall_forall _ _) Hall x Hx) as (_ & _ & Hp1 & Hp2 & _);
        exact (RFE_EB x Hp1 Hp2));
  pose proof (proj1 (Forall_forall _ _) Hall (nth j es rf_e0) (nth_In es rf_e0 Hj)) as HEOK;
  pose proof (Hlens (nth j es rf_e0) (nth_In es rf_e0 Hj)) as HLe;
  destruct (RFE_SPLIT es Hlens j Hj) as (l1 & l2 & Heq & Hl1);
  rewrite Heq in Hg; rewrite <- !app_assoc in Hg; unfold bzs in Hg; rewrite !map_app in Hg;
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg; destruct Hg as (_ & Hg);
  rewrite length_map, Hl1 in Hg;
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg; destruct Hg as (Hg & _);
  rewrite Nat2Z.inj_mul in Hg; change (Z.of_nat 56) with 56 in Hg;
  assert (HTB : forall x, T <= x < T + ATABLE -> abyte_kept W mem W m' x)
    by (intros x Hx; apply (KBLK T ATABLE x HTin);
        change (req_size ATABLE) with 896; unfold ATABLE in Hx; clear -Hx; lia);
  split;
  [ unfold AENT, bzs; apply (garr8_frame SEGS (arm W mem) (arm W m') _ _ Hg);
    intros x Hx; rewrite length_map, HLe in Hx; unfold arm;
    apply (mbyte_of_aview SEGS); exact (proj1 (HTB x ltac:(clear -Hx Hj Hle16; unfold ATABLE; lia)))
  | split;
  [ intros i Hi; apply (proj2 (HTB (T + AENT * Z.of_nat j + i)
      ltac:(clear -Hi Hj Hle16; unfold ATABLE, AENT in *; lia)));
    apply (apresent_writable SEGS);
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & _ & _ & _ & Hpp & _);
    exact (proj1 (Hpp (T + AENT * Z.of_nat j + i)
      ltac:(clear -Hi Hj Hle16; change (req_size ATABLE) with 896; unfold AENT in *; lia)))
  | split;
  [ apply RFE_HELD; apply (aentry_ok_kept B ly S W mem ly S2 W m' (nth j es rf_e0) HEOK);
    [ intros r Hr a Ha; unfold aentry_fp in Hr;
      destruct HEOK as (_ & _ & _ & _ & _ & _ & HU & _ & _ & HBUF & _ & HHP & _ & _ & HKEYS);
      destruct (in_app_or _ _ _ Hr) as [Hr1 | Hr2];
      [ destruct (Z.eq_dec (re_cap (nth j es rf_e0)) 0) as [Hc0 | Hc0];
        [ rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hr1; destruct Hr1
        | rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hr1; destruct Hr1 as [<- | []];
          unfold gfp in Ha; cbn [fst snd] in Ha;
          destruct HBUF as [(Hc' & _) | (_ & Hbin & Hjk & _)]; [clear -Hc' Hc0; lia|];
          unfold bzs in Ha; rewrite length_map, length_app in Ha;
          apply (KBLK _ _ a Hbin);
          clear -Ha HU Hjk Hc0; unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); lia ]
      | destruct Hr2 as [<- | Hr3];
        [ unfold gfp in Ha; cbn [fst snd] in Ha;
          destruct HHP as [(Hz1 & Hks1) | (Hnz1 & Hbin & Hkh1 & Hkh2 & _)];
          [ rewrite Hks1 in Ha; cbn [key_ptrs map concat bzs length] in Ha; clear -Ha; lia
          | unfold bzs in Ha; rewrite length_map, RFE_KP in Ha;
            apply (KBLK _ _ a Hbin); unfold re_nheld in Hkh1;
            clear -Ha Hkh1 Hkh2; unfold req_size;
            destruct (Z.eqb_spec (re_kh (nth j es rf_e0)) 0); lia ]
        | apply in_map_iff in Hr3; destruct Hr3 as (k & <- & Hk);
          destruct (proj1 (Forall_forall _ _) HKEYS k Hk) as (Hkin & _ & _);
          unfold gfp in Ha; cbn [fst snd] in Ha;
          unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha;
          apply (KBLK _ _ a Hkin);
          clear -Ha; unfold req_size;
          destruct (Z.eqb_spec (Z.of_nat (length (key_text k)) + 1) 0); lia ] ]
    | intros b Hb; rewrite Eab;
      destruct HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _ & HHP & _ & _ & HKEYS);
      unfold aentry_blks in Hb;
      destruct (in_app_or _ _ _ Hb) as [Hb1 | Hb2];
      [ destruct (Z.eq_dec (re_cap (nth j es rf_e0)) 0) as [Hc0 | Hc0];
        [ rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hb1; destruct Hb1
        | rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hb1; destruct Hb1 as [<- | []];
          destruct HBUF as [(Hc' & _) | (_ & Hbin & _)]; [clear -Hc' Hc0; lia | exact Hbin] ]
      | destruct (in_app_or _ _ _ Hb2) as [Hb3 | Hb4];
        [ destruct (Z.eq_dec (re_hp (nth j es rf_e0)) 0) as [Hz0 | Hz0];
          [ rewrite (proj2 (Z.eqb_eq _ 0) Hz0) in Hb3; destruct Hb3
          | rewrite (proj2 (Z.eqb_neq _ 0) Hz0) in Hb3; destruct Hb3 as [<- | []];
            destruct HHP as [(Hz1 & _) | (_ & Hbin & _)]; [clear -Hz1 Hz0; lia | exact Hbin] ]
        | apply in_map_iff in Hb4; destruct Hb4 as (k & <- & Hk);
          exact (proj1 (proj1 (Forall_forall _ _) HKEYS k Hk)) ] ] ]
  | destruct HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _);
    destruct HBUF as [(Hc0 & Hb0 & _) | (Hcp & Hbin & _)];
    [ left; split; [exact Hc0 | exact Hb0]
    | right; split; [exact Hcp | rewrite Eab; exact Hbin] ] ]]]).
(* the run to the blez: the auipc of g_nsrc's hi slot and the load of g_nsrc *)
assert (SHOKd : sh_ok SEGS Bx rf_SH0 Ed (mrestrict (w_H W) mem3)) by (unfold sh_ok, rf_SH0; constructor).
paj_run_tok_x RUN HS HJX3 SHOKd Bspan.
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
(* the value the blez compares: g_nsrc is |es|, loaded as a signed 4-byte cell *)
assert (HNU : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 514 0))) = Z.of_nat (length es)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 514 0))) with (U Ed (SOff 514 0)).
  rewrite (U_atom Ed 514 (Z.of_nat (length es)) E514 ltac:(lia)). apply sx32_small. lia. }
assert (HNS : bv_signed (sv_denot Ed (SExt true 32 (SOff 514 0))) = Z.of_nat (length es))
by (rewrite bv_signed_small by (rewrite HNU; lia); exact HNU).
assert (HZ0 : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity.
(* the blez: g_nsrc is |es| and never negative, so it is taken exactly when the relay has no source *)
psrr_branch_tok RUN BR HS SHOKd Bspan.
-
(* ---- no source: the table is empty and the loop is skipped; run to the tail at 0x1a8 ---- *)
cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
apply Bool.negb_true_iff, Z.ltb_ge in Hc.
assert (Hnil : es = []) by (destruct es as [|e es']; [reflexivity | cbn [length] in Hc; lia]).
paj_run_to_tok_x RUNTO HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x1a8).
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia ]
  | ]).
  destruct Hin. }
pmkst HS.
(* ---- the cut state X at 0x1a8: the run from the blez wrote only the frame, so the transport block carries ---- *)
assert (CK1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms2) x = aview SEGS (w_H W) mem3 x).
{ intros x Hx Hn.
  rewrite (aview_kept_out Ed _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)).
  exact (aview_kept_out Ed _ (w_H W) mem3 (ms_mem ms1) HFr1 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)). }
assert (CG1 : mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms2)))
  by (intros y Hy; exact (HG6 y (HG5 y Hy))).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARm.
pose proof (FAOUT (ms_mem ms2) _ CK1 CG1 HARm) as AOUTm.
destruct (FREST (ms_mem ms2) _ CK1 CG1 HARm) as (LKm & ROMm & E5m & NSm & GLvm & GLwm & PRESm & DONEm).
(* the registers the tail inherits *)
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (U512d : bv_unsigned (ew Ed 512) = FL) by (rewrite OLDd, HIc by lia; exact U512).
assert (U289d : bv_unsigned (ew Ed 289) = VAL (A_HI 9))
  by exact (HEId (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (EWD : forall (k : nat) (r : bv 5), (k < 34)%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot Ed (SOff k 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros k r Hk Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite OLDd, OLDc, OLDb, OLDa by lia; rewrite (EE k r Hr); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_region_nth Ed _ _ 2%nat _ HS eq_refl) as HRf.
pose proof (st_ok_pi_region_nth Ed _ _ 1%nat _ HS eq_refl) as HRF38.
cbn [ms_mem restrict] in HRf, HRF38.
assert (RSAV : rf_saved W (ms_mem ms2) (spZ regs) regs) by
 (intros i Hi;
  destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 0) with (spZ regs + (-88)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-88) 8%N (SOff 25 0)
         (bv_unsigned (getr regs 25%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 25%nat 25%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 25%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 1) with (spZ regs + (-80)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-80) 8%N (SOff 24 0)
         (bv_unsigned (getr regs 24%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 24%nat 24%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 24%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 2) with (spZ regs + (-72)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-72) 8%N (SOff 23 0)
         (bv_unsigned (getr regs 23%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 23%nat 23%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 23%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 3) with (spZ regs + (-64)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-64) 8%N (SOff 22 0)
         (bv_unsigned (getr regs 22%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 22%nat 22%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 22%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 4) with (spZ regs + (-56)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-56) 8%N (SOff 21 0)
         (bv_unsigned (getr regs 21%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 21%nat 21%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 21%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 5) with (spZ regs + (-48)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-48) 8%N (SOff 20 0)
         (bv_unsigned (getr regs 20%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 20%nat 20%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 20%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 6) with (spZ regs + (-40)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-40) 8%N (SOff 19 0)
         (bv_unsigned (getr regs 19%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 19%nat 19%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 19%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 7) with (spZ regs + (-32)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-32) 8%N (SOff 18 0)
         (bv_unsigned (getr regs 18%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 18%nat 18%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 18%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 8) with (spZ regs + (-24)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-24) 8%N (SOff 9 0)
         (bv_unsigned (getr regs 9%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 9%nat 9%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 9%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 9) with (spZ regs + (-16)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-16) 8%N (SOff 8 0)
         (bv_unsigned (getr regs 8%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 8%nat 8%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 10) with (spZ regs + (-8)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-8) 8%N (SOff 1 0)
         (bv_unsigned (getr regs 1%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 1%nat 1%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | exfalso; clear -Hi; lia ] ] ] ] ] ] ] ] ] ] ]).
(* ---- RFX ---- *)
apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest fpos ly S2 Hp W (ms_regs ms2) (ms_mem ms2) _).
unfold RFX. exists 0, out.
change (frame_addr ly 0 fpos) with F. change (flag_addr ly 0 fpos) with FL.
split; [exact HJX3|].
split.
{ split; [exists ch; exact HPRE|]. split; [exact HPERM|].
  split; [exact HG1|]. split; [exact HG2 | exact HG3]. }
split.
{ unfold rf_kept.
  split; [unfold spZ at 1; rewrite X2, U2d; rewrite unsigned_lit_small by (unfold spZ in *; lia); lia|].
  split; [rewrite X3; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 3%nat 3%bv eq_refl)|].
  split; [rewrite X4; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 4%nat 4%bv eq_refl)|].
  split; [rewrite X26; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 26%nat 26%bv eq_refl)|].
  split; [rewrite X27; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 27%nat 27%bv eq_refl)|].
  split; [rewrite X8, <- U2d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X18, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X19; rewrite OLDd, OLDc by lia; exact E33b|].
  split; [rewrite X20, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X21, <- U513d; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite X22, <- U289d; symmetry; apply Z_to_bv_bv_unsigned. }
split; [clear -HF4096; lia|].
split; [exact RSAV|].
split; [exact (field_of_region Ed _ 38%nat F _ 0 64 0 0 56 8%N (SOff 512 0) FL HRF38 U38d
    ltac:(cbn [In]; tauto)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U512d; reflexivity)
    ltac:(clear -HFL4096 HFLc C1; cbn; lia) ltac:(cbn; lia))|].
split; [exact NSm|].
split; [exact DONEm|].
split; [exact LKm|].
split; [rewrite Hnil; cbn [rf_run gse_c gse_O gse_no gse_cap]; exact AOUTm|].
split; [rewrite Hnil; cbn [rf_run gse_cap]; rewrite Eab;
  rewrite Hnil in HPERM; unfold rf_eblks in HPERM; cbn [map concat app] in HPERM; exact HPERM|].
split; [exact GLvm|].
split; [exact GLwm|].
split; [exact PRESm|].
split; [rewrite Hnil; cbn [rf_cost]; destruct HFS as (fS2 & EfS2); rewrite EfS2; exact (MO_FR S fS2)|].
(* the room round: no source, so nothing was charged: the seat's room is rf_post's kr *)
rewrite Hnil in HRM2. exact HRM2.
-
(* ---- sources: s7 = 0, s8 = 16, s9 = the hi slot of g_src; run to the loop head at 0x168 ---- *)
cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok_x RUNTO HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x168).
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia ]
  | ]).
  destruct Hin. }
pmkst HS.
(* ---- the cut state L at 0x168, round 0: the run from the blez wrote only the frame, so the transport block carries ---- *)
assert (CK2 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms2) x = aview SEGS (w_H W) mem3 x).
{ intros x Hx Hn.
  rewrite (aview_kept_out Ed _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)).
  exact (aview_kept_out Ed _ (w_H W) mem3 (ms_mem ms1) HFr1 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)). }
assert (CG2 : mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms2)))
  by (intros y Hy; exact (HG6 y (HG5 y Hy))).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARm.
pose proof (FAOUT (ms_mem ms2) _ CK2 CG2 HARm) as AOUTm.
destruct (FREST (ms_mem ms2) _ CK2 CG2 HARm) as (LKm & ROMm & E5m & NSm & GLvm & GLwm & PRESm & DONEm).
(* the registers the loop inherits, and its counters s7 = 0, s8 = 16, s9 = the hi slot of g_src *)
prreg HS (23%bv : bv 5) X23. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (U290d : bv_unsigned (ew Ed 290) = VAL (A_HI 10))
  by exact (HEId (A_HI 10) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (U512d : bv_unsigned (ew Ed 512) = FL) by (rewrite OLDd, HIc by lia; exact U512).
assert (U289d : bv_unsigned (ew Ed 289) = VAL (A_HI 9))
  by exact (HEId (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (EWD : forall (k : nat) (r : bv 5), (k < 34)%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot Ed (SOff k 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros k r Hk Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite OLDd, OLDc, OLDb, OLDa by lia; rewrite (EE k r Hr); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_region_nth Ed _ _ 2%nat _ HS eq_refl) as HRf.
pose proof (st_ok_pi_region_nth Ed _ _ 1%nat _ HS eq_refl) as HRF38.
cbn [ms_mem restrict] in HRf, HRF38.
assert (RSAV : rf_saved W (ms_mem ms2) (spZ regs) regs) by
 (intros i Hi;
  destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 0) with (spZ regs + (-88)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-88) 8%N (SOff 25 0)
         (bv_unsigned (getr regs 25%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 25%nat 25%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 25%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 1) with (spZ regs + (-80)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-80) 8%N (SOff 24 0)
         (bv_unsigned (getr regs 24%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 24%nat 24%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 24%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 2) with (spZ regs + (-72)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-72) 8%N (SOff 23 0)
         (bv_unsigned (getr regs 23%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 23%nat 23%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 23%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 3) with (spZ regs + (-64)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-64) 8%N (SOff 22 0)
         (bv_unsigned (getr regs 22%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 22%nat 22%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 22%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 4) with (spZ regs + (-56)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-56) 8%N (SOff 21 0)
         (bv_unsigned (getr regs 21%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 21%nat 21%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 21%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 5) with (spZ regs + (-48)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-48) 8%N (SOff 20 0)
         (bv_unsigned (getr regs 20%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 20%nat 20%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 20%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 6) with (spZ regs + (-40)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-40) 8%N (SOff 19 0)
         (bv_unsigned (getr regs 19%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 19%nat 19%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 19%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 7) with (spZ regs + (-32)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-32) 8%N (SOff 18 0)
         (bv_unsigned (getr regs 18%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 18%nat 18%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 18%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 8) with (spZ regs + (-24)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-24) 8%N (SOff 9 0)
         (bv_unsigned (getr regs 9%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 9%nat 9%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 9%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 9) with (spZ regs + (-16)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-16) 8%N (SOff 8 0)
         (bv_unsigned (getr regs 8%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 8%nat 8%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 10) with (spZ regs + (-8)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-8) 8%N (SOff 1 0)
         (bv_unsigned (getr regs 1%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 1%nat 1%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | exfalso; clear -Hi; lia ] ] ] ] ] ] ] ] ] ] ]).
(* ---- RFI at round 0 ---- *)
pose proof (FENT (ms_mem ms2) _ CK2 CG2 HARm) as ENTm.
destruct DONEm as (NSWm & [(HT0 & _) | (HTn & VSm & WSm & VCm & WCm & HTinm)]).
{ exfalso. destruct HREL as [(_ & Hes0 & _) | HRA]; [rewrite Hes0 in Hc; cbn [length Z.of_nat] in Hc; lia|].
  pose proof HRA as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & HT4096 & _). clear -HT0 HT4096; lia. }
apply (LOOP (length es) regs ly S Hp W mem md T es c O mx no cap out rest fpos 0%nat ly S2 Hp W (ms_regs ms2) (ms_mem ms2) _ kr
  ltac:(lia) (conj HTOPR (ex_intro _ ch (conj HPRE HCTX))) HCNTe).
unfold RFI. exists 0, out, 0.
change (frame_addr ly 0 fpos) with F. change (flag_addr ly 0 fpos) with FL.
split; [exact HJX3|].
split.
{ split; [exists ch; exact HPRE|]. split; [exact HPERM|].
  split; [exact HG1|]. split; [exact HG2 | exact HG3]. }
split.
{ unfold rf_kept.
  split; [unfold spZ at 1; rewrite X2, U2d; rewrite unsigned_lit_small by (unfold spZ in *; lia); lia|].
  split; [rewrite X3; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 3%nat 3%bv eq_refl)|].
  split; [rewrite X4; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 4%nat 4%bv eq_refl)|].
  split; [rewrite X26; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 26%nat 26%bv eq_refl)|].
  split; [rewrite X27; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 27%nat 27%bv eq_refl)|].
  split; [rewrite X8, <- U2d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X18, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X19; rewrite OLDd, OLDc by lia; exact E33b|].
  split; [rewrite X20, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X21, <- U513d; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite X22, <- U289d; symmetry; apply Z_to_bv_bv_unsigned. }
split; [clear -HF4096; lia|].
split; [rewrite X23; reflexivity|].
split; [rewrite X24; reflexivity|].
split; [rewrite X25, <- U290d; symmetry; apply Z_to_bv_bv_unsigned|].
split; [exact RSAV|].
split.
{ exact (field_of_region Ed _ 38%nat F _ 0 64 0 0 56 8%N (SOff 512 0) FL HRF38 U38d
    ltac:(cbn [In]; tauto)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U512d; reflexivity)
    ltac:(clear -HFL4096 HFLc C1; cbn; lia) ltac:(cbn; lia)). }
split; [clear -Hc; lia|].
split; [exact NSB|].
split; [exact HTn|].
split; [exact NSm|].
split; [exact NSWm|].
split; [exact VSm|].
split; [exact WSm|].
split; [exact VCm|].
split; [exact WCm|].
split; [exact HTinm|].
split; [intros j Hj; exact (ENTm j (proj2 Hj))|].
split; [exact LKm|].
split; [cbn [firstn rf_run gse_c gse_O gse_no gse_cap]; exact AOUTm|].
split; [cbn [firstn skipn rf_run gse_cap]; rewrite Eab; exact HPERM|].
split; [exact GLvm|].
split; [exact GLwm|].
split; [exact E5m|].
split; [exact ROMm|].
split; [exact PRESm|].
split; [cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]; rewrite Hbb2; exact HROOM|].
split; [destruct HFS as (fS2 & EfS2); rewrite EfS2; exact (MO_FR S fS2)|].
split; [rewrite Z.add_0_l; apply Z.le_refl|].
split; [exact HMOK|].
(* the room round: round 0 is owed the whole charge, the seat kept it *)
cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]. exact HRM2.
Qed.
(* THE GENERIC TOP: the entry segment over ARx, handing off to the tail and to the loop at round 0, and the loop
   handing off to the tail on its exit arm. *)
Theorem pb_relay_finish_h_x : rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX A_relay_finishP.
Proof.
exact (rf_entry_seg rf_tail (rf_loop rf_tail)).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; the G3 gestures_end form): relay_finish at a world relation R, concluding
   W_contract_xR.rf_spec_xR.  The cut states RFX / RFI and the two segment statements carry the journal at R
   (ajournal_gx_x -> ajournal_gx_xR R) and the step relation SRrG SEGS R; each journal lemma is its R twin.  The token
   runs go through the G instances (RUN0R: YC80xR.SRrG_run_pi_tok_AJxG; RUNR / RUNTOR: W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG; BRR: W_kit.v paj_branch_xR), the plain runs and the flag store through W_frame_x.v's G twins
   (RUNPR, RUNCR, RUNFR); the return is the strict step lifted by SRr_SRrG (WLE_R).  The calls: __asan_stack_malloc_0
   by W_frame_x.v aj_stack_malloc_pres_at_raw_xR (strict SRr, lifted by SRr_SRrG), the mutex lock and unlock by
   W_sites_x.v aj_gx_entry_at_xR (ALOCK / AUNLOCK stay strict), free (s->buf) by the R free rules over CTX (W_journal_x.v
   Section hc: afree_cf_rule_c_xR / afree_null_cf_rule_c_xR, whose call-boundary premise RO comes from the journal's
   ARx at the call state by RO_ARx), and gestures_end by GSE_R : gse_spec_xR.  The strict walk above
   keeps its text and its proofs. ---- *)
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
Let RUN0R := YC80xR.SRrG_run_pi_tok_AJxG (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr) (R := R).
Let RUNR := paj_run_x_xG B PST ARx LAWS R G HG 0 ([] : list (Z * Z)).
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R G HG 0 ([] : list (Z * Z)).
Let BRR := paj_branch_xR (PI := PI) (R := R).
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNCR := SRrG_run_pi_AJ_call_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNFR := aj_flag_store_pi_xG (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE (R := R).
(* :491 RFX at R *)
Definition RFX_xR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (fpos : Z) (lyX : alayout) (SX : astate) (HpX : list Z) (WX : world SEGS)
(regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) (kr : nat) : Prop :=
exists kX outX,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  lyX SX HpX WX memX mdX kX /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsX (spZ regs) (frame_addr ly 0 fpos) /\ frame_addr ly 0 fpos <> 0 /\
rf_saved WX memX (spZ regs) regs /\
val_mem SEGS (arm WX memX) (frame_addr ly 0 fpos + 56) 8 (flag_addr ly 0 fpos) /\
val_mem SEGS (arm WX memX) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\
rf_done lyX SX WX memX T /\
alock_at RG WX memX true /\
aout_at B RG lyX SX WX memX
  (gse_c (rf_run c O mx no cap es)) (gse_O (rf_run c O mx no cap es)) mx
  (gse_no (rf_run c O mx no cap es)) (gse_cap (rf_run c O mx no cap es)) outX /\
Permutation (ablocks B lyX SX) (rf_tblk T ++ aout_blks (gse_cap (rf_run c O mx no cap es)) outX ++ rest) /\
(exists lst, val_mem SEGS (arm WX memX) GL 4 lst) /\ awr WX memX GL 4 /\
apres_kept B W mem WX memX /\
mo_le MT S SX (rf_cost MT c O mx no cap es) /\
(* the room round: the room left after every round, which rf_post passes on *)
rp_RM RP SX kr.
(* :515 RFI at R *)
Definition RFI_xR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z)
(rest : list (Z * Z)) (fpos : Z) (i : nat) (lyL : alayout) (SL : astate) (HpL : list Z) (WL : world SEGS)
(regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (kr : nat) : Prop :=
exists kL outL spent,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  lyL SL HpL WL memL mdL kL /\
rf_entry_facts ly S Hp W mem md regs T es cap out rest /\
rf_kept regs regsL (spZ regs) (frame_addr ly 0 fpos) /\ frame_addr ly 0 fpos <> 0 /\
getr regsL 23 = w64 (Z.of_nat i) /\ getr regsL 24 = w64 (16 + 56 * Z.of_nat i) /\
getr regsL 25 = w64 (VAL (A_HI 10)) /\
rf_saved WL memL (spZ regs) regs /\
val_mem SEGS (arm WL memL) (frame_addr ly 0 fpos + 56) 8 (flag_addr ly 0 fpos) /\
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
(* the room round: the room the remaining rounds charge (each a free and a gestures_end), then rf_post's kr *)
rp_RM RP SL (Z.to_nat (rf_cost MT_rk
  (gse_c (rf_run c O mx no cap (firstn i es))) (gse_O (rf_run c O mx no cap (firstn i es))) mx
  (gse_no (rf_run c O mx no cap (firstn i es))) (gse_cap (rf_run c O mx no cap (firstn i es)))
  (skipn i es)) + kr).
(* :566 rf_tail_stmt at R *)
Definition rf_tail_stmt_xR : Prop :=
forall regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr,
RFX_xR regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr ->
YA0nH.SRrG SEGS R WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_rf_tail)) memX (seg_rom SEGS)) mdX)
(rf_post_xR B PST ARx R MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* :583 rf_loop_stmt at R *)
Definition rf_loop_stmt_xR : Prop :=
forall (k : nat) regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr,
(length es - i <= k)%nat ->
rf_ctx regs ly S Hp W mem md ->
cnt_ok_pk RP rf_pk (ablocks B ly S) ->
RFI_xR regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr ->
YA0nH.SRrG SEGS R WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)) mdL)
(rf_post_xR B PST ARx R MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr).
(* :761 rf_tail at R *)
Lemma rf_tail_xR : rf_tail_stmt_xR.
Proof using AUNLOCK HH11 HH12 HH9 HIG HIGO HPLAIN HSEPG HSEPO HV6 IMGC MLAW MO_FR RGAL RUNFR RUNR R_trans WLE_R.
unfold rf_tail_stmt_xR.
intros regs ly S Hp W mem md T es c O mx no cap out rest fpos lyX SX HpX WX regsX memX mdX kr HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RF_STK = 16704) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HX as (kX & outX & HJX & ((ch & HPRE0) & HPERM0 & HG1 & HG2 & HG3) & HKP & HF0 & HSV & HFLv & HNS & HDONE & HLK
  & HAO & HPERM & HGLv & HGLw & HPRES & HMO & HRMX).
pose proof HPRE0 as (_ & Hra & _ & Hgp & Htp & _). clear HPRE0 HPERM0.
destruct HKP as (KSP & K3 & K4 & K26 & K27 & K8 & K18 & K19 & K20 & K21 & K22).
pose proof HJX as (HSTK & HXO & (memS & HJi & HAG) & HOUT).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARx & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Hfin : In (0, fpos) (frames SX)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyX 0 fpos = frame_addr ly 0 fpos)
by (unfold frame_addr; pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _); rewrite HlyF; reflexivity).
assert (EFL : flag_addr lyX 0 fpos = flag_addr ly 0 fpos)
by (unfold flag_addr; pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _); rewrite HlyF; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARx Hfin) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARx Hfin) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARx Hfin) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARx Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
rewrite EFA in HF4096, HFceil, HFhigh, HFal, HFapp, HFpres, HFSpres, HFimg.
rewrite EFL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
(* the file's lia does not turn div / mod into equations: F / 8 enters as an atom with these facts *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as Dq; rewrite HFal in Dq; lia).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as Dm. rewrite HFal, Z.add_0_r in Dm. rewrite Dm at 1.
  replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592184995840) by (apply Z.div_lt_upper_bound; lia).
pose proof (rfx_entry WX regsX memX regs F FL
  ltac:(rewrite KSP; rewrite WS in Hslo; lia) ltac:(rewrite KSP; lia)
  ltac:(rewrite KSP, Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite K8, KSP; f_equal; lia) K18 K20 K22 HF4096 HFceil HFal
  ltac:(replace (spZ regsX + 96) with (spZ regs) by lia; exact HSV)
  (proj1 HDONE) ltac:(pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _); exact Hw) HGLw) as HS.
remember (Eimg (Ereg regsX (rfx_extra regs FL))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 11)%nat -> ew E (32 + i) = getr regs (nth i RF_SAVED 0%bv))
by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact (nth_rfx_extra regs FL i Hi)).
assert (E43 : ew E 43 = Z_to_bv 64 FL)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX (rfx_extra regs FL) 11)).
assert (UH : forall j, (j < 30)%nat -> bv_unsigned (ew E (A_HI j)) = VAL (A_HI j)).
{ intros j Hj. subst E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact (pa_val_range _). }
assert (U9 : bv_unsigned (ew E 289%nat) = VAL (A_HI 9)) by exact (UH 9%nat ltac:(lia)).
assert (U11 : bv_unsigned (ew E 291%nat) = VAL (A_HI 11)) by exact (UH 11%nat ltac:(lia)).
assert (U12 : bv_unsigned (ew E 292%nat) = VAL (A_HI 12)) by exact (UH 12%nat ltac:(lia)).
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
(* ---- the three stores: g_nsrc = 0, g_client = -1, g_listen = -1; a0 = &g_lock; up to the unlock ---- *)
paj_run_tok_xR RUNR HS HJX SHOK Bspan.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U11, ?U12 in Hr;
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
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U11, ?U12 in Hr; lia | ]).
  destruct Hin. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rg_client RG <= a < rg_client RG + 4) ->
  ~ (GL <= a < GL + 4) -> aview SEGS (w_H WX) (ms_mem ms) a = aview SEGS (w_H WX) memX a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E _ (w_H WX) memX (ms_mem ms) HFr1 a Ha (NWA a N1 N2 N3))).
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HRn.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HRc.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HRg.
cbn [ms_mem restrict] in HRn, HRc, HRg.
pose proof (field_of_region E _ 289%nat _ _ _ _ _ _ 868 4%N (SLit 0) 0 HRn U9 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as VNS1.
rewrite HH9 in VNS1. change (N.to_nat 4) with 4%nat in VNS1.
pose proof HRc as (_ & _ & _ & HCc). cbn [YP09.r_chunks YP09.r_base base_val] in HCc. apply Forall_inv in HCc.
pose proof (rfx_m1_val E _ _ _ HCc) as VCL1. rewrite U11, HH11 in VCL1.
pose proof HRg as (_ & _ & _ & HCg). cbn [YP09.r_chunks YP09.r_base base_val] in HCg. apply Forall_inv in HCg.
pose proof (rfx_m1_val E _ _ _ HCg) as VGL1. rewrite U12, HH12 in VGL1.
clear HRn HRc HRg HCc HCg.
(* ---- the unlock (a PCall to pthread_mutex_unlock, a0 = &g_lock = VAL (A_OBJ 6)) ---- *)
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
prreg HS (10%bv : bv 5) Q10.
assert (HSPc : spZ (ms_regs ms) = spZ regs + -96) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (QA0 : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 247%nat with (A_OBJ 6).
  rewrite (img_env_atomP E (A_OBJ 6) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), HV6. reflexivity. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR1.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B lyX SX a).
{ intros a Ha Ho. destruct (HG a (INL a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho). }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H WX) mem') (rg_lock RG + 4) 4 0)
    WX (ms_regs ms) (ms_mem ms) RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), K3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), K4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
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
      * rewrite HSPc. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. exact (LKW1 (a - rg_lock RG) ltac:(lia)).
      * apply HNOWN. lia.
      * rewrite HSPc. lia.
    + intros a Ha HK. exact (proj2 (proj2 (HG a (INL a ltac:(lia)))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK43) & Hfr3 & Hpres3).
(* the frame region survives the unlock (the callee writes only the lock word and its scratch below sp) *)
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H WX) mem3) HP3 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_aview E (w_H WX) (ms_mem ms) mem3 2%nat (spZ regsX)); [exact Usp | | exact Hpres3].
  intros a Ha. apply Hfr3; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- the fake frame's release: the header word, the shadow (0xf5 x 8), the flag byte; then the epilogue ---- *)
remember (havoc E 66 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 66)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (U2a : bv_unsigned (ew Ea 2) = spZ regsX) by (rewrite OLDa by lia; exact Usp).
assert (U20a : bv_unsigned (ew Ea 20) = F)
by (rewrite OLDa, (EE 20%nat 20%bv eq_refl), K20 by lia; apply unsigned_lit_small; lia).
assert (U21a : bv_unsigned (ew Ea 21) = SB + F / 8)
by (rewrite OLDa, (EE 21%nat 21%bv eq_refl), K21 by lia; apply unsigned_lit_small; unfold SB; lia).
assert (U43a : bv_unsigned (ew Ea 43) = FL) by (rewrite OLDa, E43 by lia; apply unsigned_lit_small; lia).
assert (PR2 : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) mem3 a)
by (intros a Ha; apply Hpres3; exact (apresent_grows (w_H WX) memX (ms_mem ms) a MG1 Ha)).
assert (FLV2 : val_mem SEGS (mrestrict (w_H WX) mem3) (F + 56) 8 FL).
{ apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX mem3 _ 8 FL); [|exact HFLv].
  intros k Hk. cbn in Hk. unfold off_img in HFimg.
  rewrite (Hfr3 (F + 56 + k) ltac:(lia) ltac:(lia) ltac:(lia)). apply KA; lia. }
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 20%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 43 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U20a; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply PR2; exact (proj1 (HFpres (F + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ea _ F 56 8 _ FL);
      [cbn [sv_denot]; rewrite U43a, Z.add_0_r; reflexivity | zside | zside | exact FLV2] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U20a, U2a; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 21%nat) 0 8 0 8 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U21a; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply PR2;
    unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; exact (proj1 (HFSpres o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U21a, U20a, U2a; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold SB;
    repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 43%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U43a; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply PR2; replace (FL + o) with FL by lia; exact HFLp)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U43a, U21a, U20a, U2a; repeat split;
    [ unfold zone2, off_img in HFLz; unfold SB; lia
    | destruct (Z_lt_ge_dec FL F) as [Hlt | Hge]; [left; lia|];
      destruct (Z_lt_ge_dec FL (F + 64)) as [Hlt2 | Hge2]; [exfalso; exact (proj2 (HFpres FL ltac:(lia)) HFLo) | right; lia]
    | lia ])) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the plain runner on the donor journal inside ajournal_gx (own = [(0, fpos)]): unpack, run, repack below *)
destruct HJX3 as (_ & _ & (memS3 & HJi3 & HAG3) & _). rewrite !Z.add_0_r in HJi3.
paj_run_flag_sh_x RUNFR HS HJi3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. rewrite EFL.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2a, ?U20a, ?U21a, ?U43a in Hr;
    first [ lia
    | right; lia
    | left; right; right; right; exists 0, fpos; split; [left; reflexivity|]; rewrite EFA; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
            | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ] | ]).
  destruct Hin. }
{ intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U43a
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
match goal with Hx : mem_grows _ _ |- _ => lazymatch Hx with MG1 => fail | _ => rename Hx into MG3 end end.
match goal with Hx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  lazymatch Hx with HFr1 => fail | _ => rename Hx into HFrC end end.
cbn [ms_mem mkst] in MG3, HFrC.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msf end.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
(* ---- the return: ret to the entry's ra (restored from the frame), sp back to sp0 ---- *)
apply (YA0nH.SRr_SRrG SEGS R WLE_R).
eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (E32 : ew E 32 = getr regs 25) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 24) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 23) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 22) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs 21) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs 20) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs 19) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = getr regs 9) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = getr regs 8) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = getr regs 1) by exact (EX 10%nat ltac:(lia)).
pose proof HJi3 as (HARf & _ & _ & _ & _ & Hfrf & _).
assert (EabF : ablocks B lyX (stack_free_state 0 fpos SX) = ablocks B lyX SX)
by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
(* presence and writability, from the cut to the return *)
assert (PRf : forall a, apresent (w_H WX) memX a -> apresent (w_H WX) (ms_mem msf) a)
by (intros a Ha; exact (apresent_grows (w_H WX) mem3 (ms_mem msf) a MG3 (PR2 a Ha))).
assert (WKf : forall x, writable_at SEGS (arm WX memX) x -> writable_at SEGS (arm WX (ms_mem msf)) x)
by (intros x Hx; exact (writable_kept (w_H WX) memX (ms_mem msf) x (PRf x) Hx)).
(* the release's windows: the fake frame, its shadow and the flag byte *)
assert (KC : forall x, 0 <= x < 2 ^ 64 -> ~ (F <= x < F + 64) -> ~ (SB + F / 8 <= x < SB + F / 8 + 8) -> x <> FL ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) mem3 x).
{ intros x Hx N1 N2 N3. apply (aview_kept_out Ea _ (w_H WX) mem3 (ms_mem msf) HFrC x Hx).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2a, ?U20a, ?U21a, ?U43a in Hr; lia | ]).
  destruct Hin. }
pose proof pa_img_range as Himg.
(* an image-band byte off the lock word keeps its view from after the stores to the return *)
assert (KIMG : forall x, 0x10000 <= x < 0x5fb000 -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) (ms_mem ms) x).
{ intros x Hx Nl. unfold off_img in HFimg. unfold zone2, off_img in HFLz.
  rewrite (KC x ltac:(lia) ltac:(lia) ltac:(unfold SB; lia) ltac:(lia)).
  apply Hfr3; lia. }
(* ... and from the cut, when it is none of the three stored cells *)
assert (KALL : forall x, 0x10000 <= x < 0x5fb000 -> ~ (rg_nsrc RG <= x < rg_nsrc RG + 4) ->
  ~ (rg_client RG <= x < rg_client RG + 4) -> ~ (GL <= x < GL + 4) -> ~ (rg_lock RG + 4 <= x < rg_lock RG + 8) ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x)
by (intros x Hx N1 N2 N3 N4; rewrite (KIMG x Hx N4); apply KA; [lia | exact N1 | exact N2 | exact N3]).
(* a byte of a live block keeps its view from the cut to the return *)
assert (KBLK : forall p n x, In (p, n) (ablocks B lyX SX) -> p <= x < p + req_size n ->
  aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros p n x Hin Hx.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARx Hin) as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _).
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n x HARx Hin Hx) as Hxn.
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 0 fpos HARx Hin Hfin) as Hsep.
  rewrite EFA in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep.
  assert (Nc : forall i lo m, nth_error rf_cells i = Some (lo, m) -> ~ (lo <= x < lo + m)).
  { intros i lo m Hn Hr. exact (Hxn (proj1 (HPLAIN x (in_rf_cell i lo m x Hn Hr)))). }
  rewrite (KC x ltac:(lia) ltac:(lia)
    ltac:(intros Hs; exact (fshadow_not_app F 8 p (req_size n) x ltac:(lia) ltac:(lia) Hpapp ltac:(unfold SB in Hs; lia) Hx))
    ltac:(intros ->; exact (proj2 (Hppres FL Hx) HFLo))).
  rewrite (Hfr3 x ltac:(lia) ltac:(intros Hl; apply (Nc 1%nat (rg_lock RG) 12); [reflexivity | lia]) ltac:(lia)).
  apply KA; [lia | apply (Nc 2%nat); reflexivity | apply (Nc 5%nat); reflexivity | apply (Nc 6%nat); reflexivity]. }
(* the values the tail stored, at the return *)
assert (VNSf : val_mem SEGS (arm WX (ms_mem msf)) (rg_nsrc RG) 4 0).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 0); [|exact VNS1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 1%nat S01. apply KIMG; lia. }
assert (VCLf : val_mem SEGS (arm WX (ms_mem msf)) (rg_client RG) 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VCL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 2%nat S02. apply KIMG; lia. }
assert (VGLf : val_mem SEGS (arm WX (ms_mem msf)) GL 4 (2 ^ 32 - 1)).
{ unfold arm. apply (val_mem_kept SEGS (w_H WX) (w_H WX) (ms_mem ms) _ _ 4 _); [|exact VGL1].
  intros k Hk. cbn in Hk. zsep_pick HSEPO 0%nat 3%nat S03. apply KIMG; lia. }
(* the lock: released (word 4 by the unlock), type and waiter words kept *)
assert (LKF : alock_at RG WX (ms_mem msf) false).
{ unfold alock_at, arm. zsep_pick HSEPO 0%nat 1%nat S01. zsep_pick HSEPO 0%nat 2%nat S02. zsep_pick HSEPO 0%nat 3%nat S03.
  split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK0]. intros k Hk. cbn in Hk. apply KALL; lia.
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) mem3 _ _ 4 0); [|exact HLK43]. intros k Hk. cbn in Hk.
    unfold off_img in HFimg. unfold zone2, off_img in HFLz.
    apply KC; [lia | lia | unfold SB; lia | lia].
  - apply (val_mem_kept SEGS (w_H WX) (w_H WX) memX _ _ 4 0); [|exact LK8]. intros k Hk. cbn in Hk. apply KALL; lia.
  - intros i Hi. apply WKf. exact (LKW i Hi). }
(* the controller's cells (all but g_client) and the g_out block, from the cut *)
assert (AK : akept WX memX WX (ms_mem msf) (rfx_aout_fp (gse_cap (rf_run c O mx no cap es)) outX)).
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
  - assert (Hb : 0x10000 <= a < 0x5fb000).
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
assert (KSRC : forall x, rg_src RG <= x < rg_src RG + 8 -> aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(do 3 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 5%nat 7%nat T1. zsep_pick HSEPG 6%nat 7%nat T2. zsep_pick HSEPG 7%nat 9%nat T3. zsep_pick HSEPG 7%nat 10%nat T4.
  apply KALL; lia. }
assert (KCAP : forall x, rg_capsrc RG <= x < rg_capsrc RG + 4 -> aview SEGS (w_H WX) (ms_mem msf) x = aview SEGS (w_H WX) memX x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(do 4 right; left; reflexivity)) as Bs.
  cbn [fst snd] in Bs.
  zsep_pick HSEPG 5%nat 8%nat T1. zsep_pick HSEPG 6%nat 8%nat T2. zsep_pick HSEPG 8%nat 9%nat T3. zsep_pick HSEPG 8%nat 10%nat T4.
  apply KALL; lia. }
(* ---- the post ---- *)
unfold rf_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists lyX, (stack_free_state 0 fpos SX), HpX, r, m, d, kX, outX end.
split; [rewrite R1, OLDa, E42, Hra by lia; reflexivity|].
split.
{ eapply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md []).
  all: [> lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs); exact HJi3 | exact HAG3 | intros a Ha; lia]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, U2a, KSP.
    replace (spZ regs - 96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact K3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact K4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8, OLDa by lia. exact E41.
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9, OLDa by lia. exact E40.
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18, OLDa by lia. exact E39.
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19, OLDa by lia. exact E38.
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20, OLDa by lia. exact E37.
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21, OLDa by lia. exact E36.
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22, OLDa by lia. exact E35.
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23, OLDa by lia. exact E34.
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24, OLDa by lia. exact E33.
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25, OLDa by lia. exact E32.
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26, OLDa, (EE 26%nat 26%bv eq_refl) by lia. exact K26.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27, OLDa, (EE 27%nat 27%bv eq_refl) by lia. exact K27. }
split. { intros a Hi Ho He Hpr. exact (PRf a (HPRES a Hi Ho He Hpr)). }
split. { cbn [app] in Hfrf. exact Hfrf. }
split.
{ assert (HMF : mo_le MT SX (stack_free_state 0 fpos SX) 0) by (unfold stack_free_state; exact (MO_FR SX _)).
  pose proof (mle_station MT S SX _ _ 0 MLAW HMO HMF) as HM. rewrite Z.add_0_r in HM. exact HM. }
(* the room round: the release's state is a set_fs of SX (YG01.v stack_free_state), so rp_RPF carries RFX_xR's room *)
split. { unfold stack_free_state. exact (rp_RPF RP _ _ _ HRMX). }
split. { rewrite EabF. exact HPERM. }
split.
{ apply (rfx_aout_m1 lyX SX WX memX _ _ WX _ _ _ mx _ _ outX HAO AK WKf VCLf).
  intros b Hb. rewrite EabF. eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
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
    assert (HTin' : In (T, ATABLE) (ablocks B lyX (stack_free_state 0 fpos SX))) by (rewrite EabF; exact HTin).
    split; [exact HTin'|].
    (* the empty table: aentry_ok, NoDup and (W8's twelfth conjunct) no entry block is the table, all over [] *)
    split; [|split; [constructor | split; [constructor | constructor]]].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HARf HTin') as (_ & _ & _ & _ & HTp & _).
    destruct (garr8_of_present SEGS (arm WX (ms_mem msf)) T 896) as (l & Hl & Hg).
    { intros a Ha. destruct (HTp a ltac:(unfold req_size, ATABLE; cbn in Ha |- *; lia)) as ((Hh & b & Hb) & _).
      exists b. unfold arm, mrestrict. rewrite Hh. exact Hb. }
    exists (map (Z_to_bv 8) l). unfold atable_at. cbn [length map concat app].
    rewrite (rfx_bzs_map l (garr8_bytes_ok SEGS _ _ _ Hg)), length_map, Hl.
    unfold ATABLE, AENT. split; [cbn; lia|]. split; [cbn; lia|]. exact Hg. }
split; [exact VGLf|].
intros i Hi. apply WKf. exact (HGLw i Hi).
Qed.
(* :1552 rf_loop at R *)
Lemma rf_loop_xR : rf_tail_stmt_xR -> rf_loop_stmt_xR.
Proof using AFREEN_R AFREE_R BLKN GSE_R HE5R HIG HP0 HPLAIN HPLAINO HROMO HSEPG HSEPO HV7 HV8 HWSEG HWSEGE MLAW PSTC PSTR RO_ARx RUNR RUNTOR R_trans TL.
intros TAIL. unfold rf_loop_stmt_xR.
induction k as [|k IH]; intros regs ly S Hp W mem md T es c O mx no cap out rest fpos i lyL SL HpL WL regsL memL mdL kr Hk HCTXF HCNT0 HRFI.
{ exfalso. destruct HRFI as (kL & outL & spent & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRFI as (kL & outL & spent & HJ & HEF & HKP & HF0 & H23 & H24 & H25 & HSV & HFLG & Hi & Hn16 & HT0 &
  HNS & HNSw & HSRC & HSRCw & HCAP & HCAPw & HTB & HENT & HLK & HOUT & HPERM & HGLv & HGLw & HEND5 & HROM & HPK &
  HROOM & HMLE & HSP & HMOK & HRML).
set (F := frame_addr ly 0 fpos) in *. set (sp0 := spZ regs) in *.
set (e := nth i es rf_e0).
destruct (HENT i ltac:(lia)) as (HG8 & HAW & HHELD & HBUF). fold e in HG8, HAW, HHELD, HBUF.
change (rfl_bufok lyL SL e) in HBUF.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARL.
destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL T ATABLE HARL HTB) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTapp, HTpres.
assert (Rb : 0 <= re_buf e < 2 ^ 64).
{ destruct HBUF as [(_ & ->) | (Hc & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS lyL SL _ WL memL mdL _ _ HARL Hin) as (_ & Hb4096 & Hbceil & _). pose proof (req_size_pos (re_cap e) ltac:(lia)). lia. }
set (p := T + 16 + 56 * Z.of_nat i).
set (n := Z.of_nat (length es)).
assert (HVB : val_mem SEGS (mrestrict (w_H WL) memL) p 8 (re_buf e)).
{ pose proof HHELD as (Hp1 & _). pose proof (rfl_buf_field _ _ e Hp1 Rb HG8) as H. unfold p, AENT in *.
  replace (T + 16 + 56 * Z.of_nat i) with (T + 56 * Z.of_nat i + 16) by lia. exact H. }
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
pose proof HKP as (Ksp & K3 & K4 & K26 & K27 & K8 & K18 & K19 & K20 & K21 & K22).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact K19).
assert (E24 : ew E 24 = Z_to_bv 64 (16 + 56 * Z.of_nat i)) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (EO : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j)) by (intros j Hj; subst E; apply Eimg_img; exact Hj).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsrc : forall x, rg_src RG <= x < rg_src RG + 8 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 3%nat _ 8 x eq_refl Hx)).
assert (Hnsrc : forall x, rg_nsrc RG <= x < rg_nsrc RG + 4 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 2%nat _ 4 x eq_refl Hx)).
assert (HTni : forall x, T <= x < T + 896 -> ~ in_img SEGS x)
by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL memL mdL T ATABLE x HARL HTB ltac:(change (req_size ATABLE) with 896; lia))).
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb. cbn [fst snd] in HNSb.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as HSRb. cbn [fst snd] in HSRb.
assert (Hp8 : p mod 8 = 0).
{ unfold p. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 16 + 56 * Z.of_nat i) with ((2 * (T / 16) + 2 + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
assert (HS : st_ok_pi SEGS VAL E ss_rfl (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_rf_loop)) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rfl. apply pa_entry_st_ok_full.
  - unfold rfl_sr. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    + cbn [sv_denot]. rewrite (EO (A_HI 10) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact H25.
    + cbn [sv_denot]. rewrite (EO (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned. exact K22.
  - vm_compute. reflexivity.
  - unfold rfl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 8) _ (EO (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 8))), HV8.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) T);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HSRC.
    + rewrite (VB (A_OBJ 7) _ (EO (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 7))), HV7.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold n; zside | zside |].
      rewrite Z.add_0_r. exact HNS.
    + rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
      split; [unfold p; lia|]. split; [unfold p; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 8 (SOff 34 0) (re_buf e));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HVB.
  - apply pairwise_disjoint_of_extents. unfold rfl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 8) _ (EO (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 8))), HV8.
    rewrite (VB (A_OBJ 7) _ (EO (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) (pa_val_range (A_OBJ 7))), HV7.
    rewrite (VB 33%nat p E33 ltac:(unfold p; lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    zsep_pick HSEPG 6%nat 7%nat D67.
    split; [split; [lia | split; [|exact I]] | split; [split; [|exact I] | split; exact I]].
    + rewrite !Z.add_0_r. apply rfl_apart; [lia | lia|]. intros x Hx1 Hx2.
      apply (HTni x ltac:(unfold p in Hx2; lia)). exact (proj1 (HPLAIN x (Hsrc x ltac:(lia)))).
    + rewrite !Z.add_0_r. apply rfl_apart; [lia | lia|]. intros x Hx1 Hx2.
      apply (HTni x ltac:(unfold p in Hx2; lia)). exact (proj1 (HPLAIN x (Hnsrc x ltac:(lia)))).
  - split; [|split; [exact I|]].
    + cbn [rfl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, p, n; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold n. revert HT16 HT4096 HTceil Hp8 Rb Hn16 Hi C1. clear. unfold p, SB. intros.
      repeat match goal with |- _ /\ _ => split end; lia.
    + cbn [rfl_facts f_alias alias_ok]. split; [|exact I]. apply bv_eq.
      fold (U E (SAlu ALU_ADD (SOff 32 0) (SOff 24 0))). fold (U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 T E32), (U_atom E 24 _ E24), (U_atom E 33 p E33) by (unfold p; lia).
      cbn [zalu_raw]. unfold zcanon, M64. unfold p. rewrite Z.mod_small by lia. lia. }
clear HE.
assert (HBx : U E rfl_Bx = SHADOW_OFF) by (unfold rfl_Bx; rewrite (U_atom E 19 SB E19) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS rfl_Bx rfl_SH E (mrestrict (w_H WL) memL)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyL SL HpL WL memL mdL T ATABLE p 8 HARL HTB); unfold p;
    change (req_size ATABLE) with 896; lia.
  - exact HBx.
  - rewrite (U_atom E 33 p E33) by (unfold p; lia). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold p, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold A_rf_loop.
paj_run_tok_xR RUNR HS HJ SHOK Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. }
(* ---- free (s->buf).  The run wrote nothing: the memory at the call is memL as the walk sees it. ---- *)
assert (MEQ1 : forall x, mrestrict (w_H WL) (ms_mem ms) x = mrestrict (w_H WL) memL x).
{ intros x. apply HFr. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
assert (AV1 : forall a, aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H WL) memL a)
by (intros a; apply aview_eq_of; apply MEQ1).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
(* the entry chain che is rf_ctx's, so that its trace is in CTX; rf_entry_facts' own afn_pre is not needed here *)
pose proof HEF as (_ & HPERM0 & HRFG & HSLG & HRFGe).
(* the room round: every class's live count at this round's loop head is at most the entry's plus one *)
assert (HCL : forall P, (ReplyCnt.acnt P (ablocks B lyL SL) <= ReplyCnt.acnt P (ablocks B ly S) + 1)%nat).
{ intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPERM0). apply rfl_acnt_round. }
pose proof HCTXF as (HTOPR & che & (HARe & Hrae & Hra4e & HGP0 & HTP0 & HstkE & HpresE & HchE & HQTE) & HCTXE).
change (spZ regs) with sp0 in HstkE, HpresE, HchE, HTOPR.
pose proof HstkE as (HalE & HstkE0 & HceilE & HsloE & HshiE & H47E & HbotE & HtopE & Htop2E).
assert (RSTK0 : 96 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (HceilS : alloc_ceiling <= sp0) by (unfold ASTACK in RSTK0; lia).
assert (HtopS : ly_top ly <= 2 ^ 64) by lia.
(* the stack at and above sp0 is the entry's, as the walk sees it: the journal (now at the run's memory) keeps it,
   and it is no G byte *)
assert (KST : forall a, sp0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJ0 & Hag0).
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & HJ0k & _).
  intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (unfold ASTACK in RSTK0; lia).
  rewrite (HJ0k a Hac ltac:(lia)). apply Hag0. rewrite unsigned_lit_small by lia. intros Hg.
  destruct (HG a Hg) as [Hi1 _]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (EtopL : ly_top lyL = ly_top ly).
{ pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJ0 & _).
  pose proof HJ0 as (_ & HlyL0 & _). pose proof HlyL0 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _). exact Et. }
(* the prologue's saved ra and s0, at sp0 - 8 and sp0 - 16, read through any reader that agrees there with L's *)
assert (RDW : forall rd : reader, (forall a, sp0 - 16 <= a < sp0 -> rd a = aview SEGS (w_H WL) memL a) ->
  rdword rd (sp0 - 8) = Some (raZ regs) /\ rdword rd (sp0 - 16) = Some (s0Z regs)).
{ intros rd Hrd. pose proof (HSV 10%nat ltac:(lia)) as V10. pose proof (HSV 9%nat ltac:(lia)) as V9.
  change (nth 10 RF_SAVED 0%bv) with (1%bv : bv 5) in V10. change (nth 9 RF_SAVED 0%bv) with (8%bv : bv 5) in V9.
  change (Z.of_nat 10) with 10 in V10. change (Z.of_nat 9) with 9 in V9.
  replace (sp0 - 88 + 8 * 10) with (sp0 - 8) in V10 by lia. replace (sp0 - 88 + 8 * 9) with (sp0 - 16) in V9 by lia.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R1. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8.
  change (bv_modulus 64) with (2 ^ 64) in R1, R8.
  split.
  - rewrite (rdword_ext (aview SEGS (w_H WL) memL) rd (sp0 - 8)) by (intros k0 Hk0; apply Hrd; lia).
    exact (rdword_of_val_mem SEGS (w_H WL) memL (sp0 - 8) (raZ regs) V10 R1).
  - rewrite (rdword_ext (aview SEGS (w_H WL) memL) rd (sp0 - 16)) by (intros k0 Hk0; apply Hrd; lia).
    exact (rdword_of_val_mem SEGS (w_H WL) memL (sp0 - 16) (s0Z regs) V9 R8). }
assert (Usp1 : spZ (ms_regs ms) = sp0 + -96) by (unfold spZ in Ksp |- *; rewrite Q2, (EE 2%nat 2%bv eq_refl); lia).
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), K3; exact HGP0).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), K4; exact HTP0).
assert (Q10' : getr (ms_regs ms) 10 = w64 (re_buf e)) by (rewrite Q10, E34; reflexivity).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the free's chain: relay_finish's record pushed on the entry's (rf_ctx's room refutes the no-chain case), so
   its trace - the free's return address pc + 392, then raZ regs, then the caller chain's - is rf_ctx's *)
assert (HRA1 : raZ (ms_regs ms) = A_relay_finishP + 392).
{ unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold A_relay_finishP, A_relay_finish, A_rf_loop, AF_fr_relay_finish. lia. }
assert (HCH : exists ch, chain_pre lyL (aview SEGS (w_H WL) (ms_mem ms)) (ms_regs ms) ch /\
  In (raZ (ms_regs ms) :: spine ch) CTX).
{ destruct (RDW (aview SEGS (w_H WL) (ms_mem ms)) ltac:(intros a _; apply AV1)) as [R8 R16].
  pose proof (rfl_chain_call_top ly (aview SEGS (w_H W) mem) (aview SEGS (w_H WL) (ms_mem ms)) sp0 (s0Z regs) che (raZ regs)
    HchE HceilS HalE HtopS ltac:(intros a Ha; apply KST; exact Ha)
    R8 R16 Hra4e HTOPR) as Hch'.
  exists ((sp0, raZ regs, s0Z regs) :: che). split.
  - apply (achain_chain_pre lyL _ (sp0 - 96) sp0 _ (ms_regs ms)).
    + exact (achain_ly_top ly lyL _ _ _ _ EtopL Hch').
    + rewrite Usp1. unfold ASTACK in RSTK0. lia.
    + unfold s0Z. rewrite Q8, (EE 8%nat 8%bv eq_refl), K8. unfold w64. apply unsigned_lit_small. unfold ASTACK in RSTK0. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite HRA1. exact HCTXE. }
destruct HCH as (ch & HCH & HCTXc).
set (r0 := rf_run c O mx no cap (firstn i es)) in *.
assert (Hcap0 : 0 <= gse_cap r0).
{ destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  destruct H26 as [(Hc & _) | (Hc & _)]; lia. }
rewrite (rfl_skipn_S es i Hi) in HSP, HROOM, HPERM, HRML. cbn [rf_cost rf_room rf_eblks concat map] in HSP, HROOM, HPERM, HRML.
fold e in HSP, HROOM, HPERM, HRML.
set (r1 := gse_run (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) in *.
destruct (rfl_gse_nonneg MT MLAW (gse_keys e) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) Hcap0) as [Hgc0 Hgk0].
fold r1 in Hgk0.
pose proof (rfl_cost_nonneg MT MLAW (skipn (Datatypes.S i) es) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) Hgk0) as Hrc0.
(* the room round: the room this round charges - the free's 1, then gestures_end's - and what the rounds after it
   and rf_post are owed (kr4), split exactly: MT_rk's costs are nonnegative *)
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
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
rewrite (pal_free B TL).
assert (HRFS : ASTACK - -96 <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
(* the room round: the free's stack room, from the round's inner journal (aj_stack_room_xR) *)
assert (HSR : ly_bot lyL + ACALL_PREFIX < spZ (ms_regs ms))
by (eapply aj_stack_room_xR; [exact HJi | exact Usp1 | exact HRFS]).
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply (YA0nH.SRrG_bind SEGS R R_trans) with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_xR (SK := SK) SEGS B PST ARx R RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)]
    ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  Permutation (ablocks B lyL SL) (rfl_bblk e ++ ablocks B ly4 S4) /\
  frames S4 = frames SL /\
  acall_kept SEGS B lyL SL WL mm W4 mem4 (sp0 + -96 - ASTACK) (sp0 + -96) (rfl_bex e) /\
  mo_le MT SL S4 (mo_free MT) /\
  rp_RM RP S4 kr4 /\
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + j) = aview SEGS (w_H WL) mm (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H WL) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct HBUF as [(Hc0 & Hb0) | (Hc0 & Hin0)].
  - eapply YA0nH.SRrG_mono.
    { exact (AFREEN_R WL (ms_regs ms) (ms_mem ms) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)] lyL SL HpL _ _
        (-96) (getr (ms_regs ms) 1) ch kr4 HJi ltac:(rewrite Q10', Hb0; reflexivity) Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HRO HCTXc HRMf HCNTf HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_eq _ 0) Hc0); exact (Permutation_sym HPm)|].
    split; [exact HFr4|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a []|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He Hpr).
  - eapply YA0nH.SRrG_mono.
    { exact (AFREE_R WL (ms_regs ms) (ms_mem ms) RF_STK sp0 (rf_FP T es cap out) ly S Hp W memS md [(0, fpos)] lyL SL HpL _ _
        (re_buf e) (re_cap e) (-96) (getr (ms_regs ms) 1) ch kr4 HJi Hin0 Q10' Usp1 eq_refl ltac:(lia)
        HRFS HSR Q3' Q4' eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HRO HCTXc HRMf HCNTf
        (HFPof Hc0) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [eexists; exact HJ4|].
    split; [exact HP4|].
    split; [unfold rfl_bblk; rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)), Eb1, Eb2; cbn [app];
      exact (Permutation_sym (Permutation_middle l1 l2 _))|].
    split; [exact HFr4|].
    split; [eapply rfl_acall_kept_mono; [|exact HK4]; intros a Ha; unfold rfl_bex; split; [lia | exact Ha]|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Ha Ho He Hpr. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Ha (rfl_not_owned _ _ _ _ _ _ a HARc Ha Ho) (rfl_not_owned _ _ _ _ _ _ a HAR4 Ha Ho) He); [|exact Hpr].
    intros Hblk. exact (blk_img_x SEGS B ARx LAWS lyL SL _ WL (ms_mem ms) _ (re_buf e) (re_cap e) a HARc Hin0 Hblk Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HFR4 & HK4 & HML4 & HRM4 & HERR4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK sp0 (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RF_STK sp0 _ ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem4 md4 kk4 memS HSTK HXO);
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
  - apply (region_kept_val_at E _ _ 249%nat (rg_src RG) 8 T);
    [change 249%nat with (A_OBJ 8); rewrite <- HV8; exact (HEI (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem ms)); [intros q _; apply AV1 | exact HSRC]
    | exact VS4 | lia].
  - apply (region_kept_val_at E _ _ 248%nat (rg_nsrc RG) 4 n);
    [change 248%nat with (A_OBJ 7); rewrite <- HV7; exact (HEI (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | apply (val_mem_kept SEGS (w_H WL) (w_H WL) memL (ms_mem ms)); [intros q _; apply AV1 | exact HNS]
    | exact VN4 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 36 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOK4 : sh_ok SEGS rfl_Bx [] Ea (mrestrict (w_H W4) mem4)) by constructor.
paj_run_to_tok_xR RUNTOR HS HJ4 SHOK4 Bspan AF_fr_gestures_end.
{ apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
(* ---- the call gestures_end (s), s = T + 56 i = SA.  The run wrote nothing. ---- *)
lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms0)) |- _ => rename Hx into HFr2 end.
lazymatch goal with Hx : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms0)) |- _ => rename Hx into MG2 end.
assert (MEQ2 : forall x, mrestrict (w_H W4) (ms_mem ms0) x = mrestrict (w_H W4) mem4 x).
{ intros x. apply HFr2. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
assert (AV2 : forall a, aview SEGS (w_H W4) (ms_mem ms0) a = aview SEGS (w_H W4) mem4 a) by (intros a; apply aview_eq_of; apply MEQ2).
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
  aview SEGS (w_H W4) (ms_mem ms0) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hx. rewrite AV2.
  assert (Hin1 : In (b, m) (ablocks B lyL SL)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM'|];
    destruct Hin as [<- | Hin]; [left; reflexivity | right; apply in_or_app; right; exact Hin]).
  replace x with (b + (x - b)) by lia. rewrite (KF2 b m (x - b) Hin1 ltac:(lia)); [apply AV1|].
  intros (Hc & Hx2). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
  assert (Hne : (b, m) <> (re_buf e, re_cap e)) by (intros Heq; apply (BUFNOT Hc); rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x SEGS B ARx LAWS lyL SL _ WL memL mdL b m _ _ HARL Hin1 Hin0 Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (PR2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H WL) memL a -> apresent (w_H W4) (ms_mem ms0) a).
{ intros a Ha Ho He [Hh [b Hb]]. apply (apresent_grows (w_H W4) mem4 (ms_mem ms0) a MG2). apply (HPR4 a Ha Ho He).
  split; [exact Hh|]. exists b. pose proof (MEQ1 (Z_to_bv 64 a)) as E1. unfold mrestrict in E1. rewrite Hh in E1.
  rewrite E1. exact Hb. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept WL memL W4 (ms_mem ms0) a).
{ intros a Ha Ho He. split; [rewrite AV2, (KF3 a Ha Ho He); apply AV1|].
  apply rfl_wr_pres2. exact (PR2 a Ha Ho He). }
assert (HTB4 : In (T, ATABLE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | left; reflexivity]).
assert (HX4 : forall b, In b X -> In b (ablocks B ly4 S4)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM4 | right; exact Hb]).
set (SA := T + 56 * Z.of_nat i).
assert (T10' : getr (ms_regs ms0) 10 = w64 SA).
{ rewrite T10, OLDa, E33 by lia. rewrite unsigned_lit_small by (unfold p; lia). unfold SA, p, w64. f_equal. lia. }
assert (HSA8 : SA mod 8 = 0).
{ unfold SA. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  replace (T + 56 * Z.of_nat i) with ((2 * (T / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
pose proof HHELD as (Hpd1 & Hpd2 & _).
assert (HrqG : forall m, m <= req_size m) by (intros m; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (GX : forall b, In b (gse_blks e) -> In b X) by (intros b Hb; unfold X; apply in_or_app; left; exact Hb).
assert (OX : forall b, In b (aout_blks (gse_cap r0) outL) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (GA5 : garr8 SEGS (arm W4 (ms_mem ms0)) SA (bzs (entry_bytes e))).
{ apply (garr8_frame SEGS (arm WL memL) (arm W4 (ms_mem ms0)) SA _); [unfold SA; unfold AENT in HG8; exact HG8|].
  intros x Hx. rewrite (rfl_len_entry e Hpd1 Hpd2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
  apply (KB T ATABLE x (or_introl eq_refl)). change (req_size ATABLE) with 896. unfold SA in Hx. lia. }
assert (AW5 : awr W4 (ms_mem ms0) SA AENT).
{ intros j Hj. apply (apresent_writable SEGS).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ T ATABLE HAR5 HTB4) as (_ & _ & _ & _ & HP & _).
  change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (SA + j) ltac:(unfold SA, AENT in *; lia))). }
assert (HELD5 : aheld_ok B ly4 S4 W4 (ms_mem ms0) e).
{ apply (rfl_aheld_ok_kept lyL SL WL memL ly4 S4 W4 (ms_mem ms0) e HHELD).
  - intros b Hb. exact (HX4 b (GX b Hb)).
  - intros b m x Hb Hx. apply (KB b m x (or_intror (GX _ Hb))). pose proof (HrqG m). lia. }
assert (AK5 : akept WL memL W4 (ms_mem ms0) (aout_fp B RG (gse_cap r0) outL)).
{ assert (GSL : forall a, inG (G_SL B RG) a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (intros a Ha; exact (conj (proj1 (HG a (HSLG a Ha))) (proj1 (proj2 (HG a (HSLG a Ha)))))).
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
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; clear - Har; lia]))) as [Hi1 _].
    unfold arm. apply rf_writable_of_seg; [|exact (HWSEGE a Har)].
    apply (hidden_not_img SEGS W4). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia.
  - destruct (Z.eqb_spec (gse_cap r0) 0) as [Hc0 | Hc0]; [destruct Hr|]. cbn [In] in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Har.
    assert (HobX : In (outL, gse_cap r0) X)
    by (apply OX; unfold aout_blks; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); left; reflexivity).
    assert (Hrq : req_size (gse_cap r0) = gse_cap r0) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (gse_cap r0) 0) Hc0); reflexivity).
    split; [apply (KB outL (gse_cap r0) a (or_intror HobX)); lia|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ outL (gse_cap r0) HAR5 (HX4 _ HobX)) as (_ & _ & _ & _ & HP & _).
    exact (proj1 (HP a ltac:(lia))). }
assert (AOUT5 : aout_at B RG ly4 S4 W4 (ms_mem ms0) (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL)
by (exact (aout_at_kept B RG lyL SL WL memL ly4 S4 W4 (ms_mem ms0) _ _ mx _ _ outL HOUT AK5 (fun b Hb => HX4 b (OX b Hb)))).
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
(* rf_spec_x's peak is rf_pk = 5 (W8Entry-2's composed constant): gestures_end's own premise constant gse_pk = 4,
   plus the +1 an earlier send round leaves in g_out's class; 5 is the stronger premise, so this narrows it by
   cnt_ok_pk_mono *)
(* the room round: at S4 the free only removed a block and the loop head is at most one above the entry (HCL), so
   every callee peak up to 4 fits under the entry's 5 (HCNT5g); gestures_end's gse_pk = 4 is the tight instance *)
assert (HCNT5g : forall pk : (Z -> bool) -> nat, (forall P, (pk P <= 4)%nat) -> cnt_ok_pk RP pk (ablocks B ly4 S4)).
{ intros pk Hpk. apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly S) _); [|exact HCNT0].
  intros P. pose proof (HCL P) as H1. pose proof (ReplyCnt.acnt_perm P _ _ HPM4) as H2. rewrite ReplyCnt.acnt_app in H2.
  pose proof (Hpk P) as H3. unfold rf_pk. cbv beta. lia. }
assert (HCNT5 : cnt_ok_pk RP gse_pk (ablocks B ly4 S4)) by (apply HCNT5g; intros P; unfold gse_pk; lia).
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (memS5 & HJin5 & HagS5).
assert (Usp5 : spZ (ms_regs ms0) = sp0 + -96) by (unfold spZ in Ksp |- *; rewrite T2, OLDa, (EE 2%nat 2%bv eq_refl) by lia; lia).
assert (T3' : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite T3, OLDa, (EE 3%nat 3%bv eq_refl), K3 by lia; exact HGP0).
assert (T4' : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite T4, OLDa, (EE 4%nat 4%bv eq_refl), K4 by lia; exact HTP0).
assert (HCH5 : exists ch1, achain ly4 (aview SEGS (w_H W4) (ms_mem ms0)) (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) ch1).
{ assert (K4S : forall a, sp0 - 96 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem ms0) a = aview SEGS (w_H WL) (ms_mem ms) a).
  { intros a Ha. rewrite AV2. exact (KF1 a ltac:(unfold ASTACK in RSTK0; lia) ltac:(lia)). }
  destruct (RDW (aview SEGS (w_H W4) (ms_mem ms0)) ltac:(intros a Ha; rewrite K4S by lia; apply AV1)) as [R8 R16].
  pose proof HJi4 as (_ & Hly4' & _). pose proof Hly4' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
  destruct (rfl_chain_call ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W4) (ms_mem ms0)) sp0 (s0Z regs) che (raZ regs)
    HchE HceilS HalE HtopS ltac:(intros a Ha; rewrite K4S by lia; apply KST; exact Ha)
    R8 R16 Hra4e) as [ch' Hch'].
  exists ch'. rewrite Usp5.
  replace (s0Z (ms_regs ms0)) with sp0.
  - replace (sp0 + -96) with (sp0 - 96) by lia. exact (achain_ly_top ly ly4 _ _ _ _ Etop4 Hch').
  - unfold s0Z. rewrite T8, OLDa, (EE 8%nat 8%bv eq_refl), K8 by lia. unfold w64.
    rewrite unsigned_lit_small by (unfold ASTACK in RSTK0; lia). reflexivity. }
destruct HCH5 as [ch1 HCH5].
eassert (HPRE5 : afn_pre_x SEGS B ARx GSE_STK ly4 S4 Hp4 W4 (ms_regs ms0) (ms_mem ms0) _ ch1).
{ eapply (afn_pre_x_atR SEGS B PST ARx (RF_STK + 0) (sp0 + 0) (rf_FP T es cap out) ly S Hp W memS5 md [(0, fpos)]
    ly4 S4 Hp4 W4 (ms_mem ms0) _ _ (ms_regs ms0) GSE_STK (-96) ch1 HJin5).
  - rewrite Usp5. lia.
  - reflexivity.
  - lia.
  - unfold GSE_STK, GSE_FRAME. pose proof (Z.le_max_r GE_STK ASTACK). unfold ASTACK in *. lia.
  - unfold RF_STK, RF_FRAME. pose proof (Z.le_max_l GSE_STK ASTACK). lia.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1, unsigned_lit_small by lia. lia.
  - exact T3'.
  - exact T4'.
  - exact HCH5. }
assert (ROM4 : rom_view SEGS W4 mem4).
{ apply (acall_kept_rom_view_x SEGS B ARx LAWS lyL SL WL (ms_mem ms) W4 mem4 _ _ (rfl_bex e) ly4 S4 Hp4 md4
    (proj1 HJi4) (conj KF1 (conj KF2 (conj KF3 (conj KF4 (conj KF5 KF6)))))).
  - intros a Ha. destruct (HROMO a Ha) as (_ & H2 & H3 & _). split; [exact H3 | exact H2].
  - intros a Ha. rewrite AV1. exact (HROM a Ha). }
assert (ROM5 : rom_view SEGS W4 (ms_mem ms0)) by (intros a Ha; rewrite AV2; exact (ROM4 a Ha)).
assert (END5' : garr8 SEGS (arm W4 (ms_mem ms0)) (VAL A_lit_end5) (bzs END5))
by (exact (rfl_end5_kept WL W4 memL (ms_mem ms0) HROM ROM5 HEND5)).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ exact (GSE_R W4 ly4 S4 Hp4 (ms_regs ms0) (ms_mem ms0) _ ch1 SA T e (gse_c r0) (gse_O r0) mx (gse_no r0) (gse_cap r0) outL
    (rf_eblks (skipn (Datatypes.S i) es) ++ rest) HPRE5 T10' HTB4 ltac:(unfold SA; lia) ltac:(unfold SA, AENT, ATABLE; lia) HSA8
    GA5 AW5 HELD5 AOUT5 HPG5 END5' ROM5 ROOM5 MO5 kr5 HRM4 HCNT5). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & out5 & -> & HJsl & HPsl & HPKsl & HMOsl & HRMsl & HPERMsl & HAOsl & HGAsl & HAWsl).
rewrite T1. fold r1 in HPERMsl, HAOsl.
(* ---- back from gestures_end: its journal (at G_SL) lifted to G and composed into the round's ---- *)
pose proof (ajournal_gx_G_mono_xR SEGS B PST ARx (G_SL B RG) G 0 [] GSE_STK (spZ (ms_regs ms0)) _ ly4 S4 Hp4 W4 (ms_mem ms0) _ []
  ly5 S5 Hp5 W5 mem5 md5 k5 HSLG HJsl) as HJslG.
assert (FPC : forall a, inFP ((SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL)) a ->
  (inFP (rf_FP T es cap out) a /\ exists b n, In (b, n) (ablocks B ly4 S4) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly4 S4) a).
{ intros a Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
  - left. split.
    + replace a with (T + (a - T)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ T ATABLE (a - T));
      [apply in_or_app; left; unfold rf_tblk; rewrite (proj2 (Z.eqb_neq T 0) HT0); left; reflexivity
      | change (req_size ATABLE) with 896; unfold SA in Hf; lia].
    + exists T, ATABLE. split; [exact HTB4 | change (req_size ATABLE) with 896; unfold SA in Hf; lia].
  - destruct (inFP_ablocks_fp_inv _ a Hf) as (b & m & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. split.
      * replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [|lia].
        apply in_or_app; right; apply in_or_app; left. unfold rf_eblks. apply in_concat. exists (aentry_blks e).
        split; [apply in_map, nth_In; lia|]. change (aentry_blks e) with (rfl_bblk e ++ gse_blks e).
        apply in_or_app; right; exact Hin.
      * exists b, m. split; [exact (HX4 _ (GX _ Hin)) | exact Hr].
    + destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly S)) as [Hin0 | Hnin0].
      * left. split; [|exists b, m; split; [exact (HX4 _ (OX _ Hin)) | exact Hr]].
        (* a start block: the entry's permutation puts it in rf_FP, as `rest` cannot hold it beside the current
           g_out block (no live block is listed twice) *)
        assert (Hin1 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest))
        by (eapply Permutation_in; [exact HPERM0 | exact Hin0]).
        assert (Hin2 : In (b, m) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out)).
        { rewrite !app_assoc in Hin1. rewrite !app_assoc. apply in_app_or in Hin1. destruct Hin1 as [H1 | H1]; [exact H1|].
          exfalso. pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HNf.
          inversion HNf as [|y0 l0 _ HNXf]; subst y0 l0.
          exact (rfl_nodup_app_r _ _ (b, m) (rfl_nodup_tl _ _ (rfl_nodup_tl _ _ HNXf)) Hin H1). }
        replace a with (b + (a - b)) by lia. unfold rf_FP. apply (inFP_ablocks_fp _ b m (a - b)); [exact Hin2 | lia].
      * right. exists b, m. split; [exact (HX4 _ (OX _ Hin)) | split; [exact Hnin0 | exact Hr]]. }
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G RF_STK sp0 0 [] (rf_FP T es cap out) ly S Hp W mem md [(0, fpos)]
  ly4 S4 Hp4 W4 (ms_mem ms0) _ _ GSE_STK (spZ (ms_regs ms0)) 0 [] _ [] ly5 S5 Hp5 W5 mem5 md5 k5 HJ4 HJslG
  ltac:(rewrite Usp5; unfold RF_STK, RF_FRAME; pose proof (Z.le_max_l GSE_STK ASTACK); lia)
  ltac:(rewrite Usp5; lia) ltac:(rewrite Usp5; lia)
  ltac:(intros a Hf; exfalso; exact (inFP_nil a Hf)) HG FPC) as HJ6.
cbn [app] in HJ6.
(* what gestures_end kept: every image byte outside G_SL (its journal's image clause), and live blocks' bytes
   outside its footprint *)
pose proof (ajournal_gx_inner_xR SEGS B PST ARx (G_SL B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS6 & HJin6 & HagS6).
pose proof HJin6 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (HFPC1 : ~ YI16.sink_open_fp ((SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks (gse_cap r0) outL))).
{ apply sink_closed_pos. constructor; [cbn [fst]; unfold SA; lia|]. unfold ablocks_fp. apply Forall_map.
  apply Forall_forall. intros [b m] Hb. cbn [fst].
  assert (Hb4 : In (b, m) (ablocks B ly4 S4))
  by (apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [exact (HX4 _ (GX _ Hb)) | exact (HX4 _ (OX _ Hb))]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m HAR5 Hb4) as (_ & H4096 & _). lia. }
assert (KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem ms0) a).
{ intros a Ha Ho He Hps Hg. rewrite (G3 a Ha Ho He Hps (fp_spares_closed _ a HFPC1)).
  apply HagS6. rewrite unsigned_lit_small; [exact Hg|]. pose proof (Hsegs a Ha). unfold kLowMemEnd in *. lia. }
assert (NGN : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 1%nat).
assert (VN5a : val_mem SEGS (mrestrict (w_H W4) (ms_mem ms0)) (rg_nsrc RG) 4 n)
by (apply (val_mem_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem ms0)); [intros q _; apply AV2 | exact VN4]).
assert (VN5 : val_mem SEGS (mrestrict (w_H W5) mem5) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H W4) (w_H W5) (ms_mem ms0) mem5); [|exact VN5a].
  intros q Hq. destruct (HPLAIN (rg_nsrc RG + q) (Hnsrc (rg_nsrc RG + q) ltac:(lia))) as (Hq1 & Hq2 & Hq3).
  exact (KG _ Hq1 Hq2 Hq3 (PSTC _ (Hnsrc (rg_nsrc RG + q) ltac:(lia))) (NGN (rg_nsrc RG + q) ltac:(lia))). }
jafter_call_keep_pi HS 52%nat regs5 (mrestrict (w_H W5) mem5) HPsl [1]%nat HS6.
match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  apply (region_kept_val_at Ea _ _ 248%nat (rg_nsrc RG) 4 n);
  [change 248%nat with (A_OBJ 7); rewrite <- HV7; exact (HEIa (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | exact VN5a | exact VN5 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc Ea 52 (map (getr regs5) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regsL (rfl_extra T p (re_buf e) n)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (SHOK6 : sh_ok SEGS rfl_Bx [] Eb (mrestrict (w_H W5) mem5)) by constructor.
paj_run_tok_xR RUNR HS HJ6 SHOK6 Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. }
(* ---- the round's end state N (the last run wrote nothing): what RFI_xR at i + 1 and RFX_xR need ---- *)
lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem ms1)) |- _ => rename Hx into HFr3 end.
lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) mem5) (mrestrict (w_H W5) (ms_mem ms1)) |- _ => rename Hx into MG3 end.
assert (MEQ3 : forall x, mrestrict (w_H W5) (ms_mem ms1) x = mrestrict (w_H W5) mem5 x).
{ intros x. apply HFr3. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
assert (AV3 : forall a, aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W5) mem5 a) by (intros a; apply aview_eq_of; apply MEQ3).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
(* the read-only view after gestures_end: its journal at G_SL keeps it (rom_out of G_SL) *)
assert (ROM6 : rom_view SEGS W5 mem5).
{ eapply (ajournal_gx_rom_view_xR SEGS B PST ARx). all: first [exact LAWS | exact Hsegs | exact HJsl | exact HROMO | exact PSTR | exact ROM5]. }
assert (ROMN : rom_view SEGS W5 (ms_mem ms1)) by (intros a Ha; rewrite AV3; exact (ROM6 a Ha)).
assert (KNI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha Ho He Hps Hg. rewrite AV3, (KG a Ha Ho He Hps Hg), AV2, (KF3 a Ha Ho He). apply AV1. }
assert (RFW : forall a, inG rf_cells a -> writable_at SEGS (arm W5 (ms_mem ms1)) a).
{ intros a Ha. destruct (HPLAIN a Ha) as (Hi1 & _ & _). apply rf_writable_of_seg; [|exact (HWSEG a Ha)].
  apply (hidden_not_img SEGS W5). rewrite unsigned_lit_small; [exact Hi1|]. pose proof (Hsegs a Hi1). unfold kLowMemEnd in *. lia. }
assert (KCELL : forall lo len, (forall x, lo <= x < lo + len -> inG rf_cells x /\ ~ inG (G_SL B RG) x) ->
  forall q, lo <= q < lo + len -> abyte_kept WL memL W5 (ms_mem ms1) q).
{ intros lo len Hc q Hq. destruct (Hc q Hq) as [Hq1 Hq2]. destruct (HPLAIN q Hq1) as (Hi1 & Ho1 & He1).
  split; [exact (KNI q Hi1 Ho1 He1 (PSTC q Hq1) Hq2) | intros _; exact (RFW q Hq1)]. }
assert (NGL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 0%nat).
assert (NGG : forall a, GL <= a < GL + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_lo HSEPO 3%nat).
assert (NGS : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 12%nat).
assert (NGC : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ inG (G_SL B RG) a) by (rfl_ng_hi HSEPO 13%nat).
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 1%nat _ 12 a eq_refl Ha)).
assert (ICS : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 4%nat _ 4 a eq_refl Ha)).
assert (IGL : forall a, GL <= a < GL + 4 -> inG rf_cells a) by (intros a Ha; exact (in_rf_cell 6%nat _ 4 a eq_refl Ha)).
assert (VNN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_nsrc RG) 4 n).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HNS]. intros q Hq.
  exact (proj1 (KCELL (rg_nsrc RG) 4 (fun x Hx => conj (Hnsrc x Hx) (NGN x Hx)) (rg_nsrc RG + q) ltac:(lia))). }
assert (VSN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HSRC]. intros q Hq.
  exact (proj1 (KCELL (rg_src RG) 8 (fun x Hx => conj (Hsrc x Hx) (NGS x Hx)) (rg_src RG + q) ltac:(lia))). }
assert (VCN : val_mem SEGS (arm W5 (ms_mem ms1)) (rg_capsrc RG) 4 16).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HCAP]. intros q Hq.
  exact (proj1 (KCELL (rg_capsrc RG) 4 (fun x Hx => conj (ICS x Hx) (NGC x Hx)) (rg_capsrc RG + q) ltac:(lia))). }
assert (WNN : awr W5 (ms_mem ms1) (rg_nsrc RG) 4) by (intros j Hj; exact (RFW _ (Hnsrc (rg_nsrc RG + j) ltac:(lia)))).
assert (WSN : awr W5 (ms_mem ms1) (rg_src RG) 8) by (intros j Hj; exact (RFW _ (Hsrc (rg_src RG + j) ltac:(lia)))).
assert (WCN : awr W5 (ms_mem ms1) (rg_capsrc RG) 4) by (intros j Hj; exact (RFW _ (ICS (rg_capsrc RG + j) ltac:(lia)))).
assert (LKN : alock_at RG W5 (ms_mem ms1) true).
{ apply (alock_at_kept RG WL memL W5 (ms_mem ms1) true HLK). intros r [<- | []] a Har. cbn [fst snd] in Har.
  exact (KCELL (rg_lock RG) 12 (fun x Hx => conj (ILK x Hx) (NGL x Hx)) a Har). }
assert (GLN : exists lst, val_mem SEGS (arm W5 (ms_mem ms1)) GL 4 lst).
{ destruct HGLv as [lst Hl]. exists lst. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact Hl].
  intros q Hq. exact (proj1 (KCELL GL 4 (fun x Hx => conj (IGL x Hx) (NGG x Hx)) (GL + q) ltac:(lia))). }
assert (GLW : awr W5 (ms_mem ms1) GL 4) by (intros j Hj; exact (RFW _ (IGL (GL + j) ltac:(lia)))).
assert (HTBN : In (T, ATABLE) (ablocks B ly5 S5)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | left; reflexivity]).
(* the round's own stack frame [sp0 - 96, sp0) and the fake frame [F, F + 64) are kept: the callees run below
   sp0 - 96, and their journals keep every frame byte outside their footprints *)
pose proof HJi as (_ & HlyL & _ & _ & _ & HfrL & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJi4 as (_ & Hly4 & _).
assert (EFL : frame_addr lyL 0 fpos = F).
{ destruct HlyL as (_ & _ & _ & _ & _ & EF & _). unfold F, frame_addr. first [rewrite EF | rewrite <- EF]; reflexivity. }
assert (EF4 : frame_addr ly4 0 fpos = F).
{ destruct Hly4 as (_ & _ & _ & _ & _ & EF & _). unfold F, frame_addr. first [rewrite EF | rewrite <- EF]; reflexivity. }
assert (HfinL : In (0, fpos) (frames SL)) by (rewrite HfrL; left; reflexivity).
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite HFR4; exact HfinL).
assert (RSTK : 96 + ASTACK <= RF_STK) by (unfold RF_STK, RF_FRAME; pose proof (Z.le_max_r GSE_STK ASTACK); lia).
assert (KNF : forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (unfold ASTACK in RSTK; lia).
  rewrite AV3. rewrite (G1 a Hac ltac:(rewrite Usp5; lia)).
  rewrite HagS6; [rewrite AV2, (KF1 a Hac ltac:(lia)); apply AV1|].
  rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi1 _]. pose proof (Hsegs a Hi1).
  unfold kLowMemEnd in *. lia. }
assert (RSV : rf_saved W5 (ms_mem ms1) sp0 regs).
{ intros k0 Hk0. apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact (HSV k0 Hk0)].
  intros q Hq. apply KNF. lia. }
pose proof (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARL HfinL) as (Fa & Fb & _). rewrite EFL in Fa, Fb.
change (fs_frame_bytes 0) with 64 in Fb.
assert (KNK : forall a, F <= a < F + 64 -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H WL) memL a).
{ intros a Ha.
  assert (Hfr4 : in_zr a (frame_rng ly4 (0, fpos))) by (unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF4; change (fs_frame_bytes 0) with 64; lia).
  assert (HfrL' : in_zr a (frame_rng lyL (0, fpos))) by (unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFL; change (fs_frame_bytes 0) with 64; lia).
  rewrite AV3. rewrite (G4 0 fpos a Hfin4 (or_introl Hfr4)).
  - rewrite HagS6.
    + rewrite AV2. rewrite (KF4 0 fpos a HfinL (or_introl HfrL')); [apply AV1|].
      intros (Hc & Hr). destruct HBUF as [(Hc0 & _) | (Hc0 & Hin0)]; [lia|].
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyL SL _ WL memL mdL _ _ 0 fpos HARL Hin0 HfinL) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFL in D. change (fs_frame_bytes 0) with 64 in D. lia.
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi1 _].
      exact (frm_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ 0 fpos a HAR5 Hfin4 ltac:(rewrite EF4; change (fs_frame_bytes 0) with 64; lia) Hi1).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf].
    + pose proof (sep_block_frame_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ T ATABLE 0 fpos HAR5 HTB4 Hfin4) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF4 in D. change (req_size ATABLE) with 896 in D.
      change (fs_frame_bytes 0) with 64 in D. unfold SA in Hf. lia.
    + destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
      assert (Hin4' : In (b', m') (ablocks B ly4 S4))
      by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b' m' 0 fpos HAR5 Hin4' Hfin4) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF4 in D. change (fs_frame_bytes 0) with 64 in D. lia. }
assert (FLG : val_mem SEGS (arm W5 (ms_mem ms1)) (F + 56) 8 (flag_addr ly 0 fpos)).
{ apply (val_mem_kept SEGS (w_H WL) (w_H W5) memL (ms_mem ms1)); [|exact HFLG]. intros q Hq. apply KNK. lia. }
(* the entries the loop has not reached keep their bytes and blocks: none of them is in gestures_end's footprint *)
pose proof (Permutation_NoDup HPERM4 (rfl_ablocks_nodup _ _ _ _ _ _ HAR5)) as HND4.
assert (HRN : forall b, In b (rf_eblks (skipn (Datatypes.S i) es) ++ rest) -> In b (ablocks B ly5 S5))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; right; exact Hb]).
assert (EX : forall b, In b (rf_eblks (skipn (Datatypes.S i) es)) -> In b X)
by (intros b Hb; unfold X; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (KR : forall b m x, In (b, m) ((T, ATABLE) :: X) -> In (b, m) (ablocks B ly5 S5) ->
  ~ In (b, m) (gse_blks e ++ aout_blks (gse_cap r0) outL) -> b <= x < b + req_size m -> ~ (SA + 40 <= x < SA + 52) ->
  aview SEGS (w_H W5) (ms_mem ms1) x = aview SEGS (w_H WL) memL x).
{ intros b m x Hin Hin5 Hng Hx Hs. rewrite AV3.
  assert (Hin4 : In (b, m) (ablocks B ly4 S4)) by (destruct Hin as [<- | Hin]; [exact HTB4 | exact (HX4 _ Hin)]).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m HAR5 Hin4) as (_ & Hb4096 & Hbceil & _).
  replace x with (b + (x - b)) by lia. rewrite (G2 b m (x - b) Hin4 Hin5 ltac:(lia)).
  - rewrite HagS6.
    + replace (b + (x - b)) with x by lia. exact (KB b m x Hin Hx).
    + rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ (HSLG _ Hg)) as [Hi2 _].
      exact (blk_img_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m (b + (x - b)) HAR5 Hin4 ltac:(lia) Hi2).
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia|].
    destruct (inFP_ablocks_fp_inv _ _ Hf) as (b' & m' & Hin' & Hr').
    assert (Hin4' : In (b', m') (ablocks B ly4 S4))
    by (apply in_app_or in Hin'; destruct Hin' as [H' | H']; [exact (HX4 _ (GX _ H')) | exact (HX4 _ (OX _ H'))]).
    assert (Hne : (b, m) <> (b', m')) by (intros Heq; apply Hng; rewrite Heq; exact Hin').
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m b' m' HAR5 Hin4 Hin4' Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ENTN : forall j, (Datatypes.S i <= j < length es)%nat ->
  garr8 SEGS (arm W5 (ms_mem ms1)) (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0))) /\
  awr W5 (ms_mem ms1) (T + AENT * Z.of_nat j) AENT /\
  aheld_ok B ly5 S5 W5 (ms_mem ms1) (nth j es rf_e0) /\
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
    pose proof (sep_blocks_x SEGS B ARx LAWS ly4 S4 _ W4 (ms_mem ms0) _ b m T ATABLE HAR5 (HX4 _ (EX _ Hb)) HTB4 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D. lia. }
  split; [|split; [|split]].
  - apply (garr8_frame SEGS (arm WL memL) (arm W5 (ms_mem ms1)) _ _ Gj). intros x Hx.
    rewrite (rfl_len_entry _ Pj1 Pj2) in Hx. unfold arm. apply (mbyte_of_aview SEGS).
    apply (KR T ATABLE x (or_introl eq_refl) HTBN NGT); [change (req_size ATABLE) with 896; unfold AENT in Hx; lia | unfold SA, AENT in *; lia].
  - intros q Hq. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly5 S5 _ W5 (ms_mem ms1) _ T ATABLE HAR6 HTBN) as (_ & _ & _ & _ & HP & _).
    change (req_size ATABLE) with 896 in HP. exact (proj1 (HP (T + AENT * Z.of_nat j + q) ltac:(unfold AENT in *; lia))).
  - apply (rfl_aheld_ok_kept lyL SL WL memL ly5 S5 W5 (ms_mem ms1) _ Hj').
    + intros b Hb. apply HRN. apply in_or_app; left. apply EBj.
      change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
      apply in_or_app; right; exact Hb.
    + intros b m x Hb Hx.
      assert (HbE : In (b, m) (rf_eblks (skipn (Datatypes.S i) es))).
      { apply EBj. change (aentry_blks (nth j es rf_e0)) with (rfl_bblk (nth j es rf_e0) ++ gse_blks (nth j es rf_e0)).
        apply in_or_app; right; exact Hb. }
      pose proof (HrqG m) as Hm.
      apply (KR b m x (or_intror (EX _ HbE)) (HRN _ (in_or_app _ _ _ (or_introl HbE))) (NGj _ HbE)); [lia|].
      intros Hs. apply (NTj b m x HbE ltac:(lia)). unfold SA in Hs. lia.
  - destruct Bj as [Bj | (Bc & Bin)]; [left; exact Bj | right; split; [exact Bc|]].
    apply HRN. apply in_or_app; left. apply EBj. unfold aentry_blks.
    rewrite (proj2 (Z.eqb_neq (re_cap (nth j es rf_e0)) 0) ltac:(lia)). left; reflexivity. }
(* the stream, the blocks, presence, the meter and the model after round i *)
assert (AOUTN : aout_at B RG ly5 S5 W5 (ms_mem ms1) (gse_c r1) (gse_O r1) mx (gse_no r1) (gse_cap r1) out5).
{ apply (aout_at_kept B RG ly5 S5 W5 mem5 ly5 S5 W5 (ms_mem ms1) _ _ mx _ _ out5 HAOsl).
  - intros r Hr a Har. split; [apply AV3 | apply (writable_at_grows SEGS _ _ a MG3)].
  - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]. }
assert (PERMN : Permutation (ablocks B ly5 S5)
  (rf_tblk T ++ rf_eblks (skipn (Datatypes.S i) es) ++ aout_blks (gse_cap r1) out5 ++ rest)).
{ eapply Permutation_trans; [exact HPERMsl|]. unfold rf_tblk. rewrite (proj2 (Z.eqb_neq T 0) HT0). cbn [app].
  apply perm_skip. apply Permutation_app_swap_app. }
assert (APK : apres_kept B W mem W5 (ms_mem ms1)).
{ intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) mem5 (ms_mem ms1) a MG3). apply (HPKsl a Ha Ho He).
  apply (PR2 a Ha Ho He). exact (HPK a Ha Ho He Hpr). }
assert (MLE : mo_le MT S S5 (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)))
by (exact (mle_station MT S S4 S5 _ _ MLAW (mle_station MT S SL S4 spent (mo_free MT) MLAW HMLE HML4) HMOsl)).
assert (NNL : forall b, In b (ablocks B lyL SL) -> 0 <= snd b).
{ intros [bb mm] Hb. cbn [snd]. exact (BLKN lyL SL HpL WL memL mdL bb mm HARL Hb). }
assert (INL : forall b, In b ((T, ATABLE) :: rfl_bblk e ++ X) -> In b (ablocks B lyL SL))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM' | exact Hb]).
(* the room round's `- cap` threading (W_contract.v rf_room): the round frees the OLD g_out block (outL, gse_cap r0)
   and holds the new one (out5, gse_cap r1), so the rest's room grows only by gse_cap r1 - gse_cap r0; the old block's
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
assert (U23 : U Eb (SOff 23 1) = Z.of_nat i + 1).
{ apply (U_atom_off Eb 23 (Z.of_nat i) 1); [rewrite OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact H23 | lia | lia]. }
assert (U35 : U Eb (SOff 35 0) = n) by (apply (U_atom Eb 35 n); [rewrite OLDb, OLDa by lia; exact E35 | unfold n; lia]).
assert (RKF : forall regsF : bvmap 5 word,
  (forall r, In r [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv -> getr regsF r = getr regsL r) ->
  getr regsF 22 = ew Eb 289 -> rf_kept regs regsF sp0 F).
{ intros regsF HKN N22. unfold rf_kept.
  split; [unfold spZ in Ksp |- *; rewrite (HKN 2%bv ltac:(cbv; tauto)); exact Ksp|].
  split; [rewrite (HKN 3%bv ltac:(cbv; tauto)); exact K3|].
  split; [rewrite (HKN 4%bv ltac:(cbv; tauto)); exact K4|].
  split; [rewrite (HKN 26%bv ltac:(cbv; tauto)); exact K26|].
  split; [rewrite (HKN 27%bv ltac:(cbv; tauto)); exact K27|].
  split; [rewrite (HKN 8%bv ltac:(cbv; tauto)); exact K8|].
  split; [rewrite (HKN 18%bv ltac:(cbv; tauto)); exact K18|].
  split; [rewrite (HKN 19%bv ltac:(cbv; tauto)); exact K19|].
  split; [rewrite (HKN 20%bv ltac:(cbv; tauto)); exact K20|].
  split; [rewrite (HKN 21%bv ltac:(cbv; tauto)); exact K21|].
  rewrite N22. change 289%nat with (A_HI 9). exact (img_env_atomP Eb (A_HI 9) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia)). }
(* the branch and the jump to its target write nothing: every fact above carries to the final memory *)
assert (FIN : forall m, (forall a, aview SEGS (w_H W5) m a = aview SEGS (w_H W5) (ms_mem ms1) a) ->
  mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) m) ->
  rf_saved W5 m sp0 regs /\
  val_mem SEGS (arm W5 m) (F + 56) 8 (flag_addr ly 0 fpos) /\
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
  assert (KF : forall a, abyte_kept W5 (ms_mem ms1) W5 m a)
  by (intros a; split; [apply AVF | apply (writable_at_grows SEGS _ _ a MGF)]).
  split; [intros k0 Hk0; apply (val_mem_kept SEGS (w_H W5) (w_H W5) (ms_mem ms1) m); [intros q _; apply AVF | exact (RSV k0 Hk0)]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact FLG]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VNN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WNN]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VSN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WSN]|].
  split; [apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact VCN]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact WCN]|].
  split.
  { intros j Hj. destruct (ENTN j Hj) as (G1' & A1' & H1' & B1'). split; [|split; [|split]].
    - apply (akept_garr8 W5 (ms_mem ms1)); [intros x _; apply KF | exact G1'].
    - apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact A1'].
    - exact (rfl_aheld_ok_mem ly5 S5 W5 (ms_mem ms1) W5 m _ H1' AVF).
    - exact B1'. }
  split; [apply (alock_at_kept RG W5 (ms_mem ms1) W5 m true LKN); intros r _ a _; apply KF|].
  split; [apply (aout_at_kept B RG ly5 S5 W5 (ms_mem ms1) ly5 S5 W5 m _ _ mx _ _ out5 AOUTN);
    [intros r _ a _; apply KF
    | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERMsl | right; apply in_or_app; left; exact Hb]]|].
  split; [destruct GLN as [lst Hl]; exists lst; apply (akept_vm W5 (ms_mem ms1)); [intros x _; apply KF | exact Hl]|].
  split; [apply (akept_awr W5 (ms_mem ms1)); [intros x _; apply KF | exact GLW]|].
  intros a Ha Ho He Hpr. apply (apresent_grows (w_H W5) (ms_mem ms1) m a MGF). exact (APK a Ha Ho He Hpr). }
psrr_branch_tok RUNR BRR HS SHOK6 Bspan.
- (* i + 1 < |es|: back to the loop head, RFI_xR at i + 1 *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U23, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U23, ?U35; unfold n; lia). rewrite U23, U35 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 360).
  { apply awr_ok_x_of0. awr_ok_tac. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem ms1) a)
  by (intros a; apply aview_eq_of; apply Hx; intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & FLGF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  assert (ROMF : rom_view SEGS W5 (ms_mem msF)) by (intros a Ha; rewrite AV4; exact (ROMN a Ha));
  assert (E5F : garr8 SEGS (arm W5 (ms_mem msF)) (VAL A_lit_end5) (bzs END5))
  by (exact (rfl_end5_kept WL W5 memL (ms_mem msF) HROM ROMF HEND5));
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25.
  pmkst HS.
  apply (IH regs ly S Hp W mem md T es c O mx no cap out rest fpos (Datatypes.S i) ly5 S5 Hp5 W5); [lia | exact HCTXF | exact HCNT0 |].
  assert (RC : gse_c (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (ROo : gse_O (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap (firstn (Datatypes.S i) es)) = gse_cap r1) by (rewrite RUNS; reflexivity).
  refine (ex_intro _ _ (ex_intro _ out5 (ex_intro _ (spent + mo_free MT + gse_cost MT (gse_c r0) mx (gse_no r0) (gse_cap r0) (gse_keys e)) _))).
  rewrite RC, ROo, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact (RKF _ HKN2 N22)|].
  split; [exact HF0|].
  split; [rewrite N23, OLDb, OLDa, (EE 23%nat 23%bv eq_refl), H23 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N24, OLDb, OLDa, (EE 24%nat 24%bv eq_refl), H24 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite N25; change 290%nat with (A_HI 10); exact (img_env_atomP Eb (A_HI 10) HEIb ltac:(unfold A_HI, A_TEXT, A_LIM; lia))|].
  split; [exact RSVF|]. split; [exact FLGF|].
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
- (* i + 1 = |es|: the tail, RFX_xR *)
  cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. unfold U in U23, U35.
  rewrite !bv_signed_small in Hc by (rewrite ?U23, ?U35; unfold n; lia). rewrite U23, U35 in Hc. apply Z.ltb_ge in Hc.
  assert (Hlast : Datatypes.S i = length es) by (unfold n in Hc; lia).
  paj_run_to_tok_xR RUNTOR HS HJ6 SHOK6 Bspan (AF_fr_relay_finish + 424).
  { apply awr_ok_x_of0. awr_ok_tac. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ =>
  assert (AV4 : forall a, aview SEGS (w_H W5) (ms_mem msF) a = aview SEGS (w_H W5) (ms_mem ms1) a)
  by (intros a; apply aview_eq_of; apply Hx; intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin) end;
  lazymatch goal with Hx : mem_grows (mrestrict (w_H W5) (ms_mem ms1)) (mrestrict (w_H W5) (ms_mem msF)) |- _ => rename Hx into MG4 end;
  destruct (FIN (ms_mem msF) AV4 MG4) as (RSVF & FLGF & VNF & WNF & VSF & WSF & VCF & WCF & ENTF & LKF & AOUTF & GLF & GLWF & APKF);
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsL _ [2; 3; 4; 8; 18; 19; 20; 21; 26; 27]%bv HS HAEb ltac:(vm_compute; reflexivity)) as HKN2
  end.
  cbn [ms_regs restrict] in HKN2.
  prreg HS (22%bv : bv 5) N22.
  pmkst HS.
  assert (SK0 : skipn (Datatypes.S i) es = []) by (rewrite Hlast; apply skipn_all).
  assert (FA : firstn (Datatypes.S i) es = es) by (rewrite Hlast; apply firstn_all).
  rewrite SK0 in HSP, PERMN. cbn [rf_cost rf_eblks concat map app] in HSP, PERMN. rewrite FA in RUNS.
  assert (RC : gse_c (rf_run c O mx no cap es) = gse_c r1) by (rewrite RUNS; reflexivity).
  assert (ROo : gse_O (rf_run c O mx no cap es) = gse_O r1) by (rewrite RUNS; reflexivity).
  assert (RN : gse_no (rf_run c O mx no cap es) = gse_no r1) by (rewrite RUNS; reflexivity).
  assert (RK : gse_cap (rf_run c O mx no cap es) = gse_cap r1) by (rewrite RUNS; reflexivity).
  apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest fpos ly5 S5 Hp5 W5).
  refine (ex_intro _ _ (ex_intro _ out5 _)).
  rewrite RC, ROo, RN, RK.
  split; [exact HJ6|].
  split; [exact HEF|].
  split; [exact (RKF _ HKN2 N22)|].
  split; [exact HF0|].
  split; [exact RSVF|]. split; [exact FLGF|].
  split; [exact VNF|].
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
(* :2464 rf_region_kept_stack_aj_x over the journal at R *)
Lemma rf_region_kept_stack_aj_xR : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_xR (SK := SK) SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof using RG.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; zlia.
- intros _. apply (apresent_writable SEGS). apply Hpres. zlia.
Qed.
(* :2485 rf_entry_seg at R *)
Lemma rf_entry_seg_xR : rf_tail_stmt_xR -> rf_loop_stmt_xR -> rf_spec_xR B PST ARx R MT RP MMAX G RG GTU GL CTX A_relay_finishP.
Proof using ALOCK ASM0 FFL HBcell HBgot HE5R HIG HPLAIN HPLAINO HROMG HROMO HSEPG HSEPO HV3 HV6 HV7 HWSEG IMGC MO_FR OWNLOW PSTC PSTO PSTR RGAL RUN0R RUNCR RUNR RUNTOR R_refl R_trans SMALLOC TLF WFL WLE_R.
intros TAIL LOOP.
unfold rf_spec_xR. intros W ly S Hp regs mem md ch T es c O mx no cap out rest
HPRE Hal32 HCNT HGTU0 HLOCK HREL HGLv HGLw HOUT HPERM HEND5 HROM HG1 HG2 HG3 HROOM HTOPR HCTX HMOK kr HRMe HCNTe.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rf_entry W ly S Hp regs mem md ch HPRE Hal32 HGTU0) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
(* HSEPG stays folded (zseps is opaque to lia); a separation is picked with zsep_pick right where it is used and
   cleared after: every explicit disjunction left in the context multiplies the cost of each later lia. *)
(* every block of the footprint is a live block of the caller, hence positive: the sink's own word is not in it *)
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
assert (WS : RF_STK = 16704) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the prologue writes no global: it runs on the donor's journal from the entry memory, which is packed into the
   ajournal_gx with gagree_refl when the first global is written (W6's form, W_relay_instance_gone.v:346) *)
pose proof (ajournal_x_initR (SK := SK) SEGS B PST ARx R_refl RF_STK (rf_FP T es cap out) ly S Hp W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs rf_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rf_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_relay_finishP) with (Z_to_bv 64 A_relay_finishP). unfold A_relay_finishP, A_relay_finish.
paj_run_tok_x RUN0R HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
pose proof (palf_uar_img B TLF) as HuR.
assert (IGTU : forall x, GTU <= x < GTU + 1 -> inG rf_cells x) by (intros x Hx; exact (in_rf_cell 0%nat GTU 1 x eq_refl Hx)).
pose proof (HPLAIN GTU ltac:(apply IGTU; lia)) as (HGTUi & HGTUo & HGTUe).
pose proof (proj1 (Forall_forall _ _) HIG (GTU, 1) ltac:(left; reflexivity)) as HGTUb. cbn [fst snd] in HGTUb.
(* the g_thread_up byte keeps its value across the prologue run (which writes only the frame) *)
assert (KG1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) GTU 1 0).
{ apply (keep_vm_frame E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) GTU 1 0 HFr ltac:(lia) ltac:(cbn; lia)); [|exact HGTU0].
  intros x Hx (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    revert Hr; unfold RF_FRAME; clear - Hx Hslo Hshi H47 Hceil C1 C3 Hstk0 HGTUb; lia | ]).
  destruct Hin. }
(* the call to __asan_stack_malloc_0 (64): the fake frame *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ apply (YA0nH.SRr_SRrG SEGS R WLE_R).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_xR SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC R_trans WLE_R 0 ASM0 ltac:(lia)
  W rg mm RF_STK (spZ regs)
  (rf_FP T es cap out) ly S Hp W mem md [] ly S Hp _ 0 (-96) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPRS & HKR & HFS).
(* the room round: the seat's state is a set_fs of S, so rp_RPF carries the spec's room to it (the lock keeps it) *)
assert (HRM2 : rp_RM RP S2 (Z.to_nat (rf_cost MT_rk c O mx no cap es) + kr))
by (destruct HFS as (f & ->); exact (rp_RPF RP _ _ _ HRMe)).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (proj1 (proj2 (proj2 HK))) as HK3.
assert (KG2 : val_mem SEGS (mrestrict (w_H W) mem2) GTU 1 0)
by (apply (keep_vm_img W W (ms_mem ms) mem2 GTU 1 0 HK3 IGTU KG1)).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
  - eapply rf_region_kept_stack_aj_xR; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 3) GTU 1 0);
    [rewrite (HEI (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact HV3 | exact KG1 | exact KG2 | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rf_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0's new atom), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 38%nat 33%nat 512%nat 0 F FL HS eq_refl ltac:(vm_compute; reflexivity)
RF' E33a ltac:(lia) ltac:(lia) ltac:(left; reflexivity) HFal ltac:(lia) ltac:(change (fs_frame_bytes 0) with 64; lia)
ltac:(lia)
ltac:(intros a Ha; exact (proj1 (HFpres a ltac:(change (fs_frame_bytes 0) with 64 in Ha; lia))))
ltac:(intros i Hi; unfold shadow_addr; rewrite <- SB_SHADOW_OFF;
exact (proj1 (HFSpres i ltac:(change (fs_frame_bytes 0 / 8) with 8 in Hi; lia))))
ltac:(change (fs_frame_bytes 0) with 64; exact Hflag)
ltac:(change (fs_frame_bytes 0) with 64; exact Hz)) as HS3.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS3.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL)
by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rf_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E33a).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as Dq; rewrite HFal in Dq; lia).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as Dm. rewrite HFal, Z.add_0_r in Dm. rewrite Dm at 1.
  replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by exact (HEIb (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U244 : bv_unsigned (ew Eb 244) = GTU) by (rewrite <- HV3; exact (HEIb (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (U273 : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by exact (HEIb (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 32)).
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFimg, HFapp.
pose proof (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, ff_fregion, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U38, U2b, U241, U242, U244, U273, U32b;
repeat split; lia) ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64;
rewrite U513, U38, U2b, U241, U242, U244, U273, U32b; unfold SB; repeat split; lia)) as HS4.
clear HS HS3. rename HS4 into HS. unfold ff_seated, ff_facts_ss, ff_fregion, ff_sregion in HS. norm_ss HS.
(* the frame header and the shadow poison, the g_thread_up test and the store of the frame pointer: a plain run
   (the token run keeps its windows off the shadow); it ends at the call to pthread_mutex_lock *)
paj_run_shc_x RUNPR RUNCR HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
    first [ lia
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
(* the call to pthread_mutex_lock (&g_lock) *)
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
eassert (HJX : ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md
  _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_xR; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed _ a HFPC)). }
pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (ILK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG rf_cells a)
by (intros a Ha; exact (in_rf_cell 1%nat (rg_lock RG) 12 a eq_refl Ha)).
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(right; left; reflexivity)) as HLKb. cbn [fst snd] in HLKb.
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
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
assert (LKtb : aview SEGS (w_H W) (ms_mem ms0) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms0) = spZ regs + -96).
{ unfold spZ at 1. rewrite QSP, U2b. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP Eb (A_OBJ 6) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV6. reflexivity. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite QTP, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
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
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ2) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKx. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HKx))).
      apply HG1. unfold RF_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
(* ---- back in relay_finish, the lock held.  The call wrote only the lock word and its own stack, so every
   region of the state at the call is kept; the state after it is the same one with the caller-saved atoms
   havoc'd (the GUIDE's jafter_call_keep_pi). ---- *)
zsep_pick HSEPG 0%nat 5%nat DL1. zsep_pick HSEPG 1%nat 5%nat DL2. zsep_pick HSEPG 2%nat 5%nat DL3.
zsep_pick HSEPG 3%nat 5%nat DL4. zsep_pick HSEPG 4%nat 5%nat DL5.
assert (KEEP3 : forall a,
  (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (spZ regs - 96 <= a < spZ regs) \/
  (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) \/ (VAL (A_OBJ 32) <= a < VAL (A_OBJ 32) + 8) \/
  (VAL (A_OBJ 1) <= a < VAL (A_OBJ 1) + 8) \/ (as_uar_cell B <= a < as_uar_cell B + 4) \/ (GTU <= a < GTU + 1) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply Hfr3.
  - clear -Ha HF4096 HFceil HFhigh HF8lo HF8hi HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB in *. lia.
  - clear -Ha HLKb DL1 DL2 DL3 DL4 DL5 HFimg HF8lo HF8hi HF4096 HFceil HFhigh Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB in *. lia.
  - clear -Ha HLKb HFapp HF4096 HFceil HFhigh HF8lo HF8hi HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS.
    unfold SB, ESTACK in *. lia. }
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 513%nat (SB + F / 8));
    [exact U513 | intros a Ha; apply KEEP3; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 38%nat F);
    [exact U38 | intros a Ha; apply KEEP3; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 2%nat (spZ regs));
    [exact U2b | intros a Ha; apply KEEP3; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 241%nat (VAL (A_OBJ 0)));
    [exact U241 | intros a Ha; apply KEEP3; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 273%nat (VAL (A_OBJ 32)));
    [exact U273 | intros a Ha; apply KEEP3; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 242%nat (VAL (A_OBJ 1)));
    [exact U242 | intros a Ha; apply KEEP3; right; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 32%nat (as_uar_cell B));
    [exact U32b | intros a Ha; apply KEEP3; right; right; right; right; right; right; left; lia | exact Hpres3].
  - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 244%nat GTU);
    [exact U244 | intros a Ha; apply KEEP3; right; right; right; right; right; right; right; lia | exact Hpres3]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* The token runner keeps its regions off the shadow span, so drop the fake frame's shadow region (the head of the
   state) for the rest of this segment: nothing from here to either cut point reads or writes it, and what the cut
   points say about it is semantic (W_relay_add.v:1013-1021 drops it the same way). *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 513%nat) _ _ _ _ _ :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx rest HS ltac:(vm_compute; apply submem_drop; apply submem_refl)
    ltac:(vm_compute; reflexivity)) as HS3
end end.
clear HS. rename HS3 into HS. norm_ss HS.
(* ... and the fake frame itself read-only (an empty window): cells_safe_b asks every write window to be apart from
   the shadow span, and the fake frame's atom ranges over the whole app region.  Nothing of this segment writes it
   (W_relay_add.v:1022-1031 does the same before its own token run). *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 38%nat) ?lo ?hi ?wlo ?whi ?cs :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx (YP09.mkRegion (Some 38%nat) lo hi 0 0 cs :: rest) HS
    ltac:(vm_compute; apply submem_keep; [unfold subregion; cbn; split; [reflexivity|]; split; [lia|]; split; [lia|];
          split; [left; lia | auto] | apply submem_refl])
    ltac:(vm_compute; reflexivity)) as HS4
end end.
clear HS. rename HS4 into HS. norm_ss HS.
(* the env after the call: the caller-saved atoms are new, atoms 512 and 513 (the fake frame) are not *)
assert (HCL : length CLOB = 16%nat) by (vm_compute; reflexivity).
remember (YN3v.havoc Eb 66 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 66)%nat -> ew Ec m = ew Eb m)
by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (HIc : forall m, (82 <= m)%nat -> ew Ec m = ew Eb m)
by (intros m Hm; rewrite HEc; apply ew_havoc_above; rewrite length_map, HCL; lia).
assert (HAEc : env_agree 32 (Ereg regs rf_extra) Ec)
by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
(* the relay's count, as the walk finds it: |es| in both arms of ra_rel (T = 0 forces es = []) *)
assert (NS0 : val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr W mem (rg_nsrc RG) 4).
{ destruct HREL as [(HT0 & Hes0 & (_ & _ & Hv & Hw & _)) | (_ & _ & Hv & Hw & _)];
  [rewrite Hes0; cbn [length Z.of_nat]; split; [exact Hv | exact Hw] | split; [exact Hv | exact Hw]]. }
assert (IGB : forall a, inG rf_cells a -> 0x10000 <= a /\ a < 0x5fb000).
{ intros a Ha. unfold inG, rf_cells in Ha. apply Exists_exists in Ha. destruct Ha as ((lo, sz) & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) HIG (lo, sz) Hin) as Hbb. unfold in_zr in Hr.
  cbn [fst snd] in Hbb, Hr. lia. }
assert (KC3 : forall a, inG rf_cells a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnl. destruct (HPLAIN a Ha) as (Hi & Ho & He). destruct (IGB a Ha) as (Hb1 & Hb2).
  rewrite (Hfr3 a ltac:(lia) Hnl ltac:(clear -Hb1 Hb2 Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He (PSTC a Ha)). }
zsep_pick HSEPG 5%nat 6%nat DLN.
assert (NS3 : val_mem SEGS (arm W mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 (Z.of_nat (length es)));
  [intros k Hk; apply KC3; [apply (in_rf_cell 2%nat (rg_nsrc RG) 4 (rg_nsrc RG + k) eq_refl); lia | lia]
  | exact (proj1 NS0)]. }
assert (NSB : (length es <= 16)%nat).
{ destruct HREL as [(_ & Hes0 & _) | (_ & _ & _ & _ & _ & _ & Hle & _)]; [rewrite Hes0; cbn [length]; lia | exact Hle]. }
(* the g_nsrc cell as a region: the lw at 0x82440 reads it through the object atom (HV7) *)
pose proof (st_ok_pi_havoc_hi 514 Ec _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (YN3v.havoc Ec 514 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc_hi; [exact HEIc | cbv; lia]).
assert (OLDd : forall m, (m < 514)%nat -> ew Ed m = ew Ec m)
by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E514 : ew Ed 514 = Z_to_bv 64 (Z.of_nat (length es)))
by (rewrite HEd; exact (ew_havoc_new Ec 514 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rf_extra) Ed)
by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
clear HEd.
assert (U2d : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd, OLDc by lia; exact U2b).
assert (U38d : bv_unsigned (ew Ed 38) = F) by (rewrite OLDd, OLDc by lia; exact U38).
assert (U513d : bv_unsigned (ew Ed 513) = SB + F / 8) by (rewrite OLDd, HIc by lia; exact U513).
assert (U241d : bv_unsigned (ew Ed 241) = VAL (A_OBJ 0)) by (rewrite OLDd, HIc by lia; exact U241).
assert (U242d : bv_unsigned (ew Ed 242) = VAL (A_OBJ 1)) by (rewrite OLDd, HIc by lia; exact U242).
assert (U244d : bv_unsigned (ew Ed 244) = GTU) by (rewrite OLDd, HIc by lia; exact U244).
assert (U273d : bv_unsigned (ew Ed 273) = VAL (A_OBJ 32)) by (rewrite OLDd, HIc by lia; exact U273).
assert (U32d : bv_unsigned (ew Ed 32) = as_uar_cell B) by (rewrite OLDd, OLDc by lia; exact U32b).
assert (U248d : bv_unsigned (ew Ed (A_OBJ 7)) = rg_nsrc RG)
by (rewrite <- HV7; exact (HEId (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB7 : base_val Ed (Some (A_OBJ 7)) = rg_nsrc RG) by (cbn [base_val]; exact U248d).
zsep_pick HSEPG 0%nat 6%nat DN1. zsep_pick HSEPG 1%nat 6%nat DN2. zsep_pick HSEPG 2%nat 6%nat DN3.
zsep_pick HSEPG 3%nat 6%nat DN4. zsep_pick HSEPG 4%nat 6%nat DN5.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; right; left; reflexivity)) as HNSb.
cbn [fst snd] in HNSb.
pose proof (st_ok_pi_add_region Ed _ _
  (YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 514 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
        rewrite VB7; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        constructor; [|constructor];
        apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 514 0) (Z.of_nat (length es)));
        [cbn [sv_denot]; rewrite E514, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        rewrite Z.add_0_r; exact NS3)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
        let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U248d, ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d;
        revert DN1 DN2 DN3 DN4 DN5 HNSb HF4096 HFceil HFhigh HFimg HFapp HF8lo HF8hi
               HgotR HcellR HguR HuR HGTUb Hslo Hshi H47 Hceil Hstk0 C1 C3 WS; clear; intros;
        unfold SB in *; repeat split; lia)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
(* ---- THE TRANSPORT BLOCK: what both arms of the blez need of the memory, carried from the entry memory to the
   lock's return and from there to either arm's own memory. ---- *)
pose proof pa_img_range as Himg.
(* errno is a byte of G (it is in G_SL), so the image and the allocator's statics are decided for it *)
assert (HERRG : forall a, as_errno B <= a < as_errno B + 4 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros a Ha. destruct (HG a (HG2 a ltac:(unfold G_SL, inG;
    do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))) as (Hei & Heo & _).
  split; [exact Hei | exact Heo]. }
assert (HEO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (as_errno B + i)) (as_owned_static B))
  by (intros i Hi; exact (proj2 (HERRG (as_errno B + i) ltac:(lia)))).
(* ... hence not aowned, before the fake-frame seat and after it: what the seat's RAW frame clause asks *)
assert (HNOWN : forall a, as_errno B <= a < as_errno B + 4 ->
  ~ aowned B ly S a /\ ~ aowned B ly S2 a).
{ intros a Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
  split; [ exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) ly S Hp W (ms_mem ms) _ HARa HEO
                    (a - as_errno B) ltac:(lia))
         | exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) ly S2 Hp W mem2 md2 HARb HEO
                    (a - as_errno B) ltac:(lia)) ]. }
(* an image byte off the lock word keeps its view from the entry to the lock's return *)
assert (KIMGA : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps Hnl. pose proof (Hsegs a Hi) as Hlow.
  rewrite (Hfr3 a ltac:(clear -Hlow C5; lia) Hnl
    ltac:(clear -Hlow Hslo Hceil C1 C5 WS; unfold ESTACK; lia)).
  exact (KIMG a Hi Ho He Hps). }
(* errno's four bytes keep their view across the whole prologue.  Across the fake-frame seat that is HKR, the
   seat's RAW frame clause (aj_stack_malloc_pres_at_raw): acall_kept's image clause excepts errno and cannot. *)
assert (KERR : forall a, as_errno B <= a < as_errno B + 4 ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) by
 (intros a Ha;
  pose proof (Himg a (proj1 (HERRG a Ha))) as Hb;
  zsep_pick HSEPG 5%nat 11%nat SE1;
  rewrite (Hfr3 a ltac:(clear -Hb; lia) ltac:(clear -Ha Hb SE1; lia)
    ltac:(clear -Hb Hslo Hceil C1 WS; unfold ESTACK; lia));
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(clear -Hb; lia)
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
        clear -Hr Hb HFimg HF8lo Hslo Hceil C1 WS; unfold SB in *; lia | ]);
      destruct Hin));
  rewrite (HKR a ltac:(clear -Hb; lia) (proj1 (HNOWN a Ha)) (proj2 (HNOWN a Ha))
    ltac:(clear -Hb Hslo Hceil C1 WS; unfold ESTACK; lia));
  apply (aview_kept_out E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) HFr a ltac:(clear -Hb; lia));
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    clear -Hr Hb Hslo Hceil C1 WS; unfold RF_FRAME in *; lia | ]);
  destruct Hin).
(* a byte of a live block keeps its view from the entry to the lock's return: no step of the prologue writes it
   (the runs write only the frame, the fake frame and its shadow; the two calls keep every block byte) *)
assert (KHEAP : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W) mem3 (p + i) = aview SEGS (w_H W) mem (p + i)) by
 (intros p n i Hin Hi;
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & _);
  pose proof (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ p n (p + i) HAR Hin ltac:(lia)) as Hxn;
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 _ W mem2 md2 p n 0 fpos HARb
    ltac:(rewrite Eab; exact Hin) Hfin2) as Hsep;
  unfold zdisjoint in Hsep; cbn [fst snd] in Hsep;
  change (fs_frame_bytes 0) with 64 in Hsep; fold F in Hsep;
  rewrite (Hfr3 (p + i) ltac:(clear -Hp4096 Hpceil Hi C1; lia)
    ltac:(intros Hl; apply Hxn; exact (proj1 (HPLAIN (p + i) (ILK (p + i) ltac:(lia)))))
    ltac:(clear -Hp4096 Hpceil Hi Hceil Hslo WS C1; unfold ESTACK; lia));
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 (p + i)
    ltac:(clear -Hp4096 Hpceil Hi C1; lia)
    ltac:(intros (r & Hin2 & Hr);
      lazymatch type of Hin2 with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin2 end;
      cbn [In] in Hin2;
      repeat (destruct Hin2 as [<- | Hin2];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U244, ?U273, ?U32b in Hr;
        first
        [ exact (fshadow_not_app F 8 p (req_size n) (p + i) ltac:(clear -HF4096; lia)
            ltac:(clear -HFceil C1; lia) Hpapp ltac:(clear -Hr; unfold SB in Hr; lia)
            ltac:(clear -Hi; lia))
        | clear -Hr Hp4096 Hpceil Hi Hsep Hceil Hslo WS C1; lia ] | ]);
      destruct Hin2));
  rewrite (proj1 (proj2 HK) p n i Hin Hi ltac:(intros []));
  apply (aview_kept_out E (ss_mem ss_rf0) (w_H W) mem (ms_mem ms) HFr (p + i)
    ltac:(clear -Hp4096 Hpceil Hi C1; lia));
  intros (r & Hin2 & Hr);
  lazymatch type of Hin2 with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin2 end;
  cbn [In] in Hin2;
  repeat (destruct Hin2 as [<- | Hin2];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    clear -Hr Hp4096 Hpceil Hi Hceil Hslo WS C1; lia | ]);
  destruct Hin2).
(* presence of image bytes, from the entry to the lock's return *)
assert (KPRES : forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a) by
 (intros a Hi Hpr; apply Hpres3; apply (apresent_grows (w_H W) mem2 (ms_mem ms0) a HG4);
  apply HPRS; [exact Hi | exact (apresent_grows (w_H W) mem (ms_mem ms) a HG0 Hpr)]).
(* ---- the carry: any later memory whose only write window is the frame [sp0 - 96, sp0) keeps the four transport
   facts and the rom_view.  Both arms of the blez pass their own run's frame_of and mem_grows here. ---- *)
assert (CARRY : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
  /\ (forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
  /\ (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
       aview SEGS (w_H W) m' (p + i) = aview SEGS (w_H W) mem (p + i))
  /\ (forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m' a)
  /\ rom_view SEGS W m') by
 (intros m' md' CK CG HARm;
  split;
  [ intros a Hi Ho He Hps Hnl; pose proof (Hsegs a Hi) as Hlow;
    rewrite (CK a ltac:(clear -Hlow C5; lia) ltac:(clear -Hlow C5 Hceil Hslo WS C1; lia));
    exact (KIMGA a Hi Ho He Hps Hnl)
  | split;
  [ intros a Ha; pose proof (Himg a (proj1 (HERRG a Ha))) as Hb;
    rewrite (CK a ltac:(clear -Hb; lia) ltac:(clear -Hb Hceil Hslo WS C1; lia));
    exact (KERR a Ha)
  | split;
  [ intros p n i Hin Hi;
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _);
    rewrite (CK (p + i) ltac:(clear -Hp4096 Hpceil Hi C1; lia)
      ltac:(clear -Hp4096 Hpceil Hi Hceil Hslo WS C1; lia));
    exact (KHEAP p n i Hin Hi)
  | split;
  [ intros a Hi Hpr; exact (apresent_grows (w_H W) mem3 m' a CG (KPRES a Hi Hpr))
  | intros a Ha;
    destruct (HROMO a Ha) as (HnG & Hpin & Hne & Hnh);
    assert (Hi : in_img SEGS a)
      by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]);
    assert (Hd : forall r : Z * Z, {in_zr a r} + {~ in_zr a r})
      by (intros r; unfold in_zr;
          destruct (Z_le_gt_dec (fst r) a); destruct (Z_lt_ge_dec a (fst r + snd r));
          [left; lia | right; lia | right; lia | right; lia]);
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno];
    [ exact (rom_pinned_view_x SEGS B ARx LAWS ly S2 Hp W m' md' a HARm (Hpin Hown))
    | pose proof (Hsegs a Hi) as Hlow;
      rewrite (CK a ltac:(clear -Hlow C5; lia) ltac:(clear -Hlow C5 Hceil Hslo WS C1; lia));
      rewrite (KIMGA a Hi Hno Hne (PSTR a Ha)
        ltac:(intros Hl; apply (HROMG a ltac:(left; unfold RF_G, inG; apply Exists_cons_hd;
              unfold in_zr; cbn [fst snd]; lia)); exact Ha));
      exact (HROM a Ha) ] ]]]]).
(* the four relay/listen cells this walk carries: image bytes, not allocator statics, not errno, off the lock word *)
assert (CELLOK : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
   \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) ->
   in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
   /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) by
 (intros a Ha;
  zsep_pick HSEPG 5%nat 6%nat L6; zsep_pick HSEPG 5%nat 7%nat L7;
  zsep_pick HSEPG 5%nat 8%nat L8; zsep_pick HSEPG 5%nat 10%nat L10;
  destruct Ha as [HA1 | [HA1 | [HA1 | HA1]]];
  [ destruct (HPLAIN a (in_rf_cell 2%nat (rg_nsrc RG) 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 3%nat (rg_src RG) 8 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 4%nat (rg_capsrc RG) 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1)
  | destruct (HPLAIN a (in_rf_cell 6%nat GL 4 a eq_refl ltac:(lia))) as (Hi1 & Ho1 & He1) ];
  (split; [exact Hi1 | split; [exact Ho1 | split; [exact He1 | clear -HA1 L6 L7 L8 L10; lia]]])).
(* ... and none of them is a byte of the program statics PST (PSTC) *)
assert (CELLPST : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
   \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) -> ~ Exists (in_zr a) PST) by
 (intros a Ha; destruct Ha as [HA1 | [HA1 | [HA1 | HA1]]];
  [ exact (PSTC a (in_rf_cell 2%nat (rg_nsrc RG) 4 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 3%nat (rg_src RG) 8 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 4%nat (rg_capsrc RG) 4 a eq_refl HA1))
  | exact (PSTC a (in_rf_cell 6%nat GL 4 a eq_refl HA1)) ]).
(* the controller's cells of aout_at: the same four properties *)
assert (AOUTK : forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8)
   \/ (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8)
   \/ (rg_client RG <= a < rg_client RG + 4)
   \/ (rg_client_broken RG <= a < rg_client_broken RG + 1)
   \/ (rg_send_dead RG <= a < rg_send_dead RG + 1)
   \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
   in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
   /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) by
 (intros a Ha;
  zsep_pick HSEPO 0%nat 2%nat D2; zsep_pick HSEPO 0%nat 4%nat D4; zsep_pick HSEPO 0%nat 5%nat D5;
  zsep_pick HSEPO 0%nat 6%nat D6; zsep_pick HSEPO 0%nat 7%nat D7; zsep_pick HSEPO 0%nat 8%nat D8;
  zsep_pick HSEPO 0%nat 9%nat D9; zsep_pick HSEPO 0%nat 10%nat D10;
  zsep_pick HSEPO 2%nat 11%nat E2; zsep_pick HSEPO 4%nat 11%nat E4; zsep_pick HSEPO 5%nat 11%nat E5;
  zsep_pick HSEPO 6%nat 11%nat E6; zsep_pick HSEPO 7%nat 11%nat E7; zsep_pick HSEPO 8%nat 11%nat E8;
  zsep_pick HSEPO 9%nat 11%nat E9; zsep_pick HSEPO 10%nat 11%nat E10;
  destruct Ha as [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | [HA1 | HA1]]]]]]];
  [ destruct (HPLAINO a ltac:(left; lia)) as (Hi1 & Ho1 & He1)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E5; lia)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 3 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E6; lia)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; do 4 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E7; lia)
  | destruct (HG a (HG1 a ltac:(unfold RF_G, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4))
      by (exact (HG3 a ltac:(unfold RF_G, inG; do 2 apply Exists_cons_tl; apply Exists_cons_hd;
          unfold in_zr; cbn [fst snd]; lia)))
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E8; lia)
  | destruct (HPLAINO a ltac:(right; lia)) as (Hi1 & Ho1 & He1)
  | destruct (HG a (HG2 a ltac:(unfold G_SL, inG; apply Exists_cons_tl; apply Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia))) as (Hi1 & Ho1 & _);
    assert (He1 : ~ (as_errno B <= a < as_errno B + 4)) by (clear -HA1 E10; lia) ];
  (split; [exact Hi1 | split; [exact Ho1 | split; [exact He1 |
     clear -HA1 D2 D4 D5 D6 D7 D8 D9 D10; lia]]])).
assert (RFE_EB : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat) by
 (intros e P1 P2; unfold entry_bytes; rewrite !length_app, P1, P2; cbn; reflexivity).
assert (RFE_KP : forall ks, length (key_ptrs ks) = (8 * length ks)%nat) by
 (intros ks; induction ks as [|k ks IH]; [reflexivity|];
  unfold key_ptrs in *; cbn [map concat length]; rewrite length_app, IH; cbn; lia).

assert (RFE_SPLIT : forall (l : list rentry), (forall e, In e l -> length (entry_bytes e) = 56%nat) ->
  forall j, (j < length l)%nat ->
  exists l1 l2, concat (map entry_bytes l) = l1 ++ entry_bytes (nth j l rf_e0) ++ l2 /\
                length l1 = (56 * j)%nat) by
 (induction l as [|e l IH]; intros Hl j Hj; [cbn [length] in Hj; lia|];
  destruct j as [|j];
  [ exists (@nil byte), (concat (map entry_bytes l)); cbn [concat map nth app]; split; reflexivity
  | cbn [length] in Hj;
    destruct (IH ltac:(intros x Hx; apply Hl; right; exact Hx) j ltac:(lia)) as (l1 & l2 & Heq & Hlen);
    exists (entry_bytes e ++ l1), l2; cbn [concat map nth];
    rewrite Heq, !app_assoc; split; [reflexivity|];
    rewrite length_app, Hlen, (Hl e ltac:(left; reflexivity)); lia ]).

assert (RFE_HELD : forall ly1 S1 (W1 : world SEGS) mem1 e,
  aentry_ok B ly1 S1 W1 mem1 e -> aheld_ok B ly1 S1 W1 mem1 e) by
 (intros ly1 S1 W1 mem1 e
    (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15);
  split; [exact Q3|]; split; [exact Q4|]; split; [exact Q11|]; split; [exact Q12|];
  split; [exact Q13|]; split; [exact Q14 | exact Q15]).
(* ---- the memory facts both arms need, at any later memory m' the carry covers ---- *)
assert (FAOUT : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  aout_at B RG ly S2 W m' c O mx no cap out) by
 (intros m' md' CK CG HARm;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (WIM : forall x, in_img SEGS x -> writable_at SEGS (arm W mem) x -> writable_at SEGS (arm W m') x)
    by (intros x Hix Hw; unfold arm in *; exact (writable_kept (w_H W) mem m' x (fun Hpr => KP x Hix Hpr) Hw));
  apply (aout_at_kept B RG ly S W mem ly S2 W m' c O mx no cap out HOUT);
  [ intros r Hr a Ha; unfold aout_fp in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr];
    [ cbn [fst snd] in Ha;
      first
      [ split; [ apply KE; clear -Ha; lia
               | intros Hw; exact (WIM a (proj1 (HERRG a ltac:(clear -Ha; lia))) Hw) ]
      | destruct (AOUTK a ltac:(clear -Ha; lia)) as (Hi1 & Ho1 & He1 & Hl1);
        split; [ exact (KI a Hi1 Ho1 He1 (PSTO a ltac:(clear -Ha; lia)) Hl1) | intros Hw; exact (WIM a Hi1 Hw) ] ] | ]);
    destruct (Z.eq_dec cap 0) as [Hc0 | Hc0];
    [ rewrite (proj2 (Z.eqb_eq cap 0) Hc0) in Hr; destruct Hr
    | rewrite (proj2 (Z.eqb_neq cap 0) Hc0) in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha;
      pose proof HOUT as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HAOB);
      assert (Hrs : req_size cap = cap)
        by (unfold req_size; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity);
      destruct HAOB as [(Hc' & _) | (_ & _ & HoIn & _)]; [clear -Hc' Hc0; lia|];
      split;
      [ replace a with (out + (a - out)) by (clear -Ha; lia);
        apply (KH out cap (a - out)); [exact HoIn | rewrite Hrs; clear -Ha; lia]
      | intros _; apply (apresent_writable SEGS);
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ out cap HARm ltac:(rewrite Eab; exact HoIn))
          as (_ & _ & _ & _ & Hpp & _);
        exact (proj1 (Hpp a ltac:(rewrite Hrs; clear -Ha; lia))) ] ]
  | intros b Hb; rewrite Eab; eapply Permutation_in; [apply Permutation_sym; exact HPERM|];
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb ]).

assert (FREST : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  alock_at RG W m' true
  /\ rom_view SEGS W m'
  /\ garr8 SEGS (arm W m') (VAL A_lit_end5) (bzs END5)
  /\ val_mem SEGS (arm W m') (rg_nsrc RG) 4 (Z.of_nat (length es))
  /\ (exists lst, val_mem SEGS (arm W m') GL 4 lst)
  /\ awr W m' GL 4
  /\ apres_kept B W mem W m'
  /\ rf_done ly S2 W m' T) by
 (intros m' md' CK CG HARm;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (WIM : forall x, in_img SEGS x -> writable_at SEGS (arm W mem) x -> writable_at SEGS (arm W m') x)
    by (intros x Hix Hw; unfold arm in *; exact (writable_kept (w_H W) mem m' x (fun Hpr => KP x Hix Hpr) Hw));
  assert (KCELL : forall a, (rg_nsrc RG <= a < rg_nsrc RG + 4) \/ (rg_src RG <= a < rg_src RG + 8)
     \/ (rg_capsrc RG <= a < rg_capsrc RG + 4) \/ (GL <= a < GL + 4) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
    by (intros a Ha; destruct (CELLOK a Ha) as (Hi1 & Ho1 & He1 & Hl1); exact (KI a Hi1 Ho1 He1 (CELLPST a Ha) Hl1));
  assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 4 \/ rg_lock RG + 8 <= a < rg_lock RG + 12 ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a)
    by (intros a Ha; destruct (HPLAIN a (ILK a ltac:(clear -Ha; lia))) as (Hi1 & Ho1 & He1);
        exact (KI a Hi1 Ho1 He1 (PSTC a (ILK a ltac:(clear -Ha; lia))) ltac:(clear -Ha; lia)));
  split;
  [ split;
    [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_lock RG) 4 0);
      [intros k Hk; cbn in Hk; apply KLK; clear -Hk; lia | exact LK0]
    | split;
      [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 m' (rg_lock RG + 4) 4 16);
        [intros k Hk; cbn in Hk; apply CK;
         [clear -Hk HLKb; lia | clear -Hk HLKb Hceil Hslo WS C1; lia] | exact HLK3]
      | split;
        [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_lock RG + 8) 4 0);
          [intros k Hk; cbn in Hk; apply KLK; clear -Hk; lia | exact LK8]
        | intros i Hi; apply WIM;
          [exact (proj1 (HPLAIN (rg_lock RG + i) (ILK (rg_lock RG + i) ltac:(clear -Hi; lia))))
          | exact (LKW i Hi)] ] ] ]
  | split;
    [ exact KR
    | split;
      [ apply (garr8_frame SEGS (arm W mem) (arm W m') (VAL A_lit_end5) (bzs END5) HEND5);
        intros x Hx; unfold bzs in Hx; rewrite length_map in Hx;
        unfold arm; apply (mbyte_of_aview SEGS); rewrite (KR x (HE5R x Hx)); symmetry;
        exact (HROM x (HE5R x Hx))
      | split;
        [ apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_nsrc RG) 4 (Z.of_nat (length es)));
          [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact (proj1 NS0)]
        | split;
          [ destruct HGLv as (lst & Hlst); exists lst;
            apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' GL 4 lst);
            [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact Hlst]
          | split;
            [ intros i Hi; apply WIM;
              [exact (proj1 (CELLOK (GL + i) ltac:(clear -Hi; lia))) | exact (HGLw i Hi)]
            | split;
              [ intros a Hi1 Ho1 He1 Hpr; exact (KP a Hi1 Hpr)
              | split;
                [ intros i Hi; apply WIM;
                  [exact (proj1 (CELLOK (rg_nsrc RG + i) ltac:(clear -Hi; lia)))
                  | exact (proj2 NS0 i Hi)]
                | destruct HREL as [(HT0 & Hes0 & (VS0 & WS0 & _ & _ & VC0 & WC0)) | HRA];
                  [ left; split; [exact HT0|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_src RG) 8 0);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VS0]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_src RG + i) ltac:(clear -Hi; lia))) | exact (WS0 i Hi)]|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_capsrc RG) 4 0);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VC0]|];
                    intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_capsrc RG + i) ltac:(clear -Hi; lia))) | exact (WC0 i Hi)]
                  | pose proof HRA as (VST & WST & _ & _ & VCT & WCT & _ & HTin & _);
                    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & HT4096 & _);
                    right; split; [clear -HT4096; lia|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_src RG) 8 T);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VST]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_src RG + i) ltac:(clear -Hi; lia))) | exact (WST i Hi)]|];
                    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem m' (rg_capsrc RG) 4 16);
                      [intros k Hk; cbn in Hk; apply KCELL; clear -Hk; lia | exact VCT]|];
                    split; [intros i Hi; apply WIM;
                      [exact (proj1 (CELLOK (rg_capsrc RG + i) ltac:(clear -Hi; lia))) | exact (WCT i Hi)]|];
                    rewrite Eab; exact HTin ] ] ] ] ] ] ] ] ]).
assert (FENT : forall (m' : word -> option byte) (md' : Model),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem3 x) ->
  mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) m') ->
  ARx ly S2 Hp W m' md' ->
  forall j, (j < length es)%nat ->
    garr8 SEGS (arm W m') (T + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es rf_e0)))
    /\ awr W m' (T + AENT * Z.of_nat j) AENT
    /\ aheld_ok B ly S2 W m' (nth j es rf_e0)
    /\ ((re_cap (nth j es rf_e0) = 0 /\ re_buf (nth j es rf_e0) = 0) \/
        (0 < re_cap (nth j es rf_e0) /\
         In (re_buf (nth j es rf_e0), re_cap (nth j es rf_e0)) (ablocks B ly S2)))) by
 (intros m' md' CK CG HARm j Hj;
  destruct (CARRY m' md' CK CG HARm) as (KI & KE & KH & KP & KR);
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
      abyte_kept W mem W m' a)
    by (intros p n a Hin Hx; split;
        [ replace a with (p + (a - p)) by (clear -Hx; lia);
          apply (KH p n (a - p)); [exact Hin | clear -Hx; lia]
        | intros _; apply (apresent_writable SEGS);
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARm ltac:(rewrite Eab; exact Hin))
            as (_ & _ & _ & _ & Hpp & _);
          exact (proj1 (Hpp a Hx)) ]);
  destruct HREL as [(HT0 & Hes0 & _) | HRA]; [rewrite Hes0 in Hj; cbn [length] in Hj; clear -Hj; lia|];
  pose proof HRA as (_ & _ & _ & _ & _ & _ & Hle16 & HTin & Htabx & Hall & _);
  destruct Htabx as (tail & Htl & Htot & Hg);
  assert (Hlens : forall x, In x es -> length (entry_bytes x) = 56%nat)
    by (intros x Hx; destruct (proj1 (Forall_forall _ _) Hall x Hx) as (_ & _ & Hp1 & Hp2 & _);
        exact (RFE_EB x Hp1 Hp2));
  pose proof (proj1 (Forall_forall _ _) Hall (nth j es rf_e0) (nth_In es rf_e0 Hj)) as HEOK;
  pose proof (Hlens (nth j es rf_e0) (nth_In es rf_e0 Hj)) as HLe;
  destruct (RFE_SPLIT es Hlens j Hj) as (l1 & l2 & Heq & Hl1);
  rewrite Heq in Hg; rewrite <- !app_assoc in Hg; unfold bzs in Hg; rewrite !map_app in Hg;
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg; destruct Hg as (_ & Hg);
  rewrite length_map, Hl1 in Hg;
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg; destruct Hg as (Hg & _);
  rewrite Nat2Z.inj_mul in Hg; change (Z.of_nat 56) with 56 in Hg;
  assert (HTB : forall x, T <= x < T + ATABLE -> abyte_kept W mem W m' x)
    by (intros x Hx; apply (KBLK T ATABLE x HTin);
        change (req_size ATABLE) with 896; unfold ATABLE in Hx; clear -Hx; lia);
  split;
  [ unfold AENT, bzs; apply (garr8_frame SEGS (arm W mem) (arm W m') _ _ Hg);
    intros x Hx; rewrite length_map, HLe in Hx; unfold arm;
    apply (mbyte_of_aview SEGS); exact (proj1 (HTB x ltac:(clear -Hx Hj Hle16; unfold ATABLE; lia)))
  | split;
  [ intros i Hi; apply (proj2 (HTB (T + AENT * Z.of_nat j + i)
      ltac:(clear -Hi Hj Hle16; unfold ATABLE, AENT in *; lia)));
    apply (apresent_writable SEGS);
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & _ & _ & _ & Hpp & _);
    exact (proj1 (Hpp (T + AENT * Z.of_nat j + i)
      ltac:(clear -Hi Hj Hle16; change (req_size ATABLE) with 896; unfold AENT in *; lia)))
  | split;
  [ apply RFE_HELD; apply (aentry_ok_kept B ly S W mem ly S2 W m' (nth j es rf_e0) HEOK);
    [ intros r Hr a Ha; unfold aentry_fp in Hr;
      destruct HEOK as (_ & _ & _ & _ & _ & _ & HU & _ & _ & HBUF & _ & HHP & _ & _ & HKEYS);
      destruct (in_app_or _ _ _ Hr) as [Hr1 | Hr2];
      [ destruct (Z.eq_dec (re_cap (nth j es rf_e0)) 0) as [Hc0 | Hc0];
        [ rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hr1; destruct Hr1
        | rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hr1; destruct Hr1 as [<- | []];
          unfold gfp in Ha; cbn [fst snd] in Ha;
          destruct HBUF as [(Hc' & _) | (_ & Hbin & Hjk & _)]; [clear -Hc' Hc0; lia|];
          unfold bzs in Ha; rewrite length_map, length_app in Ha;
          apply (KBLK _ _ a Hbin);
          clear -Ha HU Hjk Hc0; unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); lia ]
      | destruct Hr2 as [<- | Hr3];
        [ unfold gfp in Ha; cbn [fst snd] in Ha;
          destruct HHP as [(Hz1 & Hks1) | (Hnz1 & Hbin & Hkh1 & Hkh2 & _)];
          [ rewrite Hks1 in Ha; cbn [key_ptrs map concat bzs length] in Ha; clear -Ha; lia
          | unfold bzs in Ha; rewrite length_map, RFE_KP in Ha;
            apply (KBLK _ _ a Hbin); unfold re_nheld in Hkh1;
            clear -Ha Hkh1 Hkh2; unfold req_size;
            destruct (Z.eqb_spec (re_kh (nth j es rf_e0)) 0); lia ]
        | apply in_map_iff in Hr3; destruct Hr3 as (k & <- & Hk);
          destruct (proj1 (Forall_forall _ _) HKEYS k Hk) as (Hkin & _ & _);
          unfold gfp in Ha; cbn [fst snd] in Ha;
          unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha;
          apply (KBLK _ _ a Hkin);
          clear -Ha; unfold req_size;
          destruct (Z.eqb_spec (Z.of_nat (length (key_text k)) + 1) 0); lia ] ]
    | intros b Hb; rewrite Eab;
      destruct HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _ & HHP & _ & _ & HKEYS);
      unfold aentry_blks in Hb;
      destruct (in_app_or _ _ _ Hb) as [Hb1 | Hb2];
      [ destruct (Z.eq_dec (re_cap (nth j es rf_e0)) 0) as [Hc0 | Hc0];
        [ rewrite (proj2 (Z.eqb_eq _ 0) Hc0) in Hb1; destruct Hb1
        | rewrite (proj2 (Z.eqb_neq _ 0) Hc0) in Hb1; destruct Hb1 as [<- | []];
          destruct HBUF as [(Hc' & _) | (_ & Hbin & _)]; [clear -Hc' Hc0; lia | exact Hbin] ]
      | destruct (in_app_or _ _ _ Hb2) as [Hb3 | Hb4];
        [ destruct (Z.eq_dec (re_hp (nth j es rf_e0)) 0) as [Hz0 | Hz0];
          [ rewrite (proj2 (Z.eqb_eq _ 0) Hz0) in Hb3; destruct Hb3
          | rewrite (proj2 (Z.eqb_neq _ 0) Hz0) in Hb3; destruct Hb3 as [<- | []];
            destruct HHP as [(Hz1 & _) | (_ & Hbin & _)]; [clear -Hz1 Hz0; lia | exact Hbin] ]
        | apply in_map_iff in Hb4; destruct Hb4 as (k & <- & Hk);
          exact (proj1 (proj1 (Forall_forall _ _) HKEYS k Hk)) ] ] ]
  | destruct HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _);
    destruct HBUF as [(Hc0 & Hb0 & _) | (Hcp & Hbin & _)];
    [ left; split; [exact Hc0 | exact Hb0]
    | right; split; [exact Hcp | rewrite Eab; exact Hbin] ] ]]]).
(* the run to the blez: the auipc of g_nsrc's hi slot and the load of g_nsrc *)
assert (SHOKd : sh_ok SEGS Bx rf_SH0 Ed (mrestrict (w_H W) mem3)) by (unfold sh_ok, rf_SH0; constructor).
paj_run_tok_xR RUNR HS HJX3 SHOKd Bspan.
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
(* the value the blez compares: g_nsrc is |es|, loaded as a signed 4-byte cell *)
assert (HNU : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 514 0))) = Z.of_nat (length es)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 514 0))) with (U Ed (SOff 514 0)).
  rewrite (U_atom Ed 514 (Z.of_nat (length es)) E514 ltac:(lia)). apply sx32_small. lia. }
assert (HNS : bv_signed (sv_denot Ed (SExt true 32 (SOff 514 0))) = Z.of_nat (length es))
by (rewrite bv_signed_small by (rewrite HNU; lia); exact HNU).
assert (HZ0 : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity.
(* the blez: g_nsrc is |es| and never negative, so it is taken exactly when the relay has no source *)
psrr_branch_tok RUNR BRR HS SHOKd Bspan.
-
(* ---- no source: the table is empty and the loop is skipped; run to the tail at 0x1a8 ---- *)
cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
apply Bool.negb_true_iff, Z.ltb_ge in Hc.
assert (Hnil : es = []) by (destruct es as [|e es']; [reflexivity | cbn [length] in Hc; lia]).
paj_run_to_tok_xR RUNTOR HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x1a8).
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia ]
  | ]).
  destruct Hin. }
pmkst HS.
(* ---- the cut state X at 0x1a8: the run from the blez wrote only the frame, so the transport block carries ---- *)
assert (CK1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms2) x = aview SEGS (w_H W) mem3 x).
{ intros x Hx Hn.
  rewrite (aview_kept_out Ed _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)).
  exact (aview_kept_out Ed _ (w_H W) mem3 (ms_mem ms1) HFr1 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)). }
assert (CG1 : mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms2)))
  by (intros y Hy; exact (HG6 y (HG5 y Hy))).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARm.
pose proof (FAOUT (ms_mem ms2) _ CK1 CG1 HARm) as AOUTm.
destruct (FREST (ms_mem ms2) _ CK1 CG1 HARm) as (LKm & ROMm & E5m & NSm & GLvm & GLwm & PRESm & DONEm).
(* the registers the tail inherits *)
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (U512d : bv_unsigned (ew Ed 512) = FL) by (rewrite OLDd, HIc by lia; exact U512).
assert (U289d : bv_unsigned (ew Ed 289) = VAL (A_HI 9))
  by exact (HEId (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (EWD : forall (k : nat) (r : bv 5), (k < 34)%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot Ed (SOff k 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros k r Hk Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite OLDd, OLDc, OLDb, OLDa by lia; rewrite (EE k r Hr); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_region_nth Ed _ _ 2%nat _ HS eq_refl) as HRf.
pose proof (st_ok_pi_region_nth Ed _ _ 1%nat _ HS eq_refl) as HRF38.
cbn [ms_mem restrict] in HRf, HRF38.
assert (RSAV : rf_saved W (ms_mem ms2) (spZ regs) regs) by
 (intros i Hi;
  destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 0) with (spZ regs + (-88)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-88) 8%N (SOff 25 0)
         (bv_unsigned (getr regs 25%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 25%nat 25%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 25%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 1) with (spZ regs + (-80)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-80) 8%N (SOff 24 0)
         (bv_unsigned (getr regs 24%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 24%nat 24%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 24%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 2) with (spZ regs + (-72)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-72) 8%N (SOff 23 0)
         (bv_unsigned (getr regs 23%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 23%nat 23%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 23%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 3) with (spZ regs + (-64)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-64) 8%N (SOff 22 0)
         (bv_unsigned (getr regs 22%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 22%nat 22%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 22%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 4) with (spZ regs + (-56)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-56) 8%N (SOff 21 0)
         (bv_unsigned (getr regs 21%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 21%nat 21%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 21%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 5) with (spZ regs + (-48)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-48) 8%N (SOff 20 0)
         (bv_unsigned (getr regs 20%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 20%nat 20%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 20%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 6) with (spZ regs + (-40)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-40) 8%N (SOff 19 0)
         (bv_unsigned (getr regs 19%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 19%nat 19%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 19%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 7) with (spZ regs + (-32)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-32) 8%N (SOff 18 0)
         (bv_unsigned (getr regs 18%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 18%nat 18%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 18%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 8) with (spZ regs + (-24)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-24) 8%N (SOff 9 0)
         (bv_unsigned (getr regs 9%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 9%nat 9%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 9%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 9) with (spZ regs + (-16)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-16) 8%N (SOff 8 0)
         (bv_unsigned (getr regs 8%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 8%nat 8%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 10) with (spZ regs + (-8)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-8) 8%N (SOff 1 0)
         (bv_unsigned (getr regs 1%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 1%nat 1%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | exfalso; clear -Hi; lia ] ] ] ] ] ] ] ] ] ] ]).
(* ---- RFX_xR ---- *)
apply (TAIL regs ly S Hp W mem md T es c O mx no cap out rest fpos ly S2 Hp W (ms_regs ms2) (ms_mem ms2) _).
unfold RFX_xR. exists 0, out.
change (frame_addr ly 0 fpos) with F. change (flag_addr ly 0 fpos) with FL.
split; [exact HJX3|].
split.
{ split; [exists ch; exact HPRE|]. split; [exact HPERM|].
  split; [exact HG1|]. split; [exact HG2 | exact HG3]. }
split.
{ unfold rf_kept.
  split; [unfold spZ at 1; rewrite X2, U2d; rewrite unsigned_lit_small by (unfold spZ in *; lia); lia|].
  split; [rewrite X3; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 3%nat 3%bv eq_refl)|].
  split; [rewrite X4; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 4%nat 4%bv eq_refl)|].
  split; [rewrite X26; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 26%nat 26%bv eq_refl)|].
  split; [rewrite X27; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 27%nat 27%bv eq_refl)|].
  split; [rewrite X8, <- U2d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X18, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X19; rewrite OLDd, OLDc by lia; exact E33b|].
  split; [rewrite X20, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X21, <- U513d; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite X22, <- U289d; symmetry; apply Z_to_bv_bv_unsigned. }
split; [clear -HF4096; lia|].
split; [exact RSAV|].
split; [exact (field_of_region Ed _ 38%nat F _ 0 64 0 0 56 8%N (SOff 512 0) FL HRF38 U38d
    ltac:(cbn [In]; tauto)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U512d; reflexivity)
    ltac:(clear -HFL4096 HFLc C1; cbn; lia) ltac:(cbn; lia))|].
split; [exact NSm|].
split; [exact DONEm|].
split; [exact LKm|].
split; [rewrite Hnil; cbn [rf_run gse_c gse_O gse_no gse_cap]; exact AOUTm|].
split; [rewrite Hnil; cbn [rf_run gse_cap]; rewrite Eab;
  rewrite Hnil in HPERM; unfold rf_eblks in HPERM; cbn [map concat app] in HPERM; exact HPERM|].
split; [exact GLvm|].
split; [exact GLwm|].
split; [exact PRESm|].
split; [rewrite Hnil; cbn [rf_cost]; destruct HFS as (fS2 & EfS2); rewrite EfS2; exact (MO_FR S fS2)|].
(* the room round: no source, so nothing was charged: the seat's room is rf_post's kr *)
rewrite Hnil in HRM2. exact HRM2.
-
(* ---- sources: s7 = 0, s8 = 16, s9 = the hi slot of g_src; run to the loop head at 0x168 ---- *)
cbn [branch_taken] in Hc. rewrite bv_lts_signed, HNS, HZ0 in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok_xR RUNTOR HS HJX3 SHOKd Bspan (AF_fr_relay_finish + 0x168).
{ apply awr_ok_x_of0.
  intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U2d, ?U38d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
    first [ (exfalso; clear - Hr; lia)
    | left; unfold RF_STK, RF_FRAME, GSE_STK, GSE_FRAME, GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK; lia ]
  | ]).
  destruct Hin. }
pmkst HS.
(* ---- the cut state L at 0x168, round 0: the run from the blez wrote only the frame, so the transport block carries ---- *)
assert (CK2 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 96 <= x < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms2) x = aview SEGS (w_H W) mem3 x).
{ intros x Hx Hn.
  rewrite (aview_kept_out Ed _ (w_H W) (ms_mem ms1) (ms_mem ms2) HFr2 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)).
  exact (aview_kept_out Ed _ (w_H W) mem3 (ms_mem ms1) HFr1 x Hx
    ltac:(intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2d, ?U38d, ?U513d, ?U241d, ?U242d, ?U244d, ?U273d, ?U32d, ?U248d in Hr;
        clear -Hr Hn; lia | ]);
      destruct Hin)). }
assert (CG2 : mem_grows (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms2)))
  by (intros y Hy; exact (HG6 y (HG5 y Hy))).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX3) as HARm.
pose proof (FAOUT (ms_mem ms2) _ CK2 CG2 HARm) as AOUTm.
destruct (FREST (ms_mem ms2) _ CK2 CG2 HARm) as (LKm & ROMm & E5m & NSm & GLvm & GLwm & PRESm & DONEm).
(* the registers the loop inherits, and its counters s7 = 0, s8 = 16, s9 = the hi slot of g_src *)
prreg HS (23%bv : bv 5) X23. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (U290d : bv_unsigned (ew Ed 290) = VAL (A_HI 10))
  by exact (HEId (A_HI 10) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (U512d : bv_unsigned (ew Ed 512) = FL) by (rewrite OLDd, HIc by lia; exact U512).
assert (U289d : bv_unsigned (ew Ed 289) = VAL (A_HI 9))
  by exact (HEId (A_HI 9) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (EWD : forall (k : nat) (r : bv 5), (k < 34)%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot Ed (SOff k 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros k r Hk Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      rewrite OLDd, OLDc, OLDb, OLDa by lia; rewrite (EE k r Hr); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (st_ok_pi_region_nth Ed _ _ 2%nat _ HS eq_refl) as HRf.
pose proof (st_ok_pi_region_nth Ed _ _ 1%nat _ HS eq_refl) as HRF38.
cbn [ms_mem restrict] in HRf, HRF38.
assert (RSAV : rf_saved W (ms_mem ms2) (spZ regs) regs) by
 (intros i Hi;
  destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 0) with (spZ regs + (-88)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-88) 8%N (SOff 25 0)
         (bv_unsigned (getr regs 25%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 25%nat 25%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 25%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 1) with (spZ regs + (-80)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-80) 8%N (SOff 24 0)
         (bv_unsigned (getr regs 24%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 24%nat 24%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 24%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 2) with (spZ regs + (-72)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-72) 8%N (SOff 23 0)
         (bv_unsigned (getr regs 23%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 23%nat 23%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 23%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 3) with (spZ regs + (-64)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-64) 8%N (SOff 22 0)
         (bv_unsigned (getr regs 22%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 22%nat 22%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 22%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 4) with (spZ regs + (-56)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-56) 8%N (SOff 21 0)
         (bv_unsigned (getr regs 21%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 21%nat 21%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 21%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 5) with (spZ regs + (-48)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-48) 8%N (SOff 20 0)
         (bv_unsigned (getr regs 20%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 20%nat 20%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 20%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 6) with (spZ regs + (-40)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-40) 8%N (SOff 19 0)
         (bv_unsigned (getr regs 19%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 19%nat 19%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 19%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 7) with (spZ regs + (-32)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-32) 8%N (SOff 18 0)
         (bv_unsigned (getr regs 18%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 18%nat 18%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 18%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 8) with (spZ regs + (-24)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-24) 8%N (SOff 9 0)
         (bv_unsigned (getr regs 9%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 9%nat 9%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 9%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 9) with (spZ regs + (-16)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-16) 8%N (SOff 8 0)
         (bv_unsigned (getr regs 8%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 8%nat 8%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | destruct i as [|i];
     [ unfold RF_SAVED; cbn [nth];
       replace (spZ regs - 88 + 8 * Z.of_nat 10) with (spZ regs + (-8)) by lia;
       exact (field_of_region Ed _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 (-8) 8%N (SOff 1 0)
         (bv_unsigned (getr regs 1%bv)) HRf U2d ltac:(cbn [In]; tauto)
         (EWD 1%nat 1%bv ltac:(lia) eq_refl)
         ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as Hr64;
               change (bv_modulus 64) with (2 ^ 64) in Hr64; cbn; lia)
         ltac:(cbn; lia))
     | exfalso; clear -Hi; lia ] ] ] ] ] ] ] ] ] ] ]).
(* ---- RFI_xR at round 0 ---- *)
pose proof (FENT (ms_mem ms2) _ CK2 CG2 HARm) as ENTm.
destruct DONEm as (NSWm & [(HT0 & _) | (HTn & VSm & WSm & VCm & WCm & HTinm)]).
{ exfalso. destruct HREL as [(_ & Hes0 & _) | HRA]; [rewrite Hes0 in Hc; cbn [length Z.of_nat] in Hc; lia|].
  pose proof HRA as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR HTin) as (_ & HT4096 & _). clear -HT0 HT4096; lia. }
apply (LOOP (length es) regs ly S Hp W mem md T es c O mx no cap out rest fpos 0%nat ly S2 Hp W (ms_regs ms2) (ms_mem ms2) _ kr
  ltac:(lia) (conj HTOPR (ex_intro _ ch (conj HPRE HCTX))) HCNTe).
unfold RFI_xR. exists 0, out, 0.
change (frame_addr ly 0 fpos) with F. change (flag_addr ly 0 fpos) with FL.
split; [exact HJX3|].
split.
{ split; [exists ch; exact HPRE|]. split; [exact HPERM|].
  split; [exact HG1|]. split; [exact HG2 | exact HG3]. }
split.
{ unfold rf_kept.
  split; [unfold spZ at 1; rewrite X2, U2d; rewrite unsigned_lit_small by (unfold spZ in *; lia); lia|].
  split; [rewrite X3; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 3%nat 3%bv eq_refl)|].
  split; [rewrite X4; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 4%nat 4%bv eq_refl)|].
  split; [rewrite X26; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 26%nat 26%bv eq_refl)|].
  split; [rewrite X27; rewrite OLDd, OLDc, OLDb, OLDa by lia; exact (EE 27%nat 27%bv eq_refl)|].
  split; [rewrite X8, <- U2d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X18, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X19; rewrite OLDd, OLDc by lia; exact E33b|].
  split; [rewrite X20, <- U38d; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite X21, <- U513d; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite X22, <- U289d; symmetry; apply Z_to_bv_bv_unsigned. }
split; [clear -HF4096; lia|].
split; [rewrite X23; reflexivity|].
split; [rewrite X24; reflexivity|].
split; [rewrite X25, <- U290d; symmetry; apply Z_to_bv_bv_unsigned|].
split; [exact RSAV|].
split.
{ exact (field_of_region Ed _ 38%nat F _ 0 64 0 0 56 8%N (SOff 512 0) FL HRF38 U38d
    ltac:(cbn [In]; tauto)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U512d; reflexivity)
    ltac:(clear -HFL4096 HFLc C1; cbn; lia) ltac:(cbn; lia)). }
split; [clear -Hc; lia|].
split; [exact NSB|].
split; [exact HTn|].
split; [exact NSm|].
split; [exact NSWm|].
split; [exact VSm|].
split; [exact WSm|].
split; [exact VCm|].
split; [exact WCm|].
split; [exact HTinm|].
split; [intros j Hj; exact (ENTm j (proj2 Hj))|].
split; [exact LKm|].
split; [cbn [firstn rf_run gse_c gse_O gse_no gse_cap]; exact AOUTm|].
split; [cbn [firstn skipn rf_run gse_cap]; rewrite Eab; exact HPERM|].
split; [exact GLvm|].
split; [exact GLwm|].
split; [exact E5m|].
split; [exact ROMm|].
split; [exact PRESm|].
split; [cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]; rewrite Hbb2; exact HROOM|].
split; [destruct HFS as (fS2 & EfS2); rewrite EfS2; exact (MO_FR S fS2)|].
split; [rewrite Z.add_0_l; apply Z.le_refl|].
split; [exact HMOK|].
(* the room round: round 0 is owed the whole charge, the seat kept it *)
cbn [firstn skipn rf_run gse_c gse_O gse_no gse_cap]. exact HRM2.
Qed.
(* :3772 pb_relay_finish_h_x at R *)
Theorem pb_relay_finish_h_xR : rf_spec_xR B PST ARx R MT RP MMAX G RG GTU GL CTX A_relay_finishP.
Proof using AFREEN_R AFREE_R ALOCK ASM0 AUNLOCK BLKN GSE_R HBcell HBgot HE5R HH11 HH12 HH9 HIG HIGO HP0 HPLAIN HPLAINO HROMG HROMO HSEPG HSEPO HV3 HV6 HV7 HV8 HWSEG HWSEGE IMGC MLAW MO_FR OWNLOW PSTC PSTO PSTR RGAL RO_ARx RUN0R RUNCR RUNFR RUNR RUNTOR R_refl R_trans SMALLOC TLF WLE_R.
exact (rf_entry_seg_xR rf_tail_xR (rf_loop_xR rf_tail_xR)).
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_relay_finish_h's statement is the AR
   walk's, byte-identical, now a corollary of pb_relay_finish_h_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS: the
   instance builds it once, W_laws_x.AR_laws_x_ARi0_of.  The bridges: W_contract_x.rf_spec_x_AR0 (conclusion),
   gse_spec_x_of_AR0 (GSE); W_sites_x.alock_realizes_x_of_AR0 / aunlock_realizes_x_of_AR0; the free rules through
   W_journal_x.afree_cf_rule_c_x_of_AR0 / afree_null_cf_rule_c_x_of_AR0; HP0 is ARi0_hp0; IMGC / BLKN are
   W_kit_x.AR_imgc / AR_blkn; the frame twins' hypotheses come from the AR Section's ML / SMP / ASM0 / ASF / FFL
   (W_frame_x.v Section br: WFL_AR, SFREE_AR, SMALLOC_AR at WFx := Wf (as_universe B); OWNLOW from
   YG0s.AR_owned_low_law_ok); PSTR / PSTC / PSTO hold at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
Variable CTX : list (list Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MLAW : ameter_laws MT.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM0 : astack_malloc_pres SEGS B 0.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX.
Hypothesis AFREE0 : afree_null_cf_rule_c SEGS B MT CTX.
Hypothesis GSE : gse_spec B MT MMAX RG (BASE + AF_fr_gestures_end).
(* the placement hypotheses, Section c's (its notes say which goal demands each) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HV3 : VAL (A_OBJ 3) = GTU.
Hypothesis HV6 : VAL (A_OBJ 6) = rg_lock RG.
Hypothesis HV7 : VAL (A_OBJ 7) = rg_nsrc RG.
Hypothesis HV8 : VAL (A_OBJ 8) = rg_src RG.
Hypothesis HH9 : VAL (A_HI 9) + 868 = rg_nsrc RG.
Hypothesis HH11 : VAL (A_HI 11) + (-1208) = rg_client RG.
Hypothesis HH12 : VAL (A_HI 12) + (-1252) = GL.
Hypothesis HIG : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fb000)
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 1), 8); (VAL (A_OBJ 32), 8); (as_uar_cell B, 4);
 (GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (as_errno B, 4)].
Hypothesis HPLAIN : forall a, inG (rf_cells RG GTU GL) a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HWSEG : forall a, inG (rf_cells RG GTU GL) a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis RGAL : rg_lock RG mod 4 = 0.
Hypothesis HIGO : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fb000)
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
(* THE TOP: the entry segment, handing off to the tail and to the loop at round 0, and the loop handing off to
   the tail on its exit arm. *)
Theorem pb_relay_finish_h : rf_spec B MT MMAX G RG GTU GL CTX A_relay_finishP.
Proof.
apply rf_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (OWNLOW : ARx_owned_low_law SEGS B (ARi0 SEGS B))
  by (intros ly S Hp W mem md a H Ho; exact (YG0s.AR_owned_low_law_ok SEGS B ly S W mem md a (proj1 H) Ho)).
assert (WFL : ARx_wf_law SEGS (ARi0 SEGS B) (Wf (as_universe B)))
  by (intros ly S Hp W mem md H; exact (WFL_AR SEGS B ly S Hp W mem md (proj1 H))).
pose proof (SFREE_AR B ML) as SFREE.
pose proof (SMALLOC_AR B ML SMP) as SMALLOC.
assert (ASM0X : astack_malloc_pres_x SEGS B (ARi0 SEGS B) 0).
{ intros ly S Hp W regs mem md pos S' ((HAR & HP) & Hr) Hcnt Hpath.
  eapply SRr_mono; [exact (ASM0 ly S W regs mem md pos S' (conj HAR Hr) Hcnt Hpath)|].
  cbv beta. intros W' c' _ (EW & regs' & mem' & md' & Hc & HAR' & Hrest).
  split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HP] | exact Hrest]. }
assert (ASFX : astack_free_law_x SEGS B (ARi0 SEGS B)).
{ intros ly S Hp W mem md mem' md' cid pos (HAR & HP) Hin. intros. split; [eapply ASF; eassumption | exact HP]. }
assert (FFLX : frame_flag_lawP_x SEGS B (ARi0 SEGS B))
  by (intros ly S Hp W mem md cid pos H Hin; exact (FFL ly S W mem md cid pos (proj1 H) Hin)).
pose proof (alock_realizes_x_of_AR0 B _ ALOCK) as ALOCKX.
pose proof (aunlock_realizes_x_of_AR0 B _ AUNLOCK) as AUNLOCKX.
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE) as AFREEX.
pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE0) as AFREE0X.
pose proof (gse_spec_x_of_AR0 B MT MMAX RG _ GSE) as GSEX.
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
assert (PSTC : forall a, inG (rf_cells RG GTU GL) a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
assert (PSTO : forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8)
   \/ (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8)
   \/ (rg_client RG <= a < rg_client RG + 4)
   \/ (rg_client_broken RG <= a < rg_client_broken RG + 1)
   \/ (rg_send_dead RG <= a < rg_send_dead RG + 1)
   \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) -> ~ Exists (in_zr a) (@nil (Z * Z)))
  by (intros a _ H; inversion H).
eapply (pb_relay_finish_h_x B [] (ARi0 SEGS B) MT RP_AR MMAX G RG GTU GL CTX) with (WFx := Wf (as_universe B)); eassumption.
Qed.
End cAR.
End b.
End a.
Print Assumptions pb_relay_finish_h.
About pb_relay_finish_h.
