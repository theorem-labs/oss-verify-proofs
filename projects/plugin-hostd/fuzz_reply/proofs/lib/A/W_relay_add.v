(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of plugin-hostd's relay_add, in the form of the cgif fake-frame walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACk1.v (prologue, stack_malloc, exit) and lib/A/AC8h.v (call sites). *)
(* Modified by Theorem Labs, 2026-10-29 (a Theorem Labs lane, a Theorem Labs lane row C1): the walk is now pb_relay_add_x over any
   allocator relation ARx with its laws (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record)), stated as W_contract_x's
   ra_spec_x; pb_relay_add keeps its statement and is its corollary at ARi0, PST = [] (Section cAR). *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, a Theorem Labs lane room round F3): pb_relay_add_x takes the room record RP
   (ra_spec_x's rp_RM budget and cnt_ok_pk peak), the laws RPF / RMM, and threads them to the realloc; the fake-frame
   seat is W_frame_x.v's aj_stack_malloc_pres_at_raw_x, which states S2 = set_fs f Sc (commit cb71685bcb2; the local
   twin this file carried until then is removed). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YO0c YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_journal W_sites W_rebase W_relay_add_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x YC80x YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x.
(* route R: SRrG / wle' (YA0nH), the G runs (YC80xR), relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YC80xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_srlf_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Two cells of a zseps list (W_frame.v) are apart, picked by index: never tauto / lia over the whole list, whose
   disjunctions make both exponential.  (W_relay_finish.v's text, kept local to this file so that neither walk
   forces the other's rebuild.) *)
Lemma ra_zseps_from_In : forall b l c, zseps_from b l -> In c l -> fst b + snd b <= fst c \/ fst c + snd c <= fst b.
Proof.
intros b l c. induction l as [|x l IH]; cbn; [tauto|]. intros [Hx Hl] [<- | Hc]; [exact Hx | exact (IH Hl Hc)].
Qed.
Lemma ra_zseps_nth : forall l i j a b, zseps l -> (i < j)%nat -> nth_error l i = Some a -> nth_error l j = Some b ->
fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Proof.
induction l as [|x l IH]; intros i j a b Hs Hij Ha Hb; [destruct i; discriminate|].
destruct Hs as [Hx Hl]. destruct i as [|i].
- cbn in Ha. injection Ha as <-. destruct j as [|j]; [lia|]. cbn in Hb.
  exact (ra_zseps_from_In x l b Hx (nth_error_In l j Hb)).
- destruct j as [|j]; [lia|]. cbn in Ha, Hb. exact (IH i j a b Hl ltac:(lia) Ha Hb).
Qed.
Ltac ra_zsep_pick H i j D := pose proof (ra_zseps_nth _ i j _ _ H ltac:(clear; lia) eq_refl eq_refl) as D; cbn [fst snd] in D.
(* a byte of relay_add's globals (image, below 6270976) lies in no write window of the walk's states: HW bundles
   the three bounds (the frame is above alloc_ceiling, the fake frame is outside the image band, its shadow is
   above SB), so each region's goal is a `lia` over two hypotheses. *)
Ltac ra_glob_out HaB HW U2 U38 U513 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2, ?U38, ?U513 in Hr;
  revert Hr; revert HaB HW; clear; intros; lia | ]);
destruct Hin.
(* errno's bytes (image, in the band by HIG) lie in no write window of the fd < 0 path's states.  HW bundles the
   three bounds (the frame is above the image band, the fake frame is off it, the fake frame's shadow is above it);
   the fake frame's flag byte is not an image byte (HFLni) while errno's are (HaI). *)
Ltac ra_errno_out HaB HW HFLni HaI U2 U38 U513 U512 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2, ?U38, ?U513, ?U512 in Hr;
  first [ revert Hr; revert HaB HW; clear; intros; lia
        | lazymatch type of Hr with ?fl + _ <= ?x < _ =>
            exfalso; apply HFLni; replace fl with x by (revert Hr; clear; intros; lia); exact HaI end ] | ]);
destruct Hin.
(* A byte a (HaB : its bounds) lies in no write window of a run's regions: each region's base is rewritten by the
   U-facts Us (a tuple of base equations, tried with `rewrite ?`), then one lia over Hr, HaB and the bundle HW (the
   apartness facts, as one conjunction). *)
Ltac ra_out HaB HW U1 U2 U3 U4 U5 U6 U7 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U1, ?U2, ?U3, ?U4, ?U5, ?U6, ?U7 in Hr;
  revert Hr; revert HaB HW; clear; intros; lia | ]);
destruct Hin.
(* The entry relay_add appends: s4 = g_src + ((nsrc << 6) - (nsrc << 3)), nsrc the sign-extended 32-bit cell, as
   `prreg` leaves it - an alu64 tree over the raw env words.  That tree is not convertible with the sv_denot form
   (measured: `reflexivity` fails), so the value is computed here once, by the alu64 lemmas of Reusable/YO0c.v. *)
Lemma ra_entry_addr : forall (w516 w514 : word) (T n : Z),
w516 = Z_to_bv 64 T -> w514 = Z_to_bv 64 n -> 0 <= T < 2 ^ 63 -> 0 <= n <= 16 ->
alu64 ALU_ADD (alu64 ALU_ADD w516
  (alu64 ALU_SUB (alu64 ALU_SLL (sext 64 (bv_extract 0 32 w514)) (Z_to_bv 64 6))
                 (alu64 ALU_SLL (sext 64 (bv_extract 0 32 w514)) (Z_to_bv 64 3)))) (Z_to_bv 64 0)
= Z_to_bv 64 (T + 56 * n).
Proof.
intros w516 w514 T n -> -> HT Hn. apply bv_eq.
rewrite !alu64_add, alu64_sub, !alu64_sll, !sext64_32_unsigned.
rewrite !bv_extract_unsigned, !Z.shiftr_0_r, !bv_wrap32.
rewrite !unsigned_lit_small by lia.
rewrite (Z.mod_small n (2 ^ 32)) by lia. rewrite (sx32_small n) by lia.
change (6 mod 64) with 6. change (3 mod 64) with 3.
unfold add64, sub64, sll64. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
rewrite (Z.mod_small (n * 64) (2 ^ 64)) by lia. rewrite (Z.mod_small (n * 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small (n * 64 - n * 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small (T + (n * 64 - n * 8)) (2 ^ 64)) by lia.
rewrite Z.add_0_r. rewrite Z.mod_small by lia. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_relay_add : Z := AF_fr_relay_add.
Definition A_relay_addP : Z := BASE + A_relay_add.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): relay_add over any allocator relation ARx
   with its laws, stated as W_contract_x.ra_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS
   (the generic relation); HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table block's shadow is
   W_journal_x's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x); IMGC / BLKN (W_kit_x.v Section g,
   W_frame_x.v Section c: blk_off_imgP_x, frm_off_imgP_x); OWNLOW (W_frame_x.v Section fsp, the fake-frame seat); and in
   place of model_laws / stack_malloc_progressP the model invariant WFx with its law WFL and the two facts W_frame_x.v
   reads off them, SFREE (the flag store) and SMALLOC (the seat).  The frame laws, the runtime entries, the realloc rule
   and the memset intrinsic are their W_frame_x / W_sites_x / W_journal_x twins.  The journal's image clause exempts
   PST, so relay_add's globals are carried from the entry by the runs' frames and the seat's RAW clause (RAK below),
   not by the journal. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (lib/A/W_journal_x.v Record roomp): the allocator's room invariant rp_RM and the live counts *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the model's state invariant (cgif: Wf (as_universe B)) with its law, and the two facts W_frame_x.v's flag store
   (Section a0) and fake-frame seat (Section fsp) read off cgif's model_laws / stack_malloc_progressP *)
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* the law call_effect_journal_x asks that AR_laws_x lacks (cgif's al_owned_low), and W_kit_x.v's IMGC / BLKN *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis ASM0 : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis MLAW : ameter_laws MT.
(* the meter does not charge the fake frame: its seat and its release are set_fs steps (stack_free_state is a set_fs,
   YG01.v), and a set_fs step costs nothing *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the room invariant does not see the fake frame (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.4 NPF over rp_RM; stack_free_state is a set_fs),
   and its budget is monotone (0.4 RMM): the fd < 0 arm makes no realloc although ra_cost charges 2 at T = 0 *)
Hypothesis RPF : forall S f k, rp_RM RP S k -> rp_RM RP (set_fs f S) k.
Hypothesis RMM : forall S k k', (k <= k')%nat -> rp_RM RP S k' -> rp_RM RP S k.
Hypothesis HG : gx_ok SEGS B G.
(* relay_add's globals lie in writable segments: writable in every memory where they are not hidden *)
Hypothesis GW : forall (H : word -> bool) (m : word -> option byte) a,
inG (RA_G RG) a -> H (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict H m) a.
(* runtime entries (R5: RT_pthread_mutex_lock.v, RT_pthread_mutex_unlock.v), the allocator's realloc site rule
   (W_journal_x.v, the caller-context form) and the memset intrinsic, over ARx (W_sites_x.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
(* the allocator rules' caller-context table (W_journal_x.v Section hc), relay_add's spec's CTX; the realloc rule is
   the _c form, which takes the call's context `In (raZ regsT :: spine ch) CTX` *)
Variable CTX : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX (SIGMA WS_realloc).
(* the instance's malloc ceiling admits the table: MMAX = cf_malloc_max = 2^30 - 2^20 at the instance, an instance fact like AREALLOC *)
Hypothesis HMMAX : ATABLE < MMAX.
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
(* placement: the objects relay_add reads by PLdHi and the kept auipc registers it stores through
   (fuzz_reply.asan: g_lock 0x5d8ac0, g_nsrc 0x5d87a0, g_capsrc 0x5d8800, g_src 0x5d87c0, g_wake + 4 0xa1fa4;
   s8 = 0x5d8a60, s10 = 0x5d8a64, s9 = 0x5d8a70); the pinned placement discharges them by vm_compute *)
Hypothesis HV6 : VAL (A_OBJ 6) = rg_lock RG.
Hypothesis HLA : rg_lock RG mod 4 = 0.
Hypothesis HV7 : VAL (A_OBJ 7) = rg_nsrc RG.
Hypothesis HV16 : VAL (A_OBJ 16) = rg_capsrc RG.
Hypothesis HV8 : VAL (A_OBJ 8) = rg_src RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
Hypothesis HH30 : VAL (A_HI 30) - 704 = rg_nsrc RG.
Hypothesis HH31 : VAL (A_HI 31) - 612 = rg_capsrc RG.
Hypothesis HH32 : VAL (A_HI 32) - 688 = rg_src RG.
(* ... and they lie in the image band (W_relay_finish.v's HIG; vm_compute at the pinned placement) *)
Hypothesis HIG : Forall (fun r => 65536 <= fst r /\ fst r + snd r <= 6270976)
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_capsrc RG, 4); (rg_src RG, 8); (rg_wake RG + 4, 4); (as_errno B, 4)].
(* the INSTANCE fact that errno's four bytes (tp - 164, a writable .bss cell) lie outside as_owned_static - decided
   once by vm_compute against the instance's concrete list; with W_frame_x.v's errno_not_aowned_x and
   aj_stack_malloc_pres_at_raw_x it carries errno's view across the fake-frame seat.  (A walk whose G contains
   G_SL gets this from gx_ok instead; relay_add's G need not contain errno.) *)
Hypothesis HEO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (as_errno B + i)) (as_owned_static B).
(* ... and the same two facts for g_wake[1] (0xa1fa4, a writable .data cell relay_add only READS): its bytes are
   image bytes outside as_owned_static, so the fake-frame seat keeps them (aj_stack_malloc_pres_at_raw_x); decided
   by vm_compute against the instance's segments and concrete list *)
Hypothesis HWKI : forall i, 0 <= i < 4 -> in_img SEGS (rg_wake RG + 4 + i).
Hypothesis HWKO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (rg_wake RG + 4 + i)) (as_owned_static B).
(* the cells relay_add reads and writes are pairwise apart (the pinned placement decides it by vm_compute at
   fr_globals / PB_fr, as W_relay_finish.v's HSEPG does) *)
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 1), 8); (VAL (A_OBJ 32), 8); (as_uar_cell B, 4);
 (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_capsrc RG, 4); (rg_src RG, 8); (as_errno B, 4); (rg_wake RG + 4, 4)].
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bx : sv := SOff 33 0.
Definition ra_regions0 : smem :=
[ stack_region RA_FRAME; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
Definition ra_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0x10000 0x5fb000 2); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_ra0 : sstate := mkSS A_relay_add sr_atoms ra_regions0 None ra_facts0.
Definition ra_SH0 : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ra_extra : list word := map (Z_to_bv 64) [as_uar_cell B; SB].
(* the three table globals.  The listing reads each through its object atom (a PLdHi slot: g_nsrc A_OBJ 7 = 248,
   g_capsrc A_OBJ 16 = 257, g_src A_OBJ 8 = 249), written as the numerals vm_compute leaves in a state; the stores
   go through the kept auipc registers (A_HI 30 / 31 / 32), where the region is rebased (W_rebase.v prebase).
   Their values are seated as the atoms 514 (|es|), 515 (the capacity) and 516 (the table), so that no section
   variable is under vm_compute. *)
Definition ra_nsrc_region : YP09.region :=
YP09.mkRegion (Some 248%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 514 0))].
Definition ra_capsrc_region : YP09.region :=
YP09.mkRegion (Some 257%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 515 0))].
Definition ra_src_region : YP09.region :=
YP09.mkRegion (Some 249%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 516 0))].
(* the entry relay_add appends, on atom 517 (its address T + AENT * |es|): extent its 56 bytes, write window the
   first word only (s->fd = fd), so the run's frame clause keeps the memset's zeros in the other 52 *)
Definition ra_ent_region : YP09.region := YP09.mkRegion (Some 517%nat) 0 56 0 4 [].
(* A register's symbolic value may be replaced by any sv of the same denotation (W_kit.v st_ok_pi_pin_reg' with an
   arbitrary sv): used to name s4 by its atom 517, so that the shadow check `(s4 >> 3) + s5` is recognised. *)
Lemma ra_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
(sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
(* A region may be replaced by one of the same extent that is region_ok in the current memory (W_rebase.v's
   st_ok_rebase with an arbitrary replacement): used to give the fake frame back its write window after the calls,
   which keep a region read-only. *)
Lemma ra_widen_region : forall E ss ms i r r',
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
same_extent E r r' -> region_ok SEGS E (ms_mem ms) r' ->
regions_wf (map_nth (fun _ => r') i (ss_mem ss)) = true ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (map_nth (fun _ => r') i (ss_mem ss)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r r' HS Hn Hse Hok Hwf. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (M1 & M2 & M3) & S9).
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
do 7 (split; [assumption|]). split; [|exact S9].
split; [exact Hwf|]. split.
- exact (Forall_map_nth _ (fun _ => r') i (ss_mem ss) r Hn (fun _ => Hok) M2).
- exact (pairwise_disjoint_map_nth E (fun _ => r') i (ss_mem ss) r Hn Hse M3).
Qed.
(* ra_reshape HS i wl wh WOK: give region i of HS the write window [wl, wh), keeping its base, extent and chunks;
   WOK proves the new window writable (`forall o, wl <= o < wh -> writable_at ...`).  A plain run may only write
   awr bytes, so the globals' and the entry's windows are closed this way before one, and the fake frame's opened. *)
Ltac ra_reshape HS i wl wh WOK :=
lazymatch type of HS with st_ok_pi _ _ ?E ?ssx ?msx =>
let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
lazymatch r with YP09.mkRegion ?b ?lo ?hi _ _ ?cs =>
let HR := fresh "HR" in
pose proof (st_ok_pi_region_nth E ssx msx i r HS eq_refl) as HR;
let R1 := fresh "R1" in let R2 := fresh "R2" in let R4 := fresh "R4" in
destruct HR as (R1 & R2 & _ & R4);
unfold region_ok in R1, R2, R4; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R4;
let HN := fresh "HSn" in
assert (HN : st_ok_pi SEGS VAL E (mkSST (ss_pc ssx) (ss_regs ssx) (ss_fregs ssx)
  (map_nth (fun _ => YP09.mkRegion b lo hi wl wh cs) i (ss_mem ssx)) (ss_resv ssx) (ss_facts ssx)) msx);
[ apply (ra_widen_region E ssx msx i r (YP09.mkRegion b lo hi wl wh cs) HS eq_refl);
  [ split; reflexivity
  | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [revert R1 R2; clear; intros; lia|]; split; [revert R1 R2; clear; intros; lia|];
    split; [WOK | exact R4]
  | vm_compute; reflexivity ]
| clear HS R1 R2 R4; rename HN into HS; norm_ss HS ]
end end.
Lemma ra_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs ra_extra)) ss_ra0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_addP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx ra_SH0 (Eimg (Ereg regs ra_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE Hal32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RA_STK = 16512) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
cbn [zseps zseps_from fst snd] in HSEP.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs ra_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_ra0, A_relay_addP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ra_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, RA_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold RA_FRAME in Ho. lia.
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
+ apply pairwise_disjoint_of_extents. unfold ra_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HSEP. clear.
unfold RA_FRAME, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ra_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal32 C1 C3 WS Hstk0 HuR HuA. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ra_SH0. constructor.
Qed.
Lemma fd_signed : forall fd, - 2 ^ 31 <= fd < 2 ^ 31 -> bv_signed (Z_to_bv 64 fd) = fd.
Proof.
intros fd Hfd. assert (HU : bv_unsigned (Z_to_bv 64 fd) = if fd <? 0 then fd + 2 ^ 64 else fd).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec fd 0); [symmetry; apply (Z.mod_unique fd (2 ^ 64) (-1)); lia | apply Z.mod_small; lia]. }
destruct (Z.ltb_spec fd 0).
- rewrite bv_signed_hi by lia. lia.
- rewrite bv_signed_small by lia. lia.
Qed.
Lemma ra_lock_in : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG (RA_G RG) a.
Proof. intros a Ha. unfold RA_G, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
(* The lock's twelve bytes, kept in the ASan view, keep alock_at (their writability by GW). *)
Lemma alock_keep : forall (W W' : world SEGS) mem mem' b,
(forall a, inG (RA_G RG) a -> inG G a) ->
alock_at RG W mem b ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alock_at RG W' mem' b.
Proof.
intros W W' mem mem' b HGin (V0 & V4 & V8 & AW) HK.
split; [|split; [|split]].
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem' (rg_lock RG) 4 0); [|exact V0].
  intros j Hj. apply HK. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem' (rg_lock RG + 4) 4 _); [|exact V4].
  intros j Hj. apply HK. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem' (rg_lock RG + 8) 4 0); [|exact V8].
  intros j Hj. apply HK. lia.
- intros i Hi. unfold arm. apply GW; [apply ra_lock_in; lia|].
  apply (hidden_not_img SEGS). rewrite unsigned_lit_small.
  + exact (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia))))).
  + pose proof (pa_segs_low (rg_lock RG + i) (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia)))))).
    unfold kLowMemEnd in *. lia.
Qed.
(* Presence of image bytes along the walk (apres_kept): a run's mem_grows over the unhidden memory is presence. *)
Lemma pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, in_img SEGS a -> apresent H m0 a -> apresent H m1 a) ->
mem_grows (mrestrict H m1) (mrestrict H m2) ->
forall a, in_img SEGS a -> apresent H m0 a -> apresent H m2 a.
Proof.
intros H m0 m1 m2 P Hgr a Hi Ha. destruct (P a Hi Ha) as [Hh [b Hb]]. split; [exact Hh|].
specialize (Hgr (Z_to_bv 64 a)). unfold mrestrict in Hgr. rewrite Hh in Hgr.
destruct (m2 (Z_to_bv 64 a)) as [b2|]; [exists b2; reflexivity|]. exfalso. apply Hgr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma pres_trans : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, in_img SEGS a -> apresent H m0 a -> apresent H m1 a) ->
(forall a, in_img SEGS a -> apresent H m1 a -> apresent H m2 a) ->
forall a, in_img SEGS a -> apresent H m0 a -> apresent H m2 a.
Proof. intros H m0 m1 m2 P Q a Hi Ha. exact (Q a Hi (P a Hi Ha)). Qed.
(* fold the latest run's mem_grows into the invariant PRES *)
Ltac pres_upd PRES :=
lazymatch goal with Hg : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
let P := fresh "P" in pose proof (pres_grow H _ m1 m2 PRES Hg) as P; clear PRES Hg; rename P into PRES end.
(* the write windows of the walk's state are the frame (stack), the fake frame and its shadow (frame (0, fpos)),
   or read-only (an empty window) *)
Ltac ra_awr_tac U2b U38 U513 ly fpos F :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  lazymatch type of Hr with
  | context [ew _ 2] => rewrite U2b in Hr; left; unfold RA_STK, ASTACK, RA_FRAME; lia
  | context [ew _ 38] => rewrite U38 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd]; lia
  | context [ew _ 513] => rewrite U513 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
    right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia
  | _ => lia
  end
| ]);
destruct Hin.
(* the write windows of the locked body's state: the three table globals (g_src, g_capsrc, g_nsrc, in that order at
   the head of the state, based at Us / Uc / Un), then ra_awr_tac's frame windows *)
Ltac ra_awr_g3 Us Uc Un U2 U38 U513 ly fpos F HGin :=
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Us in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Uc in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Un in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_of0; ra_awr_tac U2 U38 U513 ly fpos F.
(* The same two, after a call that moved the layout: the journal's current layout is the callee's, and the frame
   is placed there by HFA : frame_addr ly' 0 fpos = F (the layout law alx_layout, from the journal's layout_le). *)
Ltac ra_awr_tacF U2b U38 U513 HFA fpos F :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  lazymatch type of Hr with
  | context [ew _ 2] => rewrite U2b in Hr; left; unfold RA_STK, ASTACK, RA_FRAME; lia
  | context [ew _ 38] => rewrite U38 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    rewrite HFA; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd]; lia
  | context [ew _ 513] => rewrite U513 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    rewrite HFA; change (fs_frame_bytes 0) with 64;
    right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia
  | _ => lia
  end
| ]);
destruct Hin.
Ltac ra_awr_g3F Us Uc Un U2 U38 U513 HFA fpos F HGin :=
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Us in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Uc in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Un in Ha;
  apply HGin; apply inG_cons; right; apply inG_cons; left;
  unfold in_zr; cbn [fst snd]; lia |];
apply awr_ok_x_of0; ra_awr_tacF U2 U38 U513 HFA fpos F.
(* the callee's frame-pointer chain at a call of relay_add's body: sp = sp0 - 128 and s0 = sp0, the record
   (sp0, ra, s0) of the prologue's saved words, then the entry's chain from s0 (achain_push); or no chain when sp0
   is the top (W_relay_finish_h.v rfl_chain_call, at relay_add's frame of 128 bytes) *)
Lemma ra_chain_call : forall ly (rd0 rd : reader) sp0 v ch ra,
achain ly rd0 sp0 v ch -> alloc_ceiling <= sp0 -> sp0 mod 16 = 0 -> ly_top ly <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
exists ch', achain ly rd (sp0 - 128) sp0 ch'.
Proof.
intros ly rd0 rd sp0 v ch ra Hc Hceil Hal Htop Hk H8 H16 Hra.
destruct (Z_lt_ge_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch).
  assert (Hal8 : sp0 mod 8 = 0).
  { pose proof (Z.div_mod sp0 16 ltac:(discriminate)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
    replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (Hsp' : sp0 - 128 + 16 <= sp0) by lia.
  exact (achain_push ly rd0 rd sp0 v ra ch (sp0 - 128) Hc Htop Hk H8 H16 Hra Hceil Hal8 Hlt Hsp').
- exists []. left. split; [right; left; apply Z.ge_le; exact Hge | reflexivity].
Qed.
(* ... and with room above sp0 for the caller's frame (ra_spec's premise on the realloc path), the chain is exactly
   relay_add's record on the entry's: its spine is ra :: spine ch, the caller context the realloc rule reads. *)
Lemma ra_chain_call_rec : forall ly (rd0 rd : reader) sp0 v ch ra,
achain ly rd0 sp0 v ch -> alloc_ceiling <= sp0 -> sp0 mod 16 = 0 -> ly_top ly <= 2 ^ 64 -> sp0 + 16 < ly_top ly ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
achain ly rd (sp0 - 128) sp0 ((sp0, ra, v) :: ch).
Proof.
intros ly rd0 rd sp0 v ch ra Hc Hceil Hal Htop Hroom Hk H8 H16 Hra.
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(discriminate)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
  replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
exact (achain_push ly rd0 rd sp0 v ra ch (sp0 - 128) Hc Htop Hk H8 H16 Hra Hceil Hal8 ltac:(lia) ltac:(lia)).
Qed.
(* A region of image bytes (a global of G) across a call that changes the world: the call's acall_kept keeps every
   image byte that is not owned-static and not errno, and the global stays writable by GW. *)
Lemma ra_region_kept_img : forall E lyc Sc (Wa Wb : world SEGS) memc memb slo shi (Er : Z -> Prop)
  n lo hi wlo whi cs b,
acall_kept SEGS B lyc Sc Wa memc Wb memb slo shi Er ->
bv_unsigned (ew E n) = b ->
(forall o, lo <= o < hi -> in_img SEGS (b + o) /\ ~ Exists (in_zr (b + o)) (as_owned_static B) /\
   ~ (as_errno B <= b + o < as_errno B + 4)) ->
(forall o, wlo <= o < whi -> writable_at SEGS (mrestrict (w_H Wb) memb) (b + o)) ->
region_kept SEGS E (mrestrict (w_H Wa) memc) (mrestrict (w_H Wb) memb) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc Wa Wb memc memb slo shi Er n lo hi wlo whi cs b (_ & _ & K3 & _) Hn Himg Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- destruct (Himg (a - b) ltac:(lia)) as (H1 & H2 & H3).
  replace (b + (a - b)) with a in H1, H2, H3 by ring.
  apply (mbyte_of_aview SEGS). exact (K3 a H1 H2 H3).
- intros _. specialize (Hw (a - b) ltac:(lia)). replace (b + (a - b)) with a in Hw by ring. exact Hw.
Qed.
(* ---- Three twins of AR-stated kit lemmas the walk cites, over ARx: YCbq.v:2602 region_kept_stack_aj (the journal
   ajournal_x), YCbq.v:2587 sep_blocks_perm (YGcallx.v's sep_blocks_pos_x), and W_relay_add_rep.v's rar_sep_disj /
   rar_efp_off_table (stated here, not in W_relay_add_rep.v, so that file is unchanged).  The proofs are the AR ones. *)
Lemma ra_region_kept_stack_aj_x : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
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
Lemma ra_sep_blocks_perm_x : forall ly S Hp W mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- pose proof (sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md y x b1 b2 a2 HAR ltac:(rewrite E1, E2, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint in *. zlia.
- exact (sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md x y a1 b1 b2 HAR ltac:(rewrite E1, E2; reflexivity)).
Qed.
(* two live blocks that are not the same are disjoint *)
Lemma ra_sep_disj_x : forall ly S Hp (W : world SEGS) mem md p n q m,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
  intros ly S Hp W mem md p n q m HAR H1 H2 Hne.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md p n q m HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* an old entry's footprint lies in a live block that is not the table, so off the table *)
Lemma ra_efp_off_table_x : forall ly S Hp (W : world SEGS) mem md T es,
  ARx ly S Hp W mem md -> arelay_at B RG ly S W mem T es ->
  forall e r a, In e es -> In r (aentry_fp e) -> fst r <= a < snd r ->
  exists p n, In (p, n) (ablocks B ly S) /\ 0 <= a - p < req_size n /\ ~ (T <= a < T + req_size ATABLE).
Proof.
  intros ly S Hp W mem md T es HAR HR e r a He Hr Ha.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & _ & HF & _ & HFR).
  rewrite Forall_forall in HF, HFR.
  pose proof (HF e He) as HE. pose proof (HFR e He) as HB.
  (* a block of e holding a: live, not the table, so disjoint from it *)
  assert (Hblk : forall p n, In (p, n) (aentry_blks e) -> 0 < n -> p <= a < p + n ->
    exists p n, In (p, n) (ablocks B ly S) /\ 0 <= a - p < req_size n /\ ~ (T <= a < T + req_size ATABLE)).
  { intros p n Hb Hn Hpa. exists p, n.
    pose proof (rar_aentry_blks_live B ly S W mem e HE (p, n) Hb) as Hin.
    assert (Rn : req_size n = n) by (clear - Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
    split; [exact Hin|]. split; [rewrite Rn; clear - Hpa; lia|].
    destruct (ra_sep_disj_x ly S Hp W mem md p n T ATABLE HAR Hin HinT (HB (p, n) Hb)) as [D|D];
      clear - D Rn Hpa; lia. }
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - (* the buffer *)
    destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
    destruct HE as (_ & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _).
    destruct H10 as [(Hc0 & _) | (Hcp & _ & Hj & _)]; [exfalso; exact (Hc Hc0)|].
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd] in Ha.
    apply (Hblk (re_buf e) (re_cap e)).
    + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + exact Hcp.
    + clear - Ha H7 Hj. lia.
  - destruct Hr as [<- | Hr].
    + (* the held array *)
      pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _).
      destruct H12 as [(Hz & Hk) | (Hz & _ & Hk1 & Hk2 & _)].
      * exfalso. unfold gfp, bzs in Ha. rewrite length_map, Hk in Ha. cbn in Ha. clear - Ha. lia.
      * unfold gfp, bzs in Ha. rewrite length_map, rar_key_ptrs_len in Ha. cbn [fst snd] in Ha.
        apply (Hblk (re_hp e) (re_kh e)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
           rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- clear - Hk2. lia.
        -- unfold re_nheld in Hk1. clear - Ha Hk1. lia.
    + (* a key's text *)
      apply in_map_iff in Hr as (k & <- & Hk).
      unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
      eapply Hblk.
      * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists k. split; [reflexivity | exact Hk].
      * clear. lia.
      * clear - Ha. lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): relay_add's walk at a world relation R.  Its realloc of the table re-hides at the
   cf instance (R := wle' SEGS RZ_cf), so the walk runs at SRrG SEGS R: the runs and branches before and after the call
   at their G twins (YC80xR, W_frame_x, W_journal_x, W_kit's paj_branch_xR), the realloc at its R rule (AREALLOC_R, with
   RO from ARx and the hull admission HA from the meter), the lock / unlock / memset entries through
   W_sites_x's R call steps, the fake-frame call and the return lifted from their strict forms.  At R := wle
   (RO := fun _ => True, HAD := fun _ _ _ _ _ _ => True) it is pb_relay_add_x below.  The contract text ra_spec_xR is W_contract_srlf_xR.v's. *)
Section raR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HAD : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
(* the realloc's hull admission at the call, from the meter's mo_ok at the call: at reply's top
   HAD := (fun _ Sc _ _ _ n => cf_hull_adm Sc n), and the top discharges HA_ra from the meter *)
Hypothesis HA_ra : forall lyc Sc regsT ch p n, 1 <= n -> mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HAD lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HAD CTX R (SIGMA WS_realloc).
Let RUNR := YC80xR.SRrG_run_pi_tok_AJxG wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA fr_prog_listing
(@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text
(@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr) (@pl_tw_eq fr_prog_listing PL_fr)
(R := R).
Let RUNXR := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOXR := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNFR := aj_flag_store_pi_xG (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE (R := R).
Lemma ra_region_kept_stack_aj_xR : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
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
Theorem pb_relay_add_xR : ra_spec_xR B PST ARx R MT RP G RG CTX A_relay_addP.
Proof.
intros W ly S Hp regs mem md ch fd T es HPRE Hal32 HCNT H10 Rfd HLOCK HWAKE HROM HREL HNEW HGin HGerr HLIVE HCTX HMOK kr HRM HPK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (ra_entry W ly S Hp regs mem md ch HPRE Hal32) as [HS SHOK].
assert (PRES : forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a _ Ha; exact Ha).
pose proof (ajournal_x_initR SEGS B PST ARx R_refl RA_STK (ra_FP T es) ly S Hp W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs ra_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs ra_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RA_STK = 16512) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 A_relay_addP) with (Z_to_bv 64 A_relay_addP). unfold A_relay_addP, A_relay_add.
paj_run_tok_xR RUNR HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
pres_upd PRES.
(* the call to __asan_stack_malloc_0 (64): the fake frame *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (W_frame_x.aj_stack_malloc_pres_at_raw_xR SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC R_trans WLE_R 0 ASM0 ltac:(lia) W rg mm RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly S Hp _ 0 (-128) _ HJ) end.
- unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
- reflexivity. - lia. - rewrite WS, Hes. lia.
- rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPR0 & HRAW & (fS2 & ES2)).
(* the room across the fake-frame seat (RPF): ra_spec's budget, now at S2 *)
assert (HRM2 : rp_RM RP S2 (Z.to_nat (ra_cost MT_rk T) + kr)) by (rewrite ES2; exact (RPF S fS2 _ HRM)).
clear HRM.
pose proof (pres_trans _ _ _ _ PRES HPR0) as P; clear PRES HPR0; rename P into PRES.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (palf_uar_img B TLF) as HuR.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
- eapply ra_region_kept_stack_aj_xR; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
[exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
- apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
[rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs ra_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs ra_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E33).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 38 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 38 33 513 F SB E38 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by exact (HEIb (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U273 : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by exact (HEIb (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32 : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
pose proof (pa_val_range (A_OBJ 0)) as PV0. pose proof (pa_val_range (A_OBJ 1)) as PV1. pose proof (pa_val_range (A_OBJ 32)) as PV32.
(* the geometry facts in numerals, once: the per-goal lia then unfolds only its goal *)
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in C1, C3, Hslo, Hshi, H47, Hceil, Hstk0,
HcellR, HgotR, HguR, HuR, HSEP, HFimg, HFapp, HF4096, HFceil, HFhigh, HFLapp, HFLimg, HFL4096, HFLc.
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 38 512 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U38; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (64 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (64 - 8)) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32; clear; intros;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz; apply Hz; change (64 / 8) with 8; lia ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513, U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32 HF8lo HF8hi HFq HF8; clear; intros;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header and the shadow poison: a plain run (the token run keeps its windows off the shadow) *)
paj_run_sh_x RUNPR HS HJ2.
{ intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
lazymatch type of Hr with
| context [ew _ 2] => rewrite U2b in Hr; left; unfold RA_STK, ASTACK, RA_FRAME; lia
| context [ew _ 38] => rewrite U38 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
  change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd]; lia
| context [ew _ 513] => rewrite U513 in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
  change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
  right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia
| _ => lia
end
| ]).
destruct Hin. }
pres_upd PRES.
(* relay_add's globals as the walk finds them here, kept from the entry: by the first run's frame, the fake-frame
   seat's RAW clause (image bytes off as_owned_static, so aowned in neither state by alx_owned_image, and below the
   callee's stack window) and the header run's frame.  The AR walk read this off the journal's image clause, which
   ajournal_x states only off PST. *)
assert (RAGB : forall a, inG (RA_G RG) a -> 65536 <= a < 6270976).
{ pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(left; reflexivity)) as RBLK. cbn [fst snd] in RBLK.
  pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; left; reflexivity)) as RBNS. cbn [fst snd] in RBNS.
  pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(right; right; left; reflexivity)) as RBCS. cbn [fst snd] in RBCS.
  pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as RBSR. cbn [fst snd] in RBSR.
  intros a Har. unfold RA_G in Har.
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; clear - Hzr RBLK; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; clear - Hzr RBNS; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; clear - Hzr RBCS; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; clear - Hzr RBSR; lia|].
  exfalso; exact (inG_nil a Har). }
lazymatch type of HJ2 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ =>
assert (RAK : forall a, inG (RA_G RG) a -> aview SEGS (w_H W) mx a = aview SEGS (w_H W) mem a) end.
{ assert (HWR : 6270976 < spZ regs - 20608 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8)
    by (split; [revert Hslo Hceil Hstk0 C1; clear; intros; lia|];
        split; [exact HFimg|]; revert HF8lo; clear; unfold SB; intros; lia).
  intros a Ha. pose proof (RAGB a Ha) as HaB. destruct (HG a (HGin a Ha)) as (HaIk & HaOk & _).
  etransitivity.
  { exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 a ltac:(clear - HaB; lia)
      ltac:(ra_errno_out HaB HWR HFLimg HaIk U2b U38 U513 U512)). }
  etransitivity.
  { exact (HRAW a ltac:(clear - HaB; lia)
      (fun Ho => HaOk (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARa HaIk) Ho))
      (fun Ho => HaOk (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARb HaIk) Ho))
      ltac:(revert HaB Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; unfold ESTACK; lia)). }
  exact (aview_kept_out E _ (w_H W) _ _ HFr a ltac:(clear - HaB; lia)
    ltac:(ra_errno_out HaB HWR HFLimg HaIk Usp U38 U513 U512)). }
assert (E10b : sv_denot Eb (SOff 10 0) = Z_to_bv 64 fd)
by (cbn [sv_denot]; rewrite OLDb, OLDa, (EE 10%nat 10%bv eq_refl), H10 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_pi_x RUNPR BRR HS.
-
(* fd < 0: return -1 *)
assert (Hneg : fd < 0).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
rewrite (fd_signed fd Rfd) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
pose proof (proj1 HJ2) as HARc.
lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
destruct (FFL _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (HFLp' & HFLo' & _ & _) end.
lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
destruct (alx_frames _ _ _ LAWS _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (_ & _ & HFpres' & HFSpres') end.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFLp', HFLo', HFpres', HFSpres'.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U512; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp')
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U512, U513, U38, U2b, U241, U242, U273, U32;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres' FL ltac:(lia)) HFLo')
| |- ?fl + 1 <= SB + F / 8 + ?l \/ SB + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (SB + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (SB + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres';
  exact (proj2 (HFSpres' (FL - (SB + F / 8)) ltac:(lia)) ltac:(replace (SB + F / 8 + (FL - (SB + F / 8))) with FL by lia; exact HFLo'))
| |- ?g =>
  first [ revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HgotR HcellR HguR HuR PV0 PV1 PV32 HFL4096 HFLz HFLc; clear; intros;
          unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
        | idtac "FLAGGOAL" g; fail 1 ]
end)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
paj_run_flag_sh_x RUNFR HS HJ2.
{ lia. }
{ intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
cbn [In] in Hin. change (flag_addr ly 0 fpos) with FL.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
lazymatch type of Hr with
| context [ew _ 2] => rewrite U2b in Hr; left; left; unfold RA_STK, ASTACK, RA_FRAME; lia
| context [ew _ 512] => rewrite U512 in Hr; right; lia
| context [ew _ 38] => rewrite U38 in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
  change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd]; lia
| context [ew _ 513] => rewrite U513 in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
  change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
  right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia
| _ => lia
end
| ]).
destruct Hin. }
{ intros msr HSr. change (flag_addr ly 0 fpos) with FL.
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
pres_upd PRES.
prreg HS (10%bv : bv 5) Rr10. prreg HS (1%bv : bv 5) Rr1.
assert (EabF : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ra_post_xR.
lazymatch type of HJ2 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Hpx _ _ _ ?kx =>
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyx, Sx, Hpx, r, m, d, kx end end.
split; [cbn [ms_regs]; rewrite Rr1, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split.
{ cbn [ms_mem]. eapply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md []).
all: [> lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs); exact HJ2 | apply gagree_refl | intros a Ha; lia]. }
split. { eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs ra_extra HS); [exact HAEb | vm_compute; reflexivity]. }
split. { intros a Hi _ _ Ha. exact (PRES a Hi Ha). }
split. { pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr' & _). cbn [app] in Hfr'. exact Hfr'. }
split.
{ assert (MOseat : mo_le MT S S2 0) by (rewrite ES2; exact (MO_FR S fS2)).
  assert (MOrel : mo_le MT S2 (stack_free_state 0 fpos S2) 0) by (unfold stack_free_state; exact (MO_FR S2 _)).
  pose proof (mle_station MT S S2 (stack_free_state 0 fpos S2) 0 0 MLAW MOseat MOrel) as MOsr. rewrite Z.add_0_r in MOsr.
  apply (mle_weaken MT S _ 0 (ra_cost MT T) MLAW MOsr). unfold ra_cost. destruct (T =? 0);
[pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)); pose proof (mo_free_nonneg MT MLAW); lia | lia]. }
split.
{ (* the room: no allocator call on this arm (RMM), then the fake frame's release (RPF) *)
  unfold stack_free_state. apply RPF. exact (RMM S2 kr _ (Nat.le_add_l kr _) HRM2). }
split.
{ cbn [ms_mem]. apply (alock_keep W W mem _ false HGin HLOCK). intros a Ha.
assert (HWR : 6270976 < spZ regs - 20608 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8)
  by (split; [revert Hslo Hceil Hstk0 C1; clear; intros; lia|];
      split; [exact HFimg|]; revert HF8lo; clear; unfold SB; intros; lia).
pose proof (ra_lock_in a Ha) as Hla. pose proof (RAGB a Hla) as HaB. pose proof (proj1 (HG a (HGin a Hla))) as HaIk.
etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 a ltac:(clear - HaB; lia)
  ltac:(ra_errno_out HaB HWR HFLimg HaIk U2b U38 U513 U512))|].
exact (RAK a Hla). }
split; [left; split; [exact Hneg|]; split; [cbn [ms_regs]; rewrite Rr10; apply bv_eq; reflexivity | exact EabF]|].
(* ra_post's errno conjunct (W_contract.v ra_post, last clause).  errno is an image byte in the band (HIG) and in
   no write window of the three runs (ra_errno_out), and the fake-frame seat keeps it through the RAW clause of
   aj_stack_malloc_pres_at_raw_x: errno is aowned in neither state (errno_not_aowned_x, from the instance fact HEO) and
   lies below the callee's stack window. *)
intros i Hi.
pose proof (proj1 (Forall_forall _ _) HIG (as_errno B, 4) ltac:(do 5 right; left; reflexivity)) as BE.
cbn [fst snd] in BE.
assert (HaE : 65536 <= as_errno B + i < 6270976) by (clear - BE Hi; lia).
assert (HWE : 6270976 < spZ regs - 20608 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8).
{ split; [revert Hslo Hceil Hstk0 C1; clear; intros; lia|].
  split; [exact HFimg|]. revert HF8lo; clear; unfold SB; intros; lia. }
pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + i) ltac:(clear - Hi; lia)) as HaI.
etransitivity.
{ exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 (as_errno B + i) ltac:(clear - HaE; lia)
    ltac:(ra_errno_out HaE HWE HFLimg HaI U2b U38 U513 U512)). }
etransitivity.
{ exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 (as_errno B + i) ltac:(clear - HaE; lia)
    ltac:(ra_errno_out HaE HWE HFLimg HaI U2b U38 U513 U512)). }
etransitivity.
{ exact (HRAW (as_errno B + i) ltac:(clear - HaE; lia)
    (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARa HEO i Hi)
    (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARb HEO i Hi)
    ltac:(revert HaE Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; unfold ESTACK; lia)). }
exact (aview_kept_out E _ (w_H W) _ _ HFr (as_errno B + i) ltac:(clear - HaE; lia)
  ltac:(ra_errno_out HaE HWE HFLimg HaI Usp U38 U513 U512)).
-
(* fd >= 0: under g_lock, the table grows when full and the entry is appended *)
assert (Hpos : 0 <= fd).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
rewrite (fd_signed fd Rfd) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
(* the lock as the walk finds it: kept from the entry (RAK) *)
lazymatch type of HJ2 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ =>
assert (LKc : alock_at RG W mx false) by
(apply (alock_keep W W mem _ false HGin HLOCK); intros a Ha;
 exact (RAK a (ra_lock_in a Ha))) end.
(* from here the walk writes globals: the journal at G *)
lazymatch type of HJ2 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?own ?ly' ?S' ?Hp' ?W' ?m' ?md' ?k' =>
pose proof (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md own ly' S' Hp' W' m' md' k' mem
  ltac:(lia) ltac:(lia) ltac:(rewrite !Z.add_0_r; exact HJ2) (gagree_refl _ _ _) ltac:(intros a Ha; lia)) as HJg end.
(* the token runner keeps its regions off the shadow span: drop the frame-shadow region (head of the state) for the
   locked body; it is added back, chunk-free, before the frame's shadow is written again *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 513%nat) _ _ _ _ _ :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx rest HS ltac:(vm_compute; apply submem_drop; apply submem_refl)
    ltac:(vm_compute; reflexivity)) as HS3
end end.
clear HS; rename HS3 into HS. norm_ss HS.
(* ... and the fake frame read-only (an empty window: the locked body does not write it) *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
lazymatch eval vm_compute in (ss_mem ssx) with
| YP09.mkRegion (Some 38%nat) ?lo ?hi ?wlo ?whi ?cs :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx (YP09.mkRegion (Some 38%nat) lo hi 0 0 cs :: rest) HS
    ltac:(vm_compute; apply submem_keep; [unfold subregion; cbn; split; [reflexivity|]; split; [lia|]; split; [lia|];
          split; [left; lia | auto] | apply submem_refl])
    ltac:(vm_compute; reflexivity)) as HS3
end end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H W) ?msx) =>
assert (SHOK2 : sh_ok SEGS Bx [] Ex (mrestrict (w_H W) (ms_mem msx))) by constructor end.
paj_run_tok_xR RUNXR HS HJg SHOK2 Bspan. { apply awr_ok_x_of0. ra_awr_tac U2b U38 U513 ly fpos F. }
pres_upd PRES.
(* ---- the lock (a PCall to pthread_mutex_lock, a0 = &g_lock = VAL (A_OBJ 6)) ---- *)
pose proof (pa_obj_img 6 ltac:(lia)) as HL6. rewrite HV6 in HL6.
(* the lock as the call finds it: the run wrote only its windows (the frame; the fake frame is read-only) *)
lazymatch type of HFr1 with frame_of ?Ev ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (LKd : alock_at RG W m1 false);
[ apply (alock_keep W W m0 m1 false HGin LKc); intros a Ha;
  apply (aview_kept_out Ev rs (w_H W) m0 m1 HFr1 a ltac:(lia));
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b in Hr;
      revert Hr; clear - Ha HL6 Hslo Hshi H47 Hceil Hstk0 C1 C3; unfold RA_FRAME in *; lia | ]);
  destruct Hin
| ] end.
pose proof LKd as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
assert (HSPc : spZ (ms_regs ms1) = spZ regs + -128).
{ unfold spZ at 1. rewrite QSP, U2b. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms1) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP Eb (A_OBJ 6) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV6. reflexivity. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg) as HARd.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms1) a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms1) (rg_lock RG) = Some 0).
{ unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S2 a).
{ intros a Ha Ho. destruct (HG a (HGin a (ra_lock_in a Ha))) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S2 _ W (ms_mem ms1) _ a HARd Hi) Ho). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md _ _ _ _ _ _ (-128) _ HG eq_refl HJg).
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
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply HGin. apply ra_lock_in. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + exact HLA.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * apply GW; [apply ra_lock_in; lia|].
        exact (hidden_not_img SEGS W (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact (proj1 (HG a (HGin a (ra_lock_in a ltac:(lia))))))).
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKx. exact (proj2 (proj2 (HG a (HGin a (ra_lock_in a ltac:(revert Ha; clear; intros; lia))))) (proj1 (proj2 HKx))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HLK3 & Hfr3 & Hpres3).
pose proof (pres_trans _ _ _ _ PRES (fun a (_ : in_img SEGS a) (H : apresent (w_H W) (ms_mem ms1) a) => Hpres3 a H)) as P;
clear PRES; rename P into PRES.
(* back in relay_add, the lock held *)
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARd) as (Kc3a & Ku3a & Kg3a & Kgu3a).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR3) as (Kc3 & Ku3 & Kg3 & Kgu3).
rewrite HBgot, HBcell in Kg3a, Kg3. rewrite HBcell in Kc3a, Kc3. rewrite (palf_got_uar B TLF) in Kgu3a, Kgu3.
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- apply (region_kept_aview Eb (w_H W) (ms_mem ms1) mem3 38 F); [exact U38 | | exact Hpres3].
  intros a Ha. apply Hfr3;
  [ lia
  | clear - Ha HL6 HF4096 HFceil HFhigh HFimg; lia
  | revert Ha HF4096 HFceil HFhigh HFimg Hslo Hshi H47 Hceil Hstk0 C1 WS Hes; clear; intros; lia ].
- apply (region_kept_aview Eb (w_H W) (ms_mem ms1) mem3 2 (spZ regs)); [exact U2b | | exact Hpres3].
  intros a Ha. apply Hfr3;
  [ revert Ha Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
  | revert Ha HL6 Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
  | revert Ha; clear; intros; lia ].
- apply (region_kept_val_at Eb _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
  [exact U241 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg3a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg3) | lia].
- apply (region_kept_val_at Eb _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
  [exact U273 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc3a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc3) | lia].
- apply (region_kept_val_at Eb _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
  [exact U242 | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu3a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu3) | lia].
- apply (region_kept_val_at Eb _ _ 32 (as_uar_cell B) 4 1);
  [exact U32 | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku3a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku3) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Eb 50 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 50)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (ABVc : forall m, (66 <= m)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply ew_havoc_above; cbn; lia).
assert (HAEc : env_agree 32 (Ereg regs ra_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (U2c : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact U2b).
assert (U38c : bv_unsigned (ew Ec 38) = F) by (rewrite OLDc by lia; exact U38).
assert (U512c : bv_unsigned (ew Ec 512) = FL) by (rewrite ABVc by lia; exact U512).
assert (U513c : bv_unsigned (ew Ec 513) = SB + F / 8) by (rewrite ABVc by lia; exact U513).
(* ---- the three table globals, carried from the entry: every step so far wrote the frame, the fake frame and
   the lock word only. ---- *)
pose proof (proj1 (Forall_forall _ _) HIG (rg_lock RG, 12) ltac:(left; reflexivity)) as BLK. cbn [fst snd] in BLK.
pose proof (proj1 (Forall_forall _ _) HIG (rg_nsrc RG, 4) ltac:(right; left; reflexivity)) as BNS. cbn [fst snd] in BNS.
pose proof (proj1 (Forall_forall _ _) HIG (rg_capsrc RG, 4) ltac:(right; right; left; reflexivity)) as BCS. cbn [fst snd] in BCS.
pose proof (proj1 (Forall_forall _ _) HIG (rg_src RG, 8) ltac:(right; right; right; left; reflexivity)) as BSR. cbn [fst snd] in BSR.
assert (HGB : forall a, inG (RA_G RG) a -> 65536 <= a < 6270976).
{ intros a Har. unfold RA_G in Har.
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; lia|].
  apply inG_cons in Har; destruct Har as [Hzr|Har]; [unfold in_zr in Hzr; cbn [fst snd] in Hzr; lia|].
  exfalso; exact (inG_nil a Har). }
assert (HWOUT : 6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8).
{ split; [revert Hslo Hceil Hstk0 C1; clear; intros; lia|].
  split; [exact HFimg|]. revert HF8lo; clear; unfold SB; intros; lia. }
assert (KEEPG : forall a, inG (RA_G RG) a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnw. pose proof (HGB a Ha) as HaB.
  rewrite (Hfr3 a ltac:(lia) Hnw ltac:(unfold ESTACK; revert HaB Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia)).
  rewrite (aview_kept_out Eb _ (w_H W) _ _ HFr1 a ltac:(lia) ltac:(ra_glob_out HaB HWOUT U2b U38 U513)).
  exact (RAK a Ha). }
(* the entry's values of the three cells, in one form for both arms of ra_rel *)
assert (HTne : T <> 0 -> In (T, ATABLE) (ablocks B ly S)).
{ intros HT. destruct HREL as [(HT0 & _ & _) | HR]; [lia|].
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & Hin & _). exact Hin. }
assert (ENT : val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\
              val_mem SEGS (arm W mem) (rg_capsrc RG) 4 (if T =? 0 then 0 else 16) /\
              val_mem SEGS (arm W mem) (rg_src RG) 8 T).
{ destruct HREL as [(HT0 & Hes0 & HE) | HR].
  - subst T. subst es. cbn [length Z.of_nat]. cbn [Z.eqb].
    destruct HE as (V8 & _ & V4 & _ & V4c & _). split; [exact V4 | split; [exact V4c | exact V8]].
  - destruct HR as (V8 & _ & V4 & _ & V4c & _ & _ & Hin & _).
    destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR Hin) as (_ & H4096 & _).
    destruct (Z.eqb_spec T 0) as [->|_]; [lia|].
    split; [exact V4 | split; [exact V4c | exact V8]]. }
destruct ENT as (ENTn & ENTc & ENTs).
assert (GN3 : val_mem SEGS (mrestrict (w_H W) mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 _); [|exact ENTn].
  intros j Hj. apply KEEPG; [apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; cbn in Hj; lia|].
  ra_zsep_pick HSEPG 4%nat 5%nat D45. cbn in Hj. lia. }
assert (GC3 : val_mem SEGS (mrestrict (w_H W) mem3) (rg_capsrc RG) 4 (if T =? 0 then 0 else 16)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_capsrc RG) 4 _); [|exact ENTc].
  intros j Hj. apply KEEPG;
  [apply inG_cons; right; apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; cbn in Hj; lia|].
  ra_zsep_pick HSEPG 4%nat 6%nat D46. cbn in Hj. lia. }
assert (GS3 : val_mem SEGS (mrestrict (w_H W) mem3) (rg_src RG) 8 T).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_src RG) 8 _); [|exact ENTs].
  intros j Hj. apply KEEPG;
  [apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
   unfold in_zr; cbn [fst snd]; cbn in Hj; lia|].
  ra_zsep_pick HSEPG 4%nat 7%nat D47. cbn in Hj. lia. }
(* bounds of the three seated values *)
assert (HNB : 0 <= Z.of_nat (length es) <= 16).
{ destruct HREL as [(_ & Hes0 & _) | HR]; [subst es; cbn; lia|].
  destruct HR as (_ & _ & _ & _ & _ & _ & Hlen & _). lia. }
assert (HTB : 0 <= T < alloc_ceiling).
{ destruct (Z.eqb_spec T 0) as [->|HT]; [pose proof ASAN_CEIL_range; unfold ASAN_CEIL in *; lia|].
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR (HTne HT)) as (_ & H4096 & Hceil2 & _).
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)). unfold ATABLE in *. lia. }
(* seat |es|, the capacity and the table pointer as the atoms 514, 515, 516 *)
pose proof (st_ok_pi_havoc_hi 514 Ec _ _
[Z_to_bv 64 (Z.of_nat (length es)); Z_to_bv 64 (if T =? 0 then 0 else 16); Z_to_bv 64 T] HS
ltac:(vm_compute; reflexivity)) as HS4.
clear HS. rename HS4 into HS.
remember (havoc Ec 514 [Z_to_bv 64 (Z.of_nat (length es)); Z_to_bv 64 (if T =? 0 then 0 else 16); Z_to_bv 64 T])
as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc_hi; [exact HEIc | cbv; lia]).
assert (OLDd : forall m, (m < 514)%nat -> ew Ed m = ew Ec m) by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E514 : ew Ed 514 = Z_to_bv 64 (Z.of_nat (length es)))
by (rewrite HEd; exact (ew_havoc_new _ 514
[Z_to_bv 64 (Z.of_nat (length es)); Z_to_bv 64 (if T =? 0 then 0 else 16); Z_to_bv 64 T]
0 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
assert (E515 : ew Ed 515 = Z_to_bv 64 (if T =? 0 then 0 else 16))
by (rewrite HEd; exact (ew_havoc_new _ 514
[Z_to_bv 64 (Z.of_nat (length es)); Z_to_bv 64 (if T =? 0 then 0 else 16); Z_to_bv 64 T]
1 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
assert (E516 : ew Ed 516 = Z_to_bv 64 T)
by (rewrite HEd; exact (ew_havoc_new _ 514
[Z_to_bv 64 (Z.of_nat (length es)); Z_to_bv 64 (if T =? 0 then 0 else 16); Z_to_bv 64 T]
2 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
assert (HAEd : env_agree 32 (Ereg regs ra_extra) Ed) by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
clear HEd.
assert (U2d : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by lia; exact U2c).
assert (U38d : bv_unsigned (ew Ed 38) = F) by (rewrite OLDd by lia; exact U38c).
assert (U513d : bv_unsigned (ew Ed 513) = SB + F / 8) by (rewrite OLDd by lia; exact U513c).
assert (U310 : bv_unsigned (ew Ed (A_HI 30)) = rg_nsrc RG + 704)
by (rewrite <- HH30, Z.sub_add; exact (HEId (A_HI 30) ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
assert (U311 : bv_unsigned (ew Ed (A_HI 31)) = rg_capsrc RG + 612)
by (rewrite <- HH31, Z.sub_add; exact (HEId (A_HI 31) ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
assert (U312 : bv_unsigned (ew Ed (A_HI 32)) = rg_src RG + 688)
by (rewrite <- HH32, Z.sub_add; exact (HEId (A_HI 32) ltac:(unfold A_HI, A_TEXT, A_LIM; lia))).
change (A_HI 30) with 310%nat in U310. change (A_HI 31) with 311%nat in U311. change (A_HI 32) with 312%nat in U312.
assert (U241d : bv_unsigned (ew Ed 241) = VAL (A_OBJ 0)) by (rewrite OLDd, ABVc by lia; exact U241).
assert (U242d : bv_unsigned (ew Ed 242) = VAL (A_OBJ 1)) by (rewrite OLDd, ABVc by lia; exact U242).
assert (U273d : bv_unsigned (ew Ed 273) = VAL (A_OBJ 32)) by (rewrite OLDd, ABVc by lia; exact U273).
assert (U32d : bv_unsigned (ew Ed 32) = as_uar_cell B) by (rewrite OLDd, OLDc by lia; exact U32).
assert (U248 : bv_unsigned (ew Ed 248) = rg_nsrc RG)
by (rewrite <- HV7; exact (HEId (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (U257 : bv_unsigned (ew Ed 257) = rg_capsrc RG)
by (rewrite <- HV16; exact (HEId (A_OBJ 16) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (U249 : bv_unsigned (ew Ed 249) = rg_src RG)
by (rewrite <- HV8; exact (HEId (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
(* the writability of a global byte, in any memory (GW) *)
assert (GWn : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W) mem3) (rg_nsrc RG + o)).
{ intros o Ho.
  assert (Hin : inG (RA_G RG) (rg_nsrc RG + o))
  by (apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
  apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by lia.
  exact (proj1 (HG _ (HGin _ Hin))). }
assert (GWc : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W) mem3) (rg_capsrc RG + o)).
{ intros o Ho.
  assert (Hin : inG (RA_G RG) (rg_capsrc RG + o))
  by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
  apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by lia.
  exact (proj1 (HG _ (HGin _ Hin))). }
assert (GWs : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem3) (rg_src RG + o)).
{ intros o Ho.
  assert (Hin : inG (RA_G RG) (rg_src RG + o))
  by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia).
  apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by lia.
  exact (proj1 (HG _ (HGin _ Hin))). }
(* the three base atoms need an image-band fact, or the token runner's static check cannot place their regions
   against the shadow span *)
pose proof (st_ok_pi_add_fact Ed _ _ 248 (mkAF 65536 6270976 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U248, Z.pow_0_r, Z.mod_1_r; clear - BNS; lia)) as HSa.
clear HS; rename HSa into HS.
pose proof (st_ok_pi_add_fact Ed _ _ 257 (mkAF 65536 6270976 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U257, Z.pow_0_r, Z.mod_1_r; clear - BCS; lia)) as HSa.
clear HS; rename HSa into HS.
pose proof (st_ok_pi_add_fact Ed _ _ 249 (mkAF 65536 6270976 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U249, Z.pow_0_r, Z.mod_1_r; clear - BSR; lia)) as HSa.
clear HS; rename HSa into HS. norm_ss HS.
(* The three global regions.  Every side `lia` here runs over a cleared context: the separation picks are
   disjunctions and are posed only inside the disjointness proof that needs them (lia splits every disjunction it
   sees - with fifteen of them in the context one compile went past 200 GB). *)
(* g_nsrc *)
pose proof (st_ok_pi_add_region Ed _ _ ra_nsrc_region HS ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok, ra_nsrc_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite U248; split; [clear - BNS; lia|]; split; [clear - BNS; lia|]; split;
  [ intros o Ho; exact (GWn o Ho)
  | apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 514 0) (Z.of_nat (length es)));
    [ cbn [sv_denot]; rewrite E514, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HNB; zside | clear; zside |];
    rewrite Z.add_0_r; exact GN3 ])
ltac:(ra_zsep_pick HSEPG 0%nat 5%nat P05; ra_zsep_pick HSEPG 1%nat 5%nat P15;
  ra_zsep_pick HSEPG 2%nat 5%nat P25; ra_zsep_pick HSEPG 3%nat 5%nat P35;
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, ra_nsrc_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite U248, U2d, U38d, U241d, U242d, U273d, U32d;
  repeat split;
  first [ solve [clear - P05; lia] | solve [clear - P15; lia] | solve [clear - P25; lia] | solve [clear - P35; lia]
        | solve [clear - BNS HWOUT; lia] ])) as HS5.
clear HS; rename HS5 into HS. norm_ss HS.
idtac "CP-NSRC".
(* g_capsrc *)
pose proof (st_ok_pi_add_region Ed _ _ ra_capsrc_region HS ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok, ra_capsrc_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite U257; split; [clear - BCS; lia|]; split; [clear - BCS; lia|]; split;
  [ intros o Ho; exact (GWc o Ho)
  | apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ed _ (rg_capsrc RG) 0 4 (SOff 515 0) (if T =? 0 then 0 else 16));
    [ cbn [sv_denot]; rewrite E515, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear; destruct (T =? 0); zside | clear; zside |];
    rewrite Z.add_0_r; exact GC3 ])
ltac:(ra_zsep_pick HSEPG 0%nat 6%nat P06; ra_zsep_pick HSEPG 1%nat 6%nat P16;
  ra_zsep_pick HSEPG 2%nat 6%nat P26; ra_zsep_pick HSEPG 3%nat 6%nat P36; ra_zsep_pick HSEPG 5%nat 6%nat P56;
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, ra_capsrc_region, ra_nsrc_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite U257, U248, U2d, U38d, U241d, U242d, U273d, U32d;
  repeat split;
  first [ solve [clear - P06; lia] | solve [clear - P16; lia] | solve [clear - P26; lia] | solve [clear - P36; lia]
        | solve [clear - P56; lia] | solve [clear - BCS HWOUT; lia] ])) as HS6.
clear HS; rename HS6 into HS. norm_ss HS.
idtac "CP-CAPSRC".
(* g_src *)
pose proof (st_ok_pi_add_region Ed _ _ ra_src_region HS ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok, ra_src_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite U249; split; [clear - BSR; lia|]; split; [clear - BSR; lia|]; split;
  [ intros o Ho; exact (GWs o Ho)
  | apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ed _ (rg_src RG) 0 8 (SOff 516 0) T);
    [ cbn [sv_denot]; rewrite E516, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HTB C1; zside | clear; zside |];
    rewrite Z.add_0_r; exact GS3 ])
ltac:(ra_zsep_pick HSEPG 0%nat 7%nat P07; ra_zsep_pick HSEPG 1%nat 7%nat P17;
  ra_zsep_pick HSEPG 2%nat 7%nat P27; ra_zsep_pick HSEPG 3%nat 7%nat P37;
  ra_zsep_pick HSEPG 5%nat 7%nat P57; ra_zsep_pick HSEPG 6%nat 7%nat P67;
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, ra_src_region, ra_capsrc_region, ra_nsrc_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite U249, U257, U248, U2d, U38d, U241d, U242d, U273d, U32d;
  repeat split;
  first [ solve [clear - P07; lia] | solve [clear - P17; lia] | solve [clear - P27; lia] | solve [clear - P37; lia]
        | solve [clear - P57; lia] | solve [clear - P67; lia] | solve [clear - BSR HWOUT; lia] ])) as HS7.
clear HS; rename HS7 into HS. norm_ss HS.
idtac "CP-SRC".
(* the loads of g_nsrc and g_capsrc, up to the `bne` that decides whether the table must grow *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H W) ?msx) =>
assert (SHOK5 : sh_ok SEGS Bx [] Ex (mrestrict (w_H W) (ms_mem msx))) by constructor end.
paj_run_tok_xR RUNXR HS HJ3 SHOK5 Bspan.
{ apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha;
    apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
    unfold in_zr; cbn [fst snd]; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U257 in Ha;
    apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
    unfold in_zr; cbn [fst snd]; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U248 in Ha;
    apply HGin; apply inG_cons; right; apply inG_cons; left;
    unfold in_zr; cbn [fst snd]; lia |].
  apply awr_ok_x_of0. ra_awr_tac U2d U38d U513d ly fpos F. }
pres_upd PRES.
lazymatch type of HS with ?t => idtac "STATE" t end.
(* the `bne` compares the two 32-bit cells sign-extended; both are small and non-negative *)
assert (SXn : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 514 0))) = Z.of_nat (length es)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 514 0))) with (U Ed (SOff 514 0)).
  rewrite (U_atom Ed 514 _ E514) by (clear - HNB; lia). apply sx32_small. clear - HNB; lia. }
assert (SXc : bv_unsigned (sv_denot Ed (SExt true 32 (SOff 515 0))) = (if T =? 0 then 0 else 16)).
{ rewrite U_sext32'. change (bv_unsigned (sv_denot Ed (SOff 515 0))) with (U Ed (SOff 515 0)).
  rewrite (U_atom Ed 515 _ E515) by (clear; destruct (T =? 0); lia).
  apply sx32_small. clear; destruct (T =? 0); lia. }
(* zcanon on a value that fits: `lia` cannot see through M64, so the bound is given once, here, and every
   arithmetic step below rewrites with it innermost first. *)
assert (ZC : forall v, 0 <= v < 2 ^ 64 -> zcanon v = v)
by (intros v Hv; apply zcanon_id; unfold M64; exact Hv).
(* the address of the entry relay_add appends, g_src + (|es| * 64 - |es| * 8) = T + AENT * |es|, as a value:
   the T <> 0 arm keeps it in s4 and passes it to the memset in a0 (there with a `+ 0`) *)
assert (HEA : U Ed (SAlu ALU_ADD (SOff 516 0)
  (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 6))
                (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 3)))) = T + AENT * Z.of_nat (length es)).
{ rewrite !U_SAlu. cbn [zalu_raw].
  change (U Ed (SExt true 32 (SOff 514 0))) with (bv_unsigned (sv_denot Ed (SExt true 32 (SOff 514 0)))).
  rewrite SXn, (U_atom Ed 516 T E516) by (clear - HTB C1; lia).
  rewrite !U_lit by lia.
  change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
  rewrite (ZC (Z.of_nat (length es) * 8)) by (clear - HNB; lia).
  rewrite (ZC (Z.of_nat (length es) * 64)) by (clear - HNB; lia).
  rewrite (ZC (Z.of_nat (length es) * 64 - Z.of_nat (length es) * 8)) by (clear - HNB; lia).
  rewrite (ZC (T + (Z.of_nat (length es) * 64 - Z.of_nat (length es) * 8))) by (clear - HTB HNB C1; lia).
  unfold AENT. clear - HNB. lia. }
assert (HEA0 : U Ed (SAlu ALU_ADD (SAlu ALU_ADD (SOff 516 0)
  (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 6))
                (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 3)))) (SLit 0))
  = T + AENT * Z.of_nat (length es)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HEA, U_lit by lia. rewrite Z.add_0_r.
  apply ZC. unfold AENT. clear - HTB HNB C1. lia. }
psrr_branch_pi_x RUNPR BRR HS.
all: rewrite branch_ne_U in Hc0; unfold U in Hc0; rewrite SXn, SXc in Hc0.
(* the two arms of the `bne`: the table is not full (T <> 0), or it is the empty table (T = 0) the realloc grows *)
+ (* g_nsrc <> g_capsrc: the table is not full, so it exists (T <> 0) and the realloc is not taken *)
  apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
  assert (HTne0 : T <> 0).
  { intros HT0. rewrite HT0 in Hc0. cbn [Z.eqb] in Hc0.
    destruct HREL as [(_ & Hes0 & _) | HR]; [subst es; cbn [length Z.of_nat] in Hc0; lia|].
    destruct HR as (_ & _ & _ & _ & _ & _ & _ & Hin & _). rewrite HT0 in Hin.
    destruct (alx_blocks _ _ _ LAWS ly S _ W mem md 0 ATABLE HAR Hin) as (_ & H4096 & _). lia. }
  rewrite (proj2 (Z.eqb_neq T 0) HTne0) in Hc0, SXc.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK6 : sh_ok SEGS Bx [] Ex (mrestrict Hh (ms_mem msx))) by (apply Forall_nil) end.
  paj_run_tok_xR RUNXR HS HJ3 SHOK6 Bspan.
  { apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U257 in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U248 in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_of0. ra_awr_tac U2d U38d U513d ly fpos F. }
  pres_upd PRES.
  (* ---- __asan_memset (s4, 0, 56): the new entry.  Its 56 bytes are the journal's whole footprint (ra_FP) and
     lie inside the live table block, which gives the intrinsic its destination premises. ---- *)
  assert (HinT2 : In (T, ATABLE) (ablocks B ly S2)) by (rewrite Eab; exact (HTne HTne0)).
  assert (HESZ : 0 < AENT * (Z.of_nat (length es) + 1) <= ATABLE).
  { pose proof (proj1 (HNEW Hpos)) as Hlt4. unfold AENT, ATABLE. clear - Hlt4 HNB. lia. }
  assert (HRQ : ATABLE <= req_size ATABLE) by (unfold req_size, ATABLE; cbn [Z.eqb]; lia).
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md T ATABLE HAR (HTne HTne0)) as (_ & HT4096 & HTceil & _).
  pmkst HS.
  prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3.
  prreg HS (4%bv : bv 5) M4. prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11.
  prreg HS (12%bv : bv 5) M12.
  lazymatch type of M10 with getr ?rg 10 = _ =>
    assert (MA0 : getr rg 10 = w64 (T + AENT * Z.of_nat (length es))) end.
  { rewrite M10. rewrite (ra_entry_addr (ew Ed 516) (ew Ed 514) T (Z.of_nat (length es)) E516 E514)
      by (clear - HTB HNB C1; lia).
    reflexivity. }
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3m.
  destruct HJ3 as (HSTK3 & HXO3 & (memS3 & HJi3 & HAG3) & HOUT3). rewrite !Z.add_0_r in HJi3.
  (* the entry, as a byte range: [d, d + 56) with d = T + AENT * |es|, inside the table block (T, ATABLE) *)
  assert (HEIN : forall a, T + AENT * Z.of_nat (length es) <= a < T + AENT * Z.of_nat (length es) + 56 ->
    T <= a < T + req_size ATABLE).
  { intros a Ha. revert Ha HESZ HRQ HNB. clear. unfold AENT. intros. lia. }
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_intrin_at_xR B PST ARx LAWS R_trans WLE_R OSet (SIGMA WS_asan_memset) AMEMSET W (ms_regs ms3) (ms_mem ms3) RA_STK
      (spZ regs) (ra_FP T es) ly S _ W memS3 md [(0, fpos)] ly S2 _ _ 0 (T + AENT * Z.of_nat (length es)) 0 56 (-128) _
      HJi3).
    - exact MA0.
    - exact M11.
    - exact M12.
    - lia.
    - clear - HTB. unfold AENT. lia.
    - revert HTB HNB C1. clear. unfold AENT. intros. lia.
    - unfold spZ at 1. rewrite M2, U2d. rewrite unsigned_lit_small by (revert Hslo Hshi H47 Hceil Hstk0 C1; clear; unfold spZ; intros; lia). lia.
    - reflexivity.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite M3, OLDd, OLDc, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite M4, OLDd, OLDc, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - exact M1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right; left. split.
        * unfold ra_FP. rewrite (proj2 (Z.eqb_neq T 0) HTne0).
          exists (T + AENT * Z.of_nat (length es), T + AENT * (Z.of_nat (length es) + 1)).
          split; [left; reflexivity|]. cbn [fst snd]. revert Ha. clear. unfold AENT. intros. lia.
        * exists T, ATABLE. split; [exact HinT2 | exact (HEIN a Ha)].
      + pose proof (HEIN a Ha) as Hb. revert Hb HTceil Hslo Hshi H47 Hceil Hstk0 C1 WS. clear. unfold ESTACK. intros. lia.
    - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S2 _ W _ _ T ATABLE);
      [exact HAR3m | exact HinT2 | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia].
    - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S2 _ W _ _ T ATABLE);
      [exact HAR3m | exact HinT2 | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia].
    - intros Hpq. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S2 _ W _ _ T ATABLE);
      [exact HAR3m | exact HinT2 | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia | exact Hpq].
    - exact I. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJi4 & HP4 & Hd10 & Hset & Hfr4 & Hpres4).
  assert (HJ4 : ajournal_gx_xR SEGS B PST ARx R G 0 [] RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [(0, fpos)] ly S2 Hp W mem4 md4 0).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) _ ly S Hp W mem md [(0, fpos)] ly S2 Hp W mem4 md4 0 memS3 HSTK3 HXO3);
    [rewrite !Z.add_0_r; exact HJi4 | exact HAG3 | intros a Ha _; lia]. }
  clear HJi4 HJi3 HAG3.
  pose proof (pres_trans _ _ _ _ PRES (fun a (_ : in_img SEGS a) (H : apresent (w_H W) (ms_mem ms3) a) => Hpres4 a H)) as P.
  clear PRES; rename P into PRES.
  (* ---- back in relay_add after the memset: rebuild the state, keeping all nine regions ---- *)
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly S2 _ W (ms_mem ms3) _ _ _ HAR3m HinT2) as HToff. unfold off_img in HToff.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 _ W (ms_mem ms3) _ T ATABLE 0 fpos HAR3m HinT2 Hfin2) as HTF.
  unfold zdisjoint in HTF. cbn [fst snd] in HTF. change (fs_frame_bytes 0) with 64 in HTF. fold F in HTF.
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR3m) as (Kc4a & Ku4a & Kg4a & Kgu4a).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR4) as (Kc4 & Ku4 & Kg4 & Kgu4).
  rewrite HBgot, HBcell in Kg4a, Kg4. rewrite HBcell in Kc4a, Kc4. rewrite (palf_got_uar B TLF) in Kgu4a, Kgu4.
  (* the entry's bytes, as a range inside the table block and off the image *)
  assert (HED : T <= T + AENT * Z.of_nat (length es) /\ T + AENT * Z.of_nat (length es) + 56 <= T + req_size ATABLE).
  { revert HESZ HRQ HNB. clear. unfold AENT. intros. lia. }
  jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS4.
  match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | | | apply Forall_nil].
    - apply (region_kept_aview Ed (w_H W) (ms_mem ms3) mem4 249 (rg_src RG)); [exact U249 | | exact Hpres4].
      intros a Ha. apply Hfr4;
      [ revert Ha BSR; clear; intros; lia
      | revert Ha BSR HToff HED; clear; intros; lia
      | revert Ha BSR Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ed (w_H W) (ms_mem ms3) mem4 257 (rg_capsrc RG)); [exact U257 | | exact Hpres4].
      intros a Ha. apply Hfr4;
      [ revert Ha BCS; clear; intros; lia
      | revert Ha BCS HToff HED; clear; intros; lia
      | revert Ha BCS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ed (w_H W) (ms_mem ms3) mem4 248 (rg_nsrc RG)); [exact U248 | | exact Hpres4].
      intros a Ha. apply Hfr4;
      [ revert Ha BNS; clear; intros; lia
      | revert Ha BNS HToff HED; clear; intros; lia
      | revert Ha BNS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ed (w_H W) (ms_mem ms3) mem4 38 F); [exact U38d | | exact Hpres4].
      intros a Ha. apply Hfr4;
      [ revert Ha HF4096 HFceil HFhigh C1; clear; intros; lia
      | revert Ha HTF HED; clear; intros; lia
      | revert Ha HF4096 HFceil HFhigh HFimg Hslo Hshi H47 Hceil Hstk0 C1 WS Hes; clear; intros; lia ].
    - apply (region_kept_aview Ed (w_H W) (ms_mem ms3) mem4 2 (spZ regs)); [exact U2d | | exact Hpres4].
      intros a Ha. apply Hfr4;
      [ revert Ha Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha HED HTceil Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha; clear; intros; lia ].
    - apply (region_kept_val_at Ed _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
      [exact U241d | exact (val_mem_of_rdword SEGS _ _ _ _ Kg4a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg4) | lia].
    - apply (region_kept_val_at Ed _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
      [exact U273d | exact (val_mem_of_rdword SEGS _ _ _ _ Kc4a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc4) | lia].
    - apply (region_kept_val_at Ed _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
      [exact U242d | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu4a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu4) | lia].
    - apply (region_kept_val_at Ed _ _ 32 (as_uar_cell B) 4 1);
      [exact U32d | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku4a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku4) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
  remember (havoc Ed 66 (map (getr regs4) CLOB)) as Ee eqn:HEe in HS.
  assert (HEIe : img_env VAL A_LIM Ee) by (rewrite HEe; apply img_env_havoc; [exact HEId | cbv; lia]).
  assert (OLDe : forall m, (m < 66)%nat -> ew Ee m = ew Ed m) by (intros m Hm; rewrite HEe; apply YN3v.ew_havoc_old; exact Hm).
  assert (ABVe : forall m, (82 <= m)%nat -> ew Ee m = ew Ed m) by (intros m Hm; rewrite HEe; apply ew_havoc_above; cbn; lia).
  assert (HAEe : env_agree 32 (Ereg regs ra_extra) Ee) by (rewrite HEe; apply env_agree_havoc_ge; [cbv; lia | exact HAEd]).
  clear HEe.
  (* ---- g_nsrc's region moves to the kept auipc register s8 = A_HI 30 (the store `sw s10,-704(s8)`) ---- *)
  assert (HR30 : VAL 248%nat = VAL 310%nat + -704).
  { pose proof HH30 as X1. pose proof HV7 as X2. change (A_HI 30) with 310%nat in X1. change (A_OBJ 7) with 248%nat in X2.
    revert X1 X2. clear. intros. lia. }
  prebase HS 2%nat 310%nat (-704) HR30.
  (* ---- the entry's address s4 as atom 517: its value, band fact, alias, region and shadow entry ---- *)
  destruct (alx_blocks _ _ _ LAWS ly S2 _ W mem4 md4 T ATABLE HAR4 HinT2) as (HT16 & _ & _ & HTapp & HTpres & _).
  (* this file turns off zify's mod/div handling, so the alignment is shown by hand *)
  assert (HD8 : (T + AENT * Z.of_nat (length es)) mod 8 = 0).
  { pose proof (Z.div_mod T 16 ltac:(lia)) as HT. rewrite HT16, Z.add_0_r in HT. unfold AENT.
    replace (T + 56 * Z.of_nat (length es)) with ((2 * (T / 16) + 7 * Z.of_nat (length es)) * 8)
      by (revert HT; clear; intros; lia).
    apply Z.mod_mul. lia. }
  assert (HDB : 4096 <= T + AENT * Z.of_nat (length es) /\ T + AENT * Z.of_nat (length es) + 56 <= alloc_ceiling /\
                (T + AENT * Z.of_nat (length es)) mod 8 = 0).
  { split; [|split; [|exact HD8]]; revert HT4096 HTceil HED; clear; unfold AENT; intros; lia. }
  pose proof (st_ok_pi_havoc_hi 517 Ee _ _ [Z_to_bv 64 (T + AENT * Z.of_nat (length es))] HS
    ltac:(vm_compute; reflexivity)) as HS5.
  clear HS. rename HS5 into HS.
  remember (havoc Ee 517 [Z_to_bv 64 (T + AENT * Z.of_nat (length es))]) as Ef eqn:HEf in HS.
  assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc_hi; [exact HEIe | cbv; lia]).
  assert (OLDf : forall m, (m < 517)%nat -> ew Ef m = ew Ee m) by (intros m Hm; rewrite HEf; apply YN3v.ew_havoc_old; exact Hm).
  assert (E517 : ew Ef 517 = Z_to_bv 64 (T + AENT * Z.of_nat (length es)))
  by (rewrite HEf; exact (ew_havoc_new _ 517 [Z_to_bv 64 (T + AENT * Z.of_nat (length es))] 0 (Z_to_bv 64 0)
        ltac:(cbn [length]; lia))).
  assert (HAEf : env_agree 32 (Ereg regs ra_extra) Ef) by (rewrite HEf; apply env_agree_havoc_ge; [cbv; lia | exact HAEe]).
  clear HEf.
  assert (C1b : alloc_ceiling < 2 ^ 63) by (revert C1; clear; intros; lia).
  assert (U517 : bv_unsigned (ew Ef 517) = T + AENT * Z.of_nat (length es)).
  { rewrite E517. apply unsigned_lit_small. revert HDB C1b. clear. intros. lia. }
  assert (E514f : ew Ef 514 = Z_to_bv 64 (Z.of_nat (length es))) by (rewrite OLDf, ABVe by lia; exact E514).
  assert (E516f : ew Ef 516 = Z_to_bv 64 T) by (rewrite OLDf, ABVe by lia; exact E516).
  assert (U2f : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf, OLDe by lia; exact U2d).
  assert (U38f : bv_unsigned (ew Ef 38) = F) by (rewrite OLDf, OLDe by lia; exact U38d).
  assert (U513f : bv_unsigned (ew Ef 513) = SB + F / 8) by (rewrite OLDf, ABVe by lia; exact U513d).
  assert (U249f : bv_unsigned (ew Ef 249) = rg_src RG) by (rewrite OLDf, ABVe by lia; exact U249).
  assert (U257f : bv_unsigned (ew Ef 257) = rg_capsrc RG) by (rewrite OLDf, ABVe by lia; exact U257).
  assert (U310f : bv_unsigned (ew Ef 310) = rg_nsrc RG + 704) by (rewrite OLDf, ABVe by lia; exact U310).
  assert (U241f : bv_unsigned (ew Ef 241) = VAL (A_OBJ 0)) by (rewrite OLDf, ABVe by lia; exact U241d).
  assert (U242f : bv_unsigned (ew Ef 242) = VAL (A_OBJ 1)) by (rewrite OLDf, ABVe by lia; exact U242d).
  assert (U273f : bv_unsigned (ew Ef 273) = VAL (A_OBJ 32)) by (rewrite OLDf, ABVe by lia; exact U273d).
  assert (U32f : bv_unsigned (ew Ef 32) = as_uar_cell B) by (rewrite OLDf, OLDe by lia; exact U32d).
  pose proof (st_ok_pi_add_fact Ef _ _ 517 (HPTR 3) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U517; change (2 ^ 3) with 8;
          revert HDB C1; clear; intros; lia)) as HS5.
  clear HS; rename HS5 into HS.
  (* s4's value tree is atom 517 (the alias lets the engine address the entry through s4) *)
  assert (SXnf : bv_unsigned (sv_denot Ef (SExt true 32 (SOff 514 0))) = Z.of_nat (length es)).
  { rewrite U_sext32'. change (bv_unsigned (sv_denot Ef (SOff 514 0))) with (U Ef (SOff 514 0)).
    rewrite (U_atom Ef 514 _ E514f) by (clear - HNB; lia). apply sx32_small. clear - HNB; lia. }
  assert (HAL : sv_denot Ef (SAlu ALU_ADD (SOff 516 0)
      (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 6))
                    (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 3)))) = sv_denot Ef (SOff 517 0)).
  { apply bv_eq.
    lazymatch goal with |- bv_unsigned (sv_denot Ef ?x) = bv_unsigned (sv_denot Ef ?y) =>
      change (U Ef x = U Ef y) end.
    rewrite (U_atom Ef 517 _ E517) by (revert HDB C1b; clear; intros; lia).
    rewrite !U_SAlu. cbn [zalu_raw].
    change (U Ef (SExt true 32 (SOff 514 0))) with (bv_unsigned (sv_denot Ef (SExt true 32 (SOff 514 0)))).
    rewrite SXnf, (U_atom Ef 516 T E516f) by (clear - HTB C1; lia).
    rewrite !U_lit by lia.
    change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
    rewrite (ZC (Z.of_nat (length es) * 8)) by (clear - HNB; lia).
    rewrite (ZC (Z.of_nat (length es) * 64)) by (clear - HNB; lia).
    rewrite (ZC (Z.of_nat (length es) * 64 - Z.of_nat (length es) * 8)) by (clear - HNB; lia).
    rewrite (ZC (T + (Z.of_nat (length es) * 64 - Z.of_nat (length es) * 8))) by (clear - HTB HNB C1; lia).
    unfold AENT. clear - HNB. lia. }
  pose proof (st_ok_pi_add_alias Ef _ _ _ _ HS HAL) as HS5. clear HS; rename HS5 into HS.
  (* the entry's region: extent its 56 bytes, write window its first word (s->fd) *)
  pose proof (st_ok_pi_add_region Ef _ _ ra_ent_region HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok, ra_ent_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U517; split; [revert HDB C1b; clear; intros; lia|]; split; [revert HDB C1b; clear; intros; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS);
      exact (proj1 (HTpres (T + AENT * Z.of_nat (length es) + o) ltac:(revert Ho HED; clear; intros; lia)))
    | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, ra_ent_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U517, U249f, U257f, U310f, U38f, U2f, U241f, U273f, U242f, U32f;
    repeat split;
    first [ solve [revert HToff HED BSR BCS BNS; clear; intros; lia]
          | solve [revert HTF HED; clear; intros; lia]
          | solve [revert HED HTceil Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia]
          | solve [revert HToff HED HgotR HcellR HguR HuR PV0 PV1 PV32; clear; intros; lia]
          | lazymatch goal with |- ?g => idtac "ENT-DISJ" g; fail end ])) as HS5.
  clear HS; rename HS5 into HS. norm_ss HS.
  (* ---- the run 0x82ad0-0x82af8: g_nsrc + 1 stored, the entry's shadow checked (a token: the granule is in the
     live block), s->fd = fd stored, a0 = &g_lock; it stops at the pthread_mutex_unlock call ---- *)
  assert (E33f : ew Ef 33 = Z_to_bv 64 SB) by (rewrite OLDf, OLDe, OLDd, OLDc by lia; exact E33b).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK7 : sh_ok SEGS Bx [mkSHE 517 0 56] Ex (mrestrict Hh (ms_mem msx))) end.
  { unfold sh_ok. constructor; [|constructor].
    eapply shent_ok_of_range.
    - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S2 _ W _ _ T ATABLE (T + AENT * Z.of_nat (length es)) 56);
      [exact HAR4 | exact HinT2 | revert HED; clear; intros; lia | revert HED; clear; intros; lia].
    - unfold Bx. rewrite (U_atom Ef 33 SB E33f) by (unfold SB; lia). reflexivity.
    - rewrite (U_atom Ef 517 _ E517) by (revert HDB C1b; clear; intros; lia). reflexivity.
    - lia.
    - lia.
    - intros x Hx. cbn in Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      revert Hx HTapp HED; clear; intros; lia. }
  (* the rebased g_nsrc region's new base atom 310 needs its band fact, or the token runner's static check
     (cells_safe_b) cannot place its window against the shadow span and turns shadow tokens off *)
  pose proof (st_ok_pi_add_fact Ef _ _ 310 (mkAF 65536 6271680 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U310f, Z.pow_0_r, Z.mod_1_r; revert BNS; clear; intros; lia))
    as HS5.
  clear HS; rename HS5 into HS.
  (* s4 := SOff 517 0 in the symbolic registers (the alias alone does not reach inside the shadow address) *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ef ssx msx 20%bv HS) as Q20 end.
  lazymatch type of Q20 with _ = sv_denot _ ?x => let x' := eval vm_compute in x in change x with x' in Q20 end.
  rewrite HAL in Q20.
  pose proof (ra_set_reg Ef _ _ 20%bv (SOff 517 0) HS Q20 eq_refl) as HS5. clear HS Q20; rename HS5 into HS. norm_ss HS.
  paj_run_tok_xR RUNXR HS HJ4 SHOK7 Bspan.
  { apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ra_ent_region] in Ha. rewrite U517 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold ra_FP. rewrite (proj2 (Z.eqb_neq T 0) HTne0).
        exists (T + AENT * Z.of_nat (length es), T + AENT * (Z.of_nat (length es) + 1)).
        split; [left; reflexivity|]. cbn [fst snd]. revert Ha. clear. unfold AENT. intros. lia.
      - exists T, ATABLE. split; [exact HinT2 | revert Ha HED; clear; intros; lia]. }
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249f in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U257f in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U310f in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_of0. ra_awr_tac U2f U38f U513f ly fpos F. }
  pres_upd PRES.
  (* ---- the lock as the unlock call finds it: held since the lock call (word 4 = 16, words 0 and 8 zero), and kept
     by every step since - two runs, the memset and the run after it, none of whose windows meets g_lock ---- *)
  assert (HWL : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (T + req_size ATABLE <= 65536 \/ 6270976 <= T) /\
                (T <= T + AENT * Z.of_nat (length es) /\ T + AENT * Z.of_nat (length es) + 56 <= T + req_size ATABLE) /\
                (rg_lock RG + 12 <= rg_nsrc RG \/ rg_nsrc RG + 4 <= rg_lock RG) /\
                (rg_lock RG + 12 <= rg_capsrc RG \/ rg_capsrc RG + 4 <= rg_lock RG) /\
                (rg_lock RG + 12 <= rg_src RG \/ rg_src RG + 8 <= rg_lock RG)).
  { split; [exact HWOUT|]. split; [exact HToff|]. split; [exact HED|].
    ra_zsep_pick HSEPG 4%nat 5%nat P45. ra_zsep_pick HSEPG 4%nat 6%nat P46. ra_zsep_pick HSEPG 4%nat 7%nat P47.
    split; [exact P45|]. split; [exact P46|exact P47]. }
  assert (KEEPL : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
    aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha.
    assert (HaL : rg_lock RG <= a < rg_lock RG + 12 /\ 65536 <= rg_lock RG /\ rg_lock RG + 12 <= 6270976)
    by (revert Ha BLK; clear; intros; lia).
    rewrite (aview_kept_out Ef _ (w_H W) _ _ HFr4 a ltac:(revert HaL; clear; intros; lia)
      ltac:(ra_out HaL HWL U2f U38f U513f U249f U257f U310f U517)).
    rewrite (Hfr4 a ltac:(revert HaL; clear; intros; lia) ltac:(revert HaL HWL; clear; intros; lia)
      ltac:(revert HaL Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia)).
    rewrite (aview_kept_out Ed _ (w_H W) _ _ HFr3 a ltac:(revert HaL; clear; intros; lia)
      ltac:(ra_out HaL HWL U2d U38d U513d U249 U257 U248 U248)).
    exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 a ltac:(revert HaL; clear; intros; lia)
      ltac:(ra_out HaL HWL U2d U38d U513d U249 U257 U248 U248)). }
  assert (LK0u : val_mem SEGS (mrestrict (w_H W) (ms_mem ms4)) (rg_lock RG) 4 0).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms1) (ms_mem ms4) (rg_lock RG) 4 0); [|exact LK0].
    intros j Hj. cbn in Hj. rewrite (KEEPL (rg_lock RG + j) ltac:(revert Hj BLK; clear; intros; lia)).
    apply Hfr3; [revert Hj BLK; clear; intros; lia | revert Hj; clear; intros; lia
      | revert Hj BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia]. }
  assert (LK8u : val_mem SEGS (mrestrict (w_H W) (ms_mem ms4)) (rg_lock RG + 8) 4 0).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms1) (ms_mem ms4) (rg_lock RG + 8) 4 0); [|exact LK8].
    intros j Hj. cbn in Hj. rewrite (KEEPL (rg_lock RG + 8 + j) ltac:(revert Hj BLK; clear; intros; lia)).
    apply Hfr3; [revert Hj BLK; clear; intros; lia | revert Hj; clear; intros; lia
      | revert Hj BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia]. }
  assert (LK4u : val_mem SEGS (mrestrict (w_H W) (ms_mem ms4)) (rg_lock RG + 4) 4 16).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms4) (rg_lock RG + 4) 4 16); [|exact HLK3].
    intros j Hj. cbn in Hj. exact (KEEPL (rg_lock RG + 4 + j) ltac:(revert Hj BLK; clear; intros; lia)). }
  (* ---- pthread_mutex_unlock (&g_lock) ---- *)
  pmkst HS.
  prreg HS (1%bv : bv 5) UQRA. prreg HS (2%bv : bv 5) UQSP. prreg HS (3%bv : bv 5) UQGP. prreg HS (4%bv : bv 5) UQTP.
  prreg HS (10%bv : bv 5) UQA0.
  assert (HSPu : spZ (ms_regs ms4) = spZ regs + -128).
  { unfold spZ at 1. rewrite UQSP, U2f.
    rewrite unsigned_lit_small by (revert Hslo Hshi H47 Hceil Hstk0 C1; clear; unfold spZ; intros; lia). lia. }
  assert (UQA0' : getr (ms_regs ms4) 10 = w64 (rg_lock RG)).
  { rewrite UQA0. change 247%nat with (A_OBJ 6).
    rewrite (img_env_atomP Ef (A_OBJ 6) HEIf ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). rewrite HV6. reflexivity. }
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HARu.
  assert (LKVu : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms4) a <> None).
  { intros a Ha. unfold aview.
    destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
    - pose proof (LK0u (Z.to_nat (a - rg_lock RG)) ltac:(revert Ha h1; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert Ha; clear; intros; lia).
      replace (rg_lock RG + (a - rg_lock RG)) with a in X by ring. rewrite X. discriminate.
    - pose proof (LK4u (Z.to_nat (a - (rg_lock RG + 4))) ltac:(revert h1 h2; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert h1; clear; intros; lia).
      replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by ring. rewrite X. discriminate.
    - pose proof (LK8u (Z.to_nat (a - (rg_lock RG + 8))) ltac:(revert Ha h2; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert h2; clear; intros; lia).
      replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by ring. rewrite X. discriminate. }
  assert (HNOWNu : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S2 a).
  { intros a Ha Ho. destruct (HG a (HGin a (ra_lock_in a Ha))) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S2 _ W (ms_mem ms4) _ a HARu Hi) Ho). }
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
      (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
         getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 0)
      W _ _ RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md _ _ _ _ _ _ (-128) _ HG eq_refl HJ4).
    - exact HSPu.
    - reflexivity.
    - first [clear; lia | lia].
    - first [clear; lia | lia].
    - rewrite WS, Hes. clear. lia.
    - rewrite UQGP, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite UQTP, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - exact UQRA.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
      destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
    - intros a Ha _. exact (LKVu a ltac:(revert Ha; clear; intros; lia)).
    - intros a Ha HnG. exfalso. apply HnG. apply HGin. apply ra_lock_in. revert Ha; clear; intros; lia.
    - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
      + exact UQA0'.
      + revert BLK; clear; intros; lia.
      + exact HLA.
      + revert BLK; clear; intros; lia.
      + exact LK0u.
      + exact LK4u.
      + exact LK8u.
      + intros a Ha. split; [exact (LKVu a Ha)|]. rewrite HSPu.
        revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia.
      + intros a Ha. split; [|split].
        * apply GW; [apply ra_lock_in; revert Ha; clear; intros; lia|].
          apply (hidden_not_img SEGS W (Z_to_bv 64 a)). rewrite unsigned_lit_small by (revert Ha BLK; clear; intros; lia).
          exact (proj1 (HG a (HGin a (ra_lock_in a ltac:(revert Ha; clear; intros; lia))))).
        * exact (HNOWNu a ltac:(revert Ha; clear; intros; lia)).
        * rewrite HSPu. revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia.
      + intros a Ha HKx. exact (proj2 (proj2 (HG a (HGin a (ra_lock_in a ltac:(revert Ha; clear; intros; lia))))) (proj1 (proj2 HKx))). }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (HUA0 & HUL5) & Hfr5 & Hpres5).
  pose proof (pres_trans _ _ _ _ PRES (fun a (_ : in_img SEGS a) (H : apresent (w_H W) (ms_mem ms4) a) => Hpres5 a H)) as P.
  clear PRES; rename P into PRES.
  (* ---- back in relay_add, the lock free: rebuild the state, keeping all ten regions ---- *)
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR5.
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARu) as (Kc5a & Ku5a & Kg5a & Kgu5a).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR5) as (Kc5 & Ku5 & Kg5 & Kgu5).
  rewrite HBgot, HBcell in Kg5a, Kg5. rewrite HBcell in Kc5a, Kc5. rewrite (palf_got_uar B TLF) in Kgu5a, Kgu5.
  jafter_call_keep_pi HS 82%nat regs5 (mrestrict (w_H W) mem5) HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat HS6.
  match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | | | | apply Forall_nil].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 517 (T + AENT * Z.of_nat (length es))); [exact U517 | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha HDB C1b; clear; intros; lia
      | revert Ha HWL BLK; clear; intros; lia
      | revert Ha HDB Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 249 (rg_src RG)); [exact U249f | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BSR; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BSR Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 257 (rg_capsrc RG)); [exact U257f | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BCS; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BCS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 310 (rg_nsrc RG + 704)); [exact U310f | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BNS; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BNS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 38 F); [exact U38f | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha HF4096 HFceil HFhigh C1; clear; intros; lia
      | revert Ha HWL BLK; clear; intros; lia
      | revert Ha HF4096 HFceil HFhigh HFimg Hslo Hshi H47 Hceil Hstk0 C1 WS Hes; clear; intros; lia ].
    - apply (region_kept_aview Ef (w_H W) (ms_mem ms4) mem5 2 (spZ regs)); [exact U2f | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha; clear; intros; lia ].
    - apply (region_kept_val_at Ef _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
      [exact U241f | exact (val_mem_of_rdword SEGS _ _ _ _ Kg5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg5) | lia].
    - apply (region_kept_val_at Ef _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
      [exact U273f | exact (val_mem_of_rdword SEGS _ _ _ _ Kc5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc5) | lia].
    - apply (region_kept_val_at Ef _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
      [exact U242f | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu5) | lia].
    - apply (region_kept_val_at Ef _ _ 32 (as_uar_cell B) 4 1);
      [exact U32f | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku5a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku5) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
  remember (havoc Ef 82 (map (getr regs5) CLOB)) as Eg eqn:HEg in HS.
  assert (HEIg : img_env VAL A_LIM Eg) by (rewrite HEg; apply img_env_havoc; [exact HEIf | cbv; lia]).
  assert (OLDg : forall m, (m < 82)%nat -> ew Eg m = ew Ef m) by (intros m Hm; rewrite HEg; apply YN3v.ew_havoc_old; exact Hm).
  assert (ABVg : forall m, (98 <= m)%nat -> ew Eg m = ew Ef m) by (intros m Hm; rewrite HEg; apply ew_havoc_above; cbn; lia).
  assert (HAEg : env_agree 32 (Ereg regs ra_extra) Eg) by (rewrite HEg; apply env_agree_havoc_ge; [cbv; lia | exact HAEf]).
  clear HEg.
  (* ---- g_wake[1] at the bltz: -1 since the entry (awake_at), kept by every step - relay_add reads it, never
     writes it: the entry run, the fake-frame seat (raw clause: an image byte off the owned statics, HWKI / HWKO),
     two plain runs, the lock, two token runs, the memset, a token run and the unlock ---- *)
  pose proof (proj1 (Forall_forall _ _) HIG (rg_wake RG + 4, 4) ltac:(do 4 right; left; reflexivity)) as BWK.
  cbn [fst snd] in BWK.
  assert (HWK : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (T + req_size ATABLE <= 65536 \/ 6270976 <= T) /\
                (T <= T + AENT * Z.of_nat (length es) /\ T + AENT * Z.of_nat (length es) + 56 <= T + req_size ATABLE) /\
                (rg_lock RG + 12 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_lock RG) /\
                (rg_nsrc RG + 4 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_nsrc RG) /\
                (rg_capsrc RG + 4 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_capsrc RG) /\
                (rg_src RG + 8 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_src RG)).
  { split; [exact HWOUT|]. split; [exact HToff|]. split; [exact HED|].
    ra_zsep_pick HSEPG 4%nat 9%nat Q1. ra_zsep_pick HSEPG 5%nat 9%nat Q2.
    ra_zsep_pick HSEPG 6%nat 9%nat Q3. ra_zsep_pick HSEPG 7%nat 9%nat Q4.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|exact Q4]. }
  assert (NOWK : forall ly0 S0 Hq0 W0 m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 ->
    forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> ~ aowned B ly0 S0 a).
  { intros ly0 S0 Hq0 W0 m0 md0 HA a Ha Ho.
    pose proof (HWKI (a - (rg_wake RG + 4)) ltac:(revert Ha; clear; intros; lia)) as Hi.
    pose proof (HWKO (a - (rg_wake RG + 4)) ltac:(revert Ha; clear; intros; lia)) as Hno.
    replace (rg_wake RG + 4 + (a - (rg_wake RG + 4))) with a in Hi, Hno by ring.
    exact (Hno (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HA Hi) Ho)). }
  assert (WKC : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
    aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Ha.
    assert (HaW : rg_wake RG + 4 <= a < rg_wake RG + 8 /\ 65536 <= rg_wake RG + 4 /\ rg_wake RG + 4 + 4 <= 6270976)
    by (revert Ha BWK; clear; intros; lia).
    assert (HW64 : 0 <= a < 2 ^ 64) by (revert HaW; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= a < spZ regs + -128))
    by (revert HaW Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia).
    etransitivity; [exact (Hfr5 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ef _ (w_H W) _ _ HFr4 a HW64
      ltac:(ra_out HaW HWK U2f U38f U513f U249f U257f U310f U517))|].
    etransitivity; [exact (Hfr4 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr3 a HW64
      ltac:(ra_out HaW HWK U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 a HW64
      ltac:(ra_out HaW HWK U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (Hfr3 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 a HW64
      ltac:(ra_out HaW HWK U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 a HW64
      ltac:(ra_out HaW HWK U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (HRAW a HW64 (NOWK _ _ _ _ _ _ HARa a Ha) (NOWK _ _ _ _ _ _ HARb a Ha) HWCW)|].
    exact (aview_kept_out E _ (w_H W) _ _ HFr a HW64 ltac:(ra_out HaW HWK Usp Usp Usp Usp Usp Usp Usp)). }
  assert (WK5 : val_mem SEGS (mrestrict (w_H W) mem5) (rg_wake RG + 4) 4 (2 ^ 32 - 1)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem5 (rg_wake RG + 4) 4 (2 ^ 32 - 1)); [|exact HWAKE].
    intros k Hk. cbn in Hk. exact (WKC (rg_wake RG + 4 + k) ltac:(revert Hk; clear; intros; lia)). }
  (* ---- the regions for the rest: the entry's and the globals' windows closed (no more stores to them; a plain
     run writes only awr bytes), the fake frame's window opened again (the calls kept it read-only) ---- *)
  assert (U2g : bv_unsigned (ew Eg 2) = spZ regs) by (rewrite OLDg by lia; exact U2f).
  assert (U38g : bv_unsigned (ew Eg 38) = F) by (rewrite OLDg by lia; exact U38f).
  assert (U513g : bv_unsigned (ew Eg 513) = SB + F / 8) by (rewrite ABVg by lia; exact U513f).
  assert (U512g : bv_unsigned (ew Eg 512) = FL) by (rewrite ABVg, OLDf, ABVe, OLDd, ABVc by lia; exact U512).
  assert (U517g : bv_unsigned (ew Eg 517) = T + AENT * Z.of_nat (length es)) by (rewrite ABVg by lia; exact U517).
  assert (U249g : bv_unsigned (ew Eg 249) = rg_src RG) by (rewrite ABVg by lia; exact U249f).
  assert (U257g : bv_unsigned (ew Eg 257) = rg_capsrc RG) by (rewrite ABVg by lia; exact U257f).
  assert (U310g : bv_unsigned (ew Eg 310) = rg_nsrc RG + 704) by (rewrite ABVg by lia; exact U310f).
  assert (U241g : bv_unsigned (ew Eg 241) = VAL (A_OBJ 0)) by (rewrite ABVg by lia; exact U241f).
  assert (U242g : bv_unsigned (ew Eg 242) = VAL (A_OBJ 1)) by (rewrite ABVg by lia; exact U242f).
  assert (U273g : bv_unsigned (ew Eg 273) = VAL (A_OBJ 32)) by (rewrite ABVg by lia; exact U273f).
  assert (U32g : bv_unsigned (ew Eg 32) = as_uar_cell B) by (rewrite OLDg by lia; exact U32f).
  ra_reshape HS 0%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 1%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 2%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 3%nat (-704) (-704) ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR5 Hfin2) as (_ & _ & HFpres5 & HFSpres5).
  change (fs_frame_bytes 0) with 64 in HFpres5, HFSpres5. change (64 / 8) with 8 in HFSpres5.
  fold F in HFpres5, HFSpres5.
  ra_reshape HS 4%nat 0 64 ltac:(intros o Ho; cbn [base_val]; rewrite U38g; apply (apresent_writable SEGS);
    exact (proj1 (HFpres5 (F + o) ltac:(revert Ho; clear; intros; lia)))).
  (* the fake frame's shadow, writable again (the release poisons it), no chunks *)
  pose proof (st_ok_pi_add_region Eg _ _ (fshadow_region 513 0 0 8 []) HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok, fshadow_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    change (fs_frame_bytes 0 / 8) with 8; rewrite U513g;
    split; [revert HF8lo HF8hi; clear; unfold SB; intros; lia|]; split; [revert HF8lo HF8hi; clear; unfold SB; intros; lia|];
    split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres5; rewrite <- SB_SHADOW_OFF in HFSpres5;
    apply (proj1 (HFSpres5 o ltac:(revert Ho; clear; intros; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0 / 8) with 8;
    rewrite U513g, U517g, U249g, U257g, U310g, U38g, U2g, U241g, U273g, U242g, U32g;
    repeat split;
    first [ solve [revert HTapp HED HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia]
          | solve [revert BSR BCS BNS HF8lo; clear; unfold SB; intros; lia]
          | solve [revert HFapp HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia]
          | solve [revert Hslo Hshi H47 Hceil Hstk0 C1 WS HF8hi; clear; unfold SB; intros; lia]
          | solve [revert HgotR HcellR HguR HuR PV0 PV1 PV32 HF8lo; clear; unfold SB; intros; lia]
          | lazymatch goal with |- ?g => idtac "SH-DISJ" g; fail end ])) as HS6.
  clear HS; rename HS6 into HS. norm_ss HS.
  (* g_wake[1], read-only, holding 2^32 - 1 *)
  assert (U245g : bv_unsigned (ew Eg 245) = rg_wake RG + 4).
  { change 245%nat with (A_OBJ 4). rewrite <- HV4. exact (HEIg (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). }
  pose proof (st_ok_pi_add_region Eg _ _ (YP09.mkRegion (Some 245%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit (2 ^ 32 - 1)))])
    HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U245g; split; [revert BWK; clear; intros; lia|]; split; [revert BWK; clear; intros; lia|]; split;
    [ intros o Ho; exfalso; revert Ho; clear; intros; lia
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Eg _ (rg_wake RG + 4) 0 4 (SLit (2 ^ 32 - 1)) (2 ^ 32 - 1));
      [ reflexivity | clear; zside | clear; zside | rewrite Z.add_0_r; exact WK5 ] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U245g, U513g, U517g, U249g, U257g, U310g, U38g, U2g, U241g, U273g, U242g, U32g;
    ra_zsep_pick HSEPG 0%nat 9%nat W0; ra_zsep_pick HSEPG 1%nat 9%nat W1; ra_zsep_pick HSEPG 2%nat 9%nat W2;
    ra_zsep_pick HSEPG 3%nat 9%nat W3;
    repeat split;
    first [ solve [revert HWK BWK; clear; intros; lia]
          | solve [revert BWK HF8lo; clear; unfold SB; intros; lia]
          | solve [revert W0; clear; intros; lia] | solve [revert W1; clear; intros; lia]
          | solve [revert W2; clear; intros; lia] | solve [revert W3; clear; intros; lia]
          | lazymatch goal with |- ?g => idtac "WK-DISJ" g; fail end ])) as HS6.
  clear HS; rename HS6 into HS. norm_ss HS.
  (* ---- 0x82afc-0x82b10, a plain run on the inner journal: unpoison the local c (shadow byte 4 := 1), c = 0,
     read g_wake[1]; it stops at `bltz a0` ---- *)
  destruct HJ5 as (HSTK5 & HXO5 & (memS5 & HJi5 & HAG5) & HOUT5). rewrite !Z.add_0_r in HJi5.
  paj_run_sh_x RUNPR HS HJi5.
  { intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      lazymatch type of Hr with
      | context [ew _ 2] => rewrite U2g in Hr; left; revert Hr; clear; unfold RA_STK, ASTACK, RA_FRAME; intros; lia
      | context [ew _ 38] => rewrite U38g in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd];
        revert Hr; clear; intros; lia
      | context [ew _ 513] => rewrite U513g in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
        right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
        revert Hr; clear; intros; lia
      | _ => exfalso; revert Hr; clear; intros; lia
      end
    | ]).
    destruct Hin. }
  pres_upd PRES.
  (* the run went on through `bltz` (taken: g_wake[1] = -1 is known), the retired magic, `beqz s2` (s2 = F) and the
     shadow poison, and stops at the flag store `sb zero,0(a0)`, a0 = FL: seat the flag byte, then the release *)
  lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
  destruct (FFL _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (HFLp5 & HFLo5 & (HFLapp5 & HFLimg5) & (HFL40965 & HFLz5 & HFLc5)) end.
  lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
  destruct (alx_frames _ _ _ LAWS _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (_ & _ & HFpres6 & HFSpres6) end.
  change (fs_frame_bytes 0) with 64 in HFLp5, HFLo5, HFLapp5, HFLimg5, HFL40965, HFLz5, HFLc5, HFpres6, HFSpres6.
  change (64 / 8) with 8 in HFSpres6. fold F FL in HFLp5, HFLo5, HFLapp5, HFLimg5, HFL40965, HFLz5, HFLc5, HFpres6, HFSpres6.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U512g; split; [revert HFL40965 HFLc5 C1; clear; intros; lia|]; split; [revert HFL40965 HFLc5 C1; clear; intros; lia|];
    split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by (revert Ho; clear; intros; lia); exact HFLp5)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U512g, U245g, U513g, U517g, U249g, U257g, U310g, U38g, U2g, U241g, U273g, U242g, U32g;
    repeat split;
    first [ solve [revert HFL40965 HFLz5 HFLc5 BSR BCS BNS BWK HgotR HcellR HguR HuR PV0 PV1 PV32
                   Hslo Hshi H47 Hceil Hstk0 C1 WS HF8lo HF8hi HFq HF8 HFceil; clear; unfold zone2, off_img, SB in *; intros; lia]
          | lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
              let Hlt := fresh in let Hge := fresh in let Hlt2 := fresh in let Hge2 := fresh in
              destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; revert Hlt; clear; intros; lia|];
              destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; revert Hge2; clear; intros; lia];
              first [ exact (proj2 (HFpres6 FL ltac:(revert Hge Hlt2; clear; intros; lia)) HFLo5)
                    | exact (proj2 (HTpres FL ltac:(revert Hge Hlt2 HED; clear; intros; lia)) HFLo5) ] end
          | lazymatch goal with |- ?g => idtac "FLAGGOAL" g; fail end ])) as HS6 end.
  clear HS; rename HS6 into HS. norm_ss HS.
  (* ---- the flag store (the fake frame released: stack_free_state), the epilogue, to the ret ---- *)
  paj_run_flag_sh_x RUNFR HS HJi5.
  { first [clear; lia | lia]. }
  { intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. change (flag_addr ly 0 fpos) with FL.
    repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      lazymatch type of Hr with
      | context [ew _ 2] => rewrite U2g in Hr; left; left; revert Hr; clear; unfold RA_STK, ASTACK, RA_FRAME; intros; lia
      | context [ew _ 512] => rewrite U512g in Hr; right; revert Hr; clear; intros; lia
      | context [ew _ 38] => rewrite U38g in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd];
        revert Hr; clear; intros; lia
      | context [ew _ 513] => rewrite U513g in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
        right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
        revert Hr; clear; intros; lia
      | _ => exfalso; revert Hr; clear; intros; lia
      end
    | ]).
    destruct Hin. }
  { intros msr HSr. change (flag_addr ly 0 fpos) with FL.
    lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512g
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
    rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
  pres_upd PRES.
  (* ---- what the last two runs (the release and the flag store) keep: every byte but the frame, the fake frame,
     its shadow and its flag ---- *)
  assert (KEND : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> ~ (F <= a < F + 64) ->
    ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL -> aview SEGS (w_H W) (ms_mem ms6) a = aview SEGS (w_H W) mem5 a).
  { intros a Ha N1 N2 N3 N4.
    assert (NW : forall E0 rs, (forall r, In r rs -> ~ (base_val E0 (YP09.r_base r) + YP09.r_wlo r <= a < base_val E0 (YP09.r_base r) + YP09.r_whi r)) ->
      ~ in_wrange E0 rs a) by (intros E0 rs Hn (r & Hin & Hr); exact (Hn r Hin Hr)).
    rewrite (aview_kept_out Eg _ (w_H W) _ _ HFr6 a Ha).
    2:{ apply NW. intros r Hin.
        lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
        cbn [In] in Hin.
        repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2g, ?U38g, ?U513g, ?U512g;
          revert N1 N2 N3 N4; clear; intros; lia | ]).
        destruct Hin. }
    exact (aview_kept_out Eg _ (w_H W) _ _ HFr5 a Ha ltac:(apply NW; intros r Hin;
        lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
        cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2g, ?U38g, ?U513g, ?U512g;
          revert N1 N2 N3 N4; clear; intros; lia | ]);
        destruct Hin)). }
  (* ---- the values the regions hold at the ret: g_src = T, g_capsrc = 16, g_nsrc = |es| + 1, s->fd = fd ---- *)
  assert (U516g : ew Eg 516 = Z_to_bv 64 T) by (rewrite ABVg, OLDf, ABVe by lia; exact E516).
  assert (U515g : ew Eg 515 = Z_to_bv 64 16).
  { rewrite ABVg, OLDf, ABVe by lia. rewrite E515, (proj2 (Z.eqb_neq T 0) HTne0). reflexivity. }
  assert (U514g : ew Eg 514 = Z_to_bv 64 (Z.of_nat (length es))) by (rewrite ABVg, OLDf, ABVe by lia; exact E514).
  assert (U10g : ew Eg 10 = Z_to_bv 64 fd)
  by (rewrite OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
  assert (SXng : bv_unsigned (sv_denot Eg (SExt true 32 (SOff 514 0))) = Z.of_nat (length es)).
  { rewrite U_sext32'. change (bv_unsigned (sv_denot Eg (SOff 514 0))) with (U Eg (SOff 514 0)).
    rewrite (U_atom Eg 514 _ U514g) by (clear - HNB; lia). apply sx32_small. clear - HNB; lia. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth Ex ssx msx 3 _ HS eq_refl) as RQ3;
    pose proof (st_ok_pi_region_nth Ex ssx msx 4 _ HS eq_refl) as RQ4;
    pose proof (st_ok_pi_region_nth Ex ssx msx 5 _ HS eq_refl) as RQ5;
    pose proof (st_ok_pi_region_nth Ex ssx msx 6 _ HS eq_refl) as RQ6 end.
  lazymatch type of RQ4 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eg m n (rg_src RG) cs lo hi wlo whi 0 8%N (SOff 516 0) T RQ4 U249g ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite U516g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(revert HTB C1; clear; intros; cbn; lia) ltac:(cbn; lia)) as VSRC end.
  lazymatch type of RQ5 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eg m n (rg_capsrc RG) cs lo hi wlo whi 0 4%N (SOff 515 0) 16 RQ5 U257g ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite U515g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as VCAP end.
  lazymatch type of RQ3 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eg m n (T + AENT * Z.of_nat (length es)) cs lo hi wlo whi 0 4%N (SOff 10 0) fd RQ3 U517g
      ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite U10g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(revert Hpos Rfd; clear; intros; cbn; lia) ltac:(cbn; lia)) as VENT end.
  assert (HNS1 : sv_denot Eg (SAlu ALU_ADD (SExt true 32 (SOff 514 0)) (SLit 1)) = Z_to_bv 64 (Z.of_nat (length es) + 1)).
  { apply bv_eq.
    lazymatch goal with |- bv_unsigned (sv_denot Eg ?x) = _ => change (U Eg x = bv_unsigned (Z_to_bv 64 (Z.of_nat (length es) + 1))) end.
    rewrite U_SAlu. cbn [zalu_raw].
    change (U Eg (SExt true 32 (SOff 514 0))) with (bv_unsigned (sv_denot Eg (SExt true 32 (SOff 514 0)))).
    rewrite SXng, U_lit by lia. rewrite (ZC (Z.of_nat (length es) + 1)) by (clear - HNB; lia).
    rewrite unsigned_lit_small by (clear - HNB; lia). reflexivity. }
  lazymatch type of RQ6 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eg m n (rg_nsrc RG + 704) cs lo hi wlo whi (-704) 4%N
      (SAlu ALU_ADD (SExt true 32 (SOff 514 0)) (SLit 1)) (Z.of_nat (length es) + 1) RQ6 U310g ltac:(left; reflexivity)
      HNS1 ltac:(revert HNB; clear; intros; cbn; lia) ltac:(cbn; lia)) as VNS end.
  rewrite Z.add_0_r in VSRC, VCAP, VENT. replace (rg_nsrc RG + 704 + -704) with (rg_nsrc RG) in VNS by ring.
  (* ---- facts for ra_post.  (1) errno's four bytes, kept from the entry to the ret (the g_wake chain, at errno) ---- *)
  pose proof (proj1 (Forall_forall _ _) HIG (as_errno B, 4) ltac:(do 5 right; left; reflexivity)) as BE2.
  cbn [fst snd] in BE2.
  assert (HWE2 : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                 (T + req_size ATABLE <= 65536 \/ 6270976 <= T) /\
                 (T <= T + AENT * Z.of_nat (length es) /\ T + AENT * Z.of_nat (length es) + 56 <= T + req_size ATABLE) /\
                 (rg_lock RG + 12 <= as_errno B \/ as_errno B + 4 <= rg_lock RG) /\
                 (rg_nsrc RG + 4 <= as_errno B \/ as_errno B + 4 <= rg_nsrc RG) /\
                 (rg_capsrc RG + 4 <= as_errno B \/ as_errno B + 4 <= rg_capsrc RG) /\
                 (rg_src RG + 8 <= as_errno B \/ as_errno B + 4 <= rg_src RG)).
  { split; [exact HWOUT|]. split; [exact HToff|]. split; [exact HED|].
    ra_zsep_pick HSEPG 4%nat 8%nat Q1. ra_zsep_pick HSEPG 5%nat 8%nat Q2.
    ra_zsep_pick HSEPG 6%nat 8%nat Q3. ra_zsep_pick HSEPG 7%nat 8%nat Q4.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|exact Q4]. }
  assert (ERC : forall i, 0 <= i < 4 ->
    aview SEGS (w_H W) (ms_mem ms6) (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
  { intros i Hi.
    assert (HaW : as_errno B <= as_errno B + i < as_errno B + 4 /\ 65536 <= as_errno B /\ as_errno B + 4 <= 6270976)
    by (revert Hi BE2; clear; intros; lia).
    assert (HW64 : 0 <= as_errno B + i < 2 ^ 64) by (revert HaW; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= as_errno B + i < spZ regs + -128))
    by (revert HaW Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia).
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + i) ltac:(clear - Hi; lia)) as HaI.
    etransitivity.
    { apply KEND; [exact HW64 | revert HaW HWOUT; clear; intros; lia | revert HaW HFimg; clear; intros; lia
                  | revert HaW HWOUT; clear; intros; lia | intros Heq; apply HFLimg5; rewrite <- Heq; exact HaI]. }
    etransitivity; [exact (Hfr5 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ef _ (w_H W) _ _ HFr4 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2f U38f U513f U249f U257f U310f U517))|].
    etransitivity; [exact (Hfr4 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr3 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (Hfr3 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (HRAW (as_errno B + i) HW64
      (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARa HEO i Hi)
      (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARb HEO i Hi) HWCW)|].
    exact (aview_kept_out E _ (w_H W) _ _ HFr (as_errno B + i) HW64 ltac:(ra_out HaW HWE2 Usp Usp Usp Usp Usp Usp Usp)). }
  idtac "A1-ERRNO".
  (* (2) the lock: words 0 and 8 from the unlock call's entry (LK0u / LK8u), word 4 from its post (HUL5) *)
  assert (LKEND : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
    aview SEGS (w_H W) (ms_mem ms6) a = aview SEGS (w_H W) mem5 a).
  { intros a Ha.
    assert (HaI : in_img SEGS a) by exact (proj1 (HG a (HGin a (ra_lock_in a Ha)))).
    apply KEND; [revert Ha BLK; clear; intros; lia | revert Ha BLK HWOUT; clear; intros; lia
                | revert Ha BLK HFimg; clear; intros; lia | revert Ha BLK HWOUT; clear; intros; lia
                | intros Heq; apply HFLimg5; rewrite <- Heq; exact HaI]. }
  assert (LKU : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) (ms_mem ms4) a).
  { intros a Ha Hn. apply (Hfr5 a ltac:(revert Ha BLK; clear; intros; lia) Hn).
    revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia. }
  assert (LKF : alock_at RG W (ms_mem ms6) false).
  { unfold alock_at. split; [|split; [|split]].
    - apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms4) (ms_mem ms6) (rg_lock RG) 4 0); [|exact LK0u].
      intros j Hj. cbn in Hj. rewrite (LKEND (rg_lock RG + j) ltac:(revert Hj; clear; intros; lia)).
      exact (LKU (rg_lock RG + j) ltac:(revert Hj; clear; intros; lia) ltac:(revert Hj; clear; intros; lia)).
    - apply (val_mem_kept SEGS (w_H W) (w_H W) mem5 (ms_mem ms6) (rg_lock RG + 4) 4 0); [|exact HUL5].
      intros j Hj. cbn in Hj. exact (LKEND (rg_lock RG + 4 + j) ltac:(revert Hj; clear; intros; lia)).
    - apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms4) (ms_mem ms6) (rg_lock RG + 8) 4 0); [|exact LK8u].
      intros j Hj. cbn in Hj. rewrite (LKEND (rg_lock RG + 8 + j) ltac:(revert Hj; clear; intros; lia)).
      exact (LKU (rg_lock RG + 8 + j) ltac:(revert Hj; clear; intros; lia) ltac:(revert Hj; clear; intros; lia)).
    - intros i Hi. unfold arm. apply GW; [apply ra_lock_in; lia|].
      apply (hidden_not_img SEGS). rewrite unsigned_lit_small.
      + exact (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia))))).
      + pose proof (pa_segs_low (rg_lock RG + i) (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia)))))).
        unfold kLowMemEnd in *. lia. }
  idtac "A1-LOCK".
  (* (3) heap bytes outside the new entry: kept by the journal (from memS5) and by G-agreement (memS5 = mem off
     G; a block byte is no image byte, every G byte is one) *)
  assert (HEAPK : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
    ~ inFP (ra_FP T es) (p + i) -> aview SEGS (w_H W) (ms_mem ms6) (p + i) = aview SEGS (w_H W) mem (p + i)).
  { intros p n i Hin Hi Hnf.
    assert (EabF6 : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
    by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    pose proof HJi5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _).
    rewrite (Hblk p n i Hin ltac:(rewrite EabF6; exact Hin) Hi Hnf).
    idtac "HK1".
    apply (aview_gagree SEGS G (w_H W) mem memS5 (p + i) HAG5).
    idtac "HK2".
    destruct (alx_blocks _ _ _ LAWS ly S _ W mem md p n HAR Hin) as (_ & Hp4096 & Hpceil & _).
    assert (Hpi : 0 <= p + i < 2 ^ 64) by (revert Hi Hp4096 Hpceil C1; clear; intros; lia).
    rewrite (unsigned_lit_small (p + i) Hpi).
    idtac "HK3".
    apply inGb_false. intros HGi.
    idtac "HK4".
    destruct (alx_client_img _ _ _ LAWS ly S _ W mem md (p + i) HAR) as (_ & HNI).
    { left. exists p, n. split; [exact Hin | revert Hi; clear; intros; lia]. }
    idtac "HK5".
    exact (HNI (proj1 (HG (p + i) HGi))). }
  idtac "A1-HEAP".
  (* (4) the new entry: s->fd = fd (the region, VENT) and its 52 other bytes zero since the memset, kept by the last
     four steps (the run to the unlock - its entry window is s->fd only -, the unlock, the release, the flag store) *)
  assert (HTSH : T + req_size ATABLE <= SB + F / 8 \/ SB + F / 8 + 8 <= T)
  by (revert HTapp HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia).
  assert (HTST : T + req_size ATABLE + 16512 <= spZ regs)
  by (revert HTceil Hslo Hceil Hstk0 WS; clear; intros; lia).
  assert (HZB : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (T + req_size ATABLE <= 65536 \/ 6270976 <= T) /\ (T + req_size ATABLE <= F \/ F + 64 <= T) /\
                (T + req_size ATABLE <= SB + F / 8 \/ SB + F / 8 + 8 <= T) /\ T + req_size ATABLE + 16512 <= spZ regs /\
                65536 <= rg_lock RG /\ rg_lock RG + 12 <= 6270976 /\
                65536 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= 6270976 /\ 65536 <= rg_capsrc RG /\ rg_capsrc RG + 4 <= 6270976 /\
                65536 <= rg_src RG /\ rg_src RG + 8 <= 6270976).
  { split; [exact HWOUT|]. split; [exact HToff|]. split; [exact HTF|]. split; [exact HTSH|]. split; [exact HTST|].
    revert BLK BNS BCS BSR; clear; intros; lia. }
  assert (ZER : forall j, 0 <= j < 52 ->
    aview SEGS (w_H W) (ms_mem ms6) (T + AENT * Z.of_nat (length es) + 4 + j) = Some 0).
  { intros j Hj.
    assert (HaZ : T + AENT * Z.of_nat (length es) + 4 <= T + AENT * Z.of_nat (length es) + 4 + j <
                  T + AENT * Z.of_nat (length es) + 56 /\ T <= T + AENT * Z.of_nat (length es) /\
                  T + AENT * Z.of_nat (length es) + 56 <= T + req_size ATABLE)
    by (revert Hj HED; clear; intros; lia).
    assert (HW64 : 0 <= T + AENT * Z.of_nat (length es) + 4 + j < 2 ^ 64) by (revert HaZ HDB C1b; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= T + AENT * Z.of_nat (length es) + 4 + j < spZ regs + -128))
    by (revert HaZ HZB; clear; unfold ESTACK; intros; lia).
    etransitivity.
    { apply KEND; [exact HW64 | revert HaZ HZB; clear; intros; lia | revert HaZ HZB; clear; intros; lia
                  | revert HaZ HZB; clear; intros; lia
                  | intros Heq; exact (proj2 (HTpres FL ltac:(rewrite <- Heq; revert HaZ; clear; intros; lia)) HFLo5) ]. }
    etransitivity; [exact (Hfr5 _ HW64 ltac:(revert HaZ HZB; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ef _ (w_H W) _ _ HFr4 _ HW64
      ltac:(ra_out HaZ HZB U2f U38f U513f U249f U257f U310f U517))|].
    replace (T + AENT * Z.of_nat (length es) + 4 + j) with (T + AENT * Z.of_nat (length es) + (4 + j)) by ring.
    rewrite (Hset (4 + j) ltac:(revert Hj; clear; intros; lia)). reflexivity. }
  idtac "A1-ZER".
  assert (GNEW : garr8 SEGS (arm W (ms_mem ms6)) (T + AENT * Z.of_nat (length es)) (bzs (entry_bytes (ra_new fd)))).
  { apply (ra_new_entry_garr8 W (ms_mem ms6) (T + AENT * Z.of_nat (length es)) fd).
    - split; [exact Hpos | exact (proj2 Rfd)].
    - exact VENT.
    - exact ZER. }
  idtac "A1-GNEW".
  (* (5) the end state: the table block live and present; the globals writable *)
  assert (EabF : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
  by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  pose proof (proj1 HJi5) as HAR6.
  assert (HinT6 : In (T, ATABLE) (ablocks B ly (stack_free_state 0 fpos S2))) by (rewrite EabF; exact (HTne HTne0)).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ T ATABLE HAR6 HinT6) as (_ & _ & _ & _ & HTpres6 & _).
  assert (GWany : forall m a, inG (RA_G RG) a -> writable_at SEGS (mrestrict (w_H W) m) a).
  { intros m a Ha. apply GW; [exact Ha|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small.
    - exact (proj1 (HG _ (HGin _ Ha))).
    - pose proof (pa_segs_low a (proj1 (HG _ (HGin _ Ha)))). unfold kLowMemEnd in *. lia. }
  (* ---- the return ---- *)
  prreg HS (10%bv : bv 5) Rr10. prreg HS (1%bv : bv 5) Rr1.
  idtac "A1-RR10"; lazymatch type of Rr10 with ?t => idtac t end.
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold ra_post_xR.
  lazymatch type of HJi5 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Hpx _ _ _ ?kx =>
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyx, Sx, Hpx, r, m, d, kx end end.
  split; [cbn [ms_regs]; rewrite Rr1, OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
  split.
  { cbn [ms_mem]. eapply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md []).
    all: [> lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs); exact HJi5 | exact HAG5
         | intros a Ha; lia]. }
  split. { eapply (aregs_preserved_of_st_ok SEGS _ Eg _ _ regs ra_extra HS); [exact HAEg | vm_compute; reflexivity]. }
  split. { intros a Hi _ _ Ha. exact (PRES a Hi Ha). }
  split. { pose proof HJi5 as (_ & _ & _ & _ & _ & Hfr' & _). cbn [app] in Hfr'. exact Hfr'. }
  split.
  { assert (MOseat : mo_le MT S S2 0) by (rewrite ES2; exact (MO_FR S fS2)).
    assert (MOrel : mo_le MT S2 (stack_free_state 0 fpos S2) 0) by (unfold stack_free_state; exact (MO_FR S2 _)).
    pose proof (mle_station MT S S2 (stack_free_state 0 fpos S2) 0 0 MLAW MOseat MOrel) as MOsr. rewrite Z.add_0_r in MOsr.
    apply (mle_weaken MT S _ 0 (ra_cost MT T) MLAW MOsr). unfold ra_cost.
    rewrite (proj2 (Z.eqb_neq T 0) HTne0). lia. }
  split.
  { (* the room: no allocator call on this arm (RMM), then the fake frame's release (RPF) *)
    unfold stack_free_state. apply RPF. exact (RMM S2 kr _ (Nat.le_add_l kr _) HRM2). }
  split. { cbn [ms_mem]. exact LKF. }
  split.
  { right. split; [exact Hpos|]. split.
    - cbn [ms_regs]. rewrite Rr10. reflexivity.
    - exists T. split.
      + eapply (arelay_append B RG ly S W mem ly (stack_free_state 0 fpos S2) W (ms_mem ms6) T T es fd HREL).
        * exact (proj1 (HNEW Hpos)).
        * exact (proj2 (HNEW Hpos)).
        * split; [exact Hpos | exact (proj2 Rfd)].
        * exact HinT6.
        * intros _; reflexivity.
        * intros b Hb. rewrite EabF. exact Hb.
        * exact VSRC.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left.
          unfold in_zr; cbn [fst snd]; lia.
        * exact VNS.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; left. unfold in_zr; cbn [fst snd]; lia.
        * exact VCAP.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; right; apply inG_cons; left. unfold in_zr; cbn [fst snd]; lia.
        * exact GNEW.
        * (* the old table bytes: below the new entry, kept by the journal *)
          intros x Hx. split.
          -- replace x with (T + (x - T)) by ring.
             apply (HEAPK T ATABLE (x - T) (HTne HTne0)); [revert Hx HED; clear; intros; lia|].
             unfold ra_FP. rewrite (proj2 (Z.eqb_neq T 0) HTne0). intros (r & Hr & Hrx).
             destruct Hr as [<- | []]. cbn [fst snd] in Hrx. revert Hx Hrx; clear; intros; lia.
          -- intros _. unfold arm. apply (apresent_writable SEGS).
             exact (proj1 (HTpres6 x ltac:(revert Hx HED; clear; intros; lia))).
        * (* the rest of the table: present, so visible *)
          intros x Hx. apply (aview_some_of_apresent SEGS).
          exact (proj1 (HTpres6 x ltac:(revert Hx HRQ; clear; unfold AENT; intros; lia))).
        * (* the old entries' footprints: off the table (W_relay_add_rep.v rar_efp_off_table), so outside the new
             entry, and kept by the journal *)
          intros r Hr a Ha. apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
          destruct HREL as [(HT0 & _ & _) | HR]; [exfalso; exact (HTne0 HT0)|].
          destruct (ra_efp_off_table_x ly S _ W mem md T es HAR HR e r a He Hr Ha) as (p & n & Hin & Hpi & Hoff).
          split.
          -- replace a with (p + (a - p)) by ring. apply (HEAPK p n (a - p) Hin Hpi).
             unfold ra_FP. rewrite (proj2 (Z.eqb_neq T 0) HTne0). intros (r' & Hr' & Hr'x).
             destruct Hr' as [<- | []]. cbn [fst snd] in Hr'x.
             replace (p + (a - p)) with a in Hr'x by ring. apply Hoff. revert Hr'x HED; clear; unfold AENT; intros; lia.
          -- intros _. unfold arm. apply (apresent_writable SEGS).
             assert (Hin6 : In (p, n) (ablocks B ly (stack_free_state 0 fpos S2))) by (rewrite EabF; exact Hin).
             destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR6 Hin6) as (_ & _ & _ & _ & Hpres6 & _).
             exact (proj1 (Hpres6 a ltac:(revert Hpi; clear; intros; lia))).
      + right. split; [exact HTne0|]. split; [reflexivity | exact EabF]. }
  (* errno *)
  exact ERC.
+ (* g_nsrc = g_capsrc: only the empty table (T = 0, |es| = 0), which the realloc grows to 16 entries *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
  assert (HT0 : T = 0).
  { destruct (Z.eqb_spec T 0) as [HT|HT]; [exact HT|].
    exfalso. cbn in Hc0. pose proof (proj1 (HNEW Hpos)) as Hlt4. lia. }
  rewrite HT0 in Hc0. cbn in Hc0.
  (* the empty table: |es| = 0 *)
  assert (Hes0 : es = []) by (apply length_zero_iff_nil; clear - Hc0; lia).
  subst T. subst es. clear Hc Hc0.
  (* the bne again (its recorded condition decides it), up to the `bnez a0` at 0x82a78 *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK6 : sh_ok SEGS Bx [] Ex (mrestrict Hh (ms_mem msx))) by (apply Forall_nil) end.
  paj_run_tok_xR RUNXR HS HJ3 SHOK6 Bspan.
  { ra_awr_g3 U249 U257 U248 U2d U38d U513d ly fpos F HGin. }
  pres_upd PRES.
  (* the `bnez a0`: a0 = sext |es| = 0, so it falls through to `li s11,16` *)
  psrr_branch_pi_x RUNPR BRR HS.
  { exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. rewrite SXn in Hc.
    change (bv_unsigned (sv_denot Ed (SLit 0))) with 0 in Hc. cbn in Hc. discriminate Hc. }
  clear Hc.
  (* s11 = 16, a0 = g_src = 0, a1 = 16 * 64 - 16 * 8 = 896, up to the realloc call at 0x82a98 *)
  paj_run_tok_xR RUNXR HS HJ3 SHOK6 Bspan.
  { ra_awr_g3 U249 U257 U248 U2d U38d U513d ly fpos F HGin. }
  pres_upd PRES.
  (* ---- realloc(g_src = 0, 896): the table, 16 entries ---- *)
  lazymatch goal with ms0 : machine_state |- _ => rename ms0 into msA end.
  assert (HceilS : alloc_ceiling <= spZ regs) by (revert Hceil Hslo WS; clear; intros; lia).
  (* the stack at and above sp0 is the entry's (the journal keeps it; it is no G byte) *)
  assert (KST : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msA) a = aview SEGS (w_H W) mem a).
  { pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (memS0 & HJ0 & Hag0).
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & HJ0k & _).
    intros a Ha. assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (clear - Ha HceilS; lia).
    rewrite (HJ0k a Hac ltac:(clear - Ha; lia)). apply Hag0.
    rewrite unsigned_lit_small by (clear - Ha HceilS C1; lia). intros Hg.
    destruct (HG a Hg) as [Hi1 _]. pose proof (Hsegs a Hi1) as Hlow.
    revert Hlow Ha HceilS C1; clear; unfold kLowMemEnd; intros; lia. }
  (* the prologue's saved ra and s0 at sp0 - 8 and sp0 - 16: chunks of the stack region (the state's fifth) *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx 4 _ HS eq_refl) as HRS
  | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 4 _ HS eq_refl) as HRS
  end.
  cbn [ms_mem restrict] in HRS.
  pose proof (slot_of_region _ _ (spZ regs) _ _ _ _ _ (-8) (SOff 1 0) (raZ regs) HRS U2d) as V8.
  specialize (V8 ltac:(repeat first [left; reflexivity | right])
    ltac:(cbn [sv_denot]; rewrite OLDd, OLDc, OLDb, OLDa, (EE 1%nat 1%bv eq_refl) by lia; rewrite Z.add_0_r; reflexivity)
    (bv_unsigned_in_range 64 (getr regs 1))).
  pose proof (slot_of_region _ _ (spZ regs) _ _ _ _ _ (-16) (SOff 8 0) (s0Z regs) HRS U2d) as V16.
  specialize (V16 ltac:(repeat first [left; reflexivity | right])
    ltac:(cbn [sv_denot]; rewrite OLDd, OLDc, OLDb, OLDa, (EE 8%nat 8%bv eq_refl) by lia; rewrite Z.add_0_r; reflexivity)
    (bv_unsigned_in_range 64 (getr regs 8))).
  pose proof (rdword_of_val_mem SEGS _ _ _ _ V8 (bv_unsigned_in_range 64 (getr regs 1))) as R8.
  pose proof (rdword_of_val_mem SEGS _ _ _ _ V16 (bv_unsigned_in_range 64 (getr regs 8))) as R16.
  replace (spZ regs + -8) with (spZ regs - 8) in R8 by ring.
  replace (spZ regs + -16) with (spZ regs - 16) in R16 by ring.
  clear HRS V8 V16.
  (* the chain at the call: relay_add's record on the entry's (ra_spec's room premise on this path) *)
  destruct (HCTX Hpos eq_refl) as (HROOM & HCTXin).
  pose proof (ra_chain_call_rec ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msA)) (spZ regs) (s0Z regs) ch (raZ regs)
    Hch HceilS Hal16 ltac:(revert Htop2 H47; clear; intros; lia) HROOM KST R8 R16 Hra4) as Hch'.
  set (ch' := (spZ regs, raZ regs, s0Z regs) :: ch) in Hch'.
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3.
  prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  assert (HSPa : spZ (ms_regs msA) = spZ regs + -128).
  { unfold spZ at 1. rewrite N2, U2d. rewrite unsigned_lit_small by (revert Hslo Hshi H47 Hceil Hstk0 C1; clear; unfold spZ; intros; lia). lia. }
  assert (HCH : chain_pre ly (aview SEGS (w_H W) (ms_mem msA)) (ms_regs msA) ch').
  { apply (achain_chain_pre ly _ (spZ regs - 128) (spZ regs) ch' (ms_regs msA) Hch').
    - rewrite HSPa. revert Hceil Hslo WS; clear; intros; lia.
    - unfold s0Z. rewrite N8. exact U2d.
    - unfold raZ. rewrite N1, unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia. }
  (* the meter's forced-success premise and the live-bytes room: ra_spec's, at T = 0, carried across the fake-frame
     seat (a set_fs step: MO_FR, ES2; it keeps the live blocks: Eab) *)
  assert (HMOr : mo_ok MT S2 (mo_malloc MT ATABLE + mo_free MT)).
  { pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)) as Hm0. pose proof (mo_free_nonneg MT MLAW) as Hf0.
    assert (MOseat : mo_le MT S S2 0) by (rewrite ES2; exact (MO_FR S fS2)).
    apply (mok_station MT S S2 (ra_cost MT 0) 0 _ MLAW HMOK MOseat); [clear - Hm0 Hf0; lia|].
    unfold ra_cost. cbn [Z.eqb]. clear; lia. }
  assert (HBB : blocks_bytes S2 + ATABLE <= LIVE_MAX).
  { rewrite (blocks_bytes_bsum B ly S2), Eab, <- (blocks_bytes_bsum B ly S). exact (HLIVE Hpos eq_refl). }
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3m.
  destruct HJ3 as (HSTK3 & HXO3 & (memS3 & HJi3 & HAG3) & HOUT3). rewrite !Z.add_0_r in HJi3.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (AREALLOC_R W (ms_regs msA) (ms_mem msA) RA_STK (spZ regs) (ra_FP 0 []) ly S _ W memS3 md [(0, fpos)] ly S2 _ _ 0
      0 0 ATABLE (-128) _ ch' kr HJi3).
    - left; reflexivity.
    - rewrite N10, E516. reflexivity.
    - rewrite N11. unfold ATABLE. first [reflexivity | vm_compute; reflexivity].
    - split; [unfold ATABLE; lia | exact HMMAX].
    - exact HBB.
    - (* the live counts at the call's pre state S2: the entry's (Eab), under ra_peak 0 *)
      unfold cnt_ok. apply (cnt_ok_pk_mono RP (ra_peak 0) _ (ablocks B ly S) (ablocks B ly S2)); [|exact HPK].
      intros P. cbv beta. rewrite Eab. lia.
    - exact HSPa.
    - reflexivity.
    - apply Z.leb_le; reflexivity.
    - unfold RA_STK, RA_FRAME. clear; lia.
    - (* the stack room below the call, from the journal's astk_ok *)
      eapply aj_stack_room_xR; [exact HJi3 | exact HSPa | unfold RA_STK, RA_FRAME; clear; lia].
    - rewrite N3, OLDd, OLDc, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite N4, OLDd, OLDc, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - exact N1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact HCH.
    - exact (RO_ARx _ _ _ _ _ _ (proj1 HJi3)).
    - (* the hull admission at the call, from the meter (HA_ra) *)
      apply HA_ra; [unfold ATABLE; lia | exact HMOr].
    - (* the caller context: the call returns to A_relay_addP + 332, on relay_add's record *)
      replace (raZ (ms_regs msA)) with (A_relay_addP + 332); [exact HCTXin|].
      unfold raZ. rewrite N1, unsigned_lit_small by (clear - HBASE; lia).
      unfold A_relay_addP, A_relay_add, AF_fr_relay_add. clear; lia.
    - (* the room: ra_cost MT_rk 0 = 2, the realloc's own charge, carried across the seat (HRM2) *)
      exact HRM2.
    - intros Hpq. exfalso. apply Hpq. reflexivity.
    - exact HMOr. }
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & res & -> & HJi4 & HP4 & Hres10 & Hfr4 & Hres4096 & HpermZ & _ & _ &
    Hkept4 & Hmle4 & HRM4 & Herr4 & Hpres4).
  assert (HJ4 : ajournal_gx_xR SEGS B PST ARx R G 0 [] RA_STK (spZ regs) (ra_FP 0 []) ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem4 md4 (0 + 3)).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) _ ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem4 md4 _ memS3 HSTK3 HXO3);
    [rewrite !Z.add_0_r; exact HJi4 | exact HAG3 | intros a Ha _; clear - Ha; lia]. }
  (* ---- back in relay_add: the new table at res ---- *)
  pose proof (proj1 HJi4) as HAR4.
  assert (HinN : In (res, ATABLE) (ablocks B ly4 S4))
  by (apply (Permutation_in _ (Permutation_sym (HpermZ eq_refl))); left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 mem4 md4 res ATABLE HAR4 HinN) as (HN16 & HN4096 & HNceil & _).
  assert (HRQ : ATABLE <= req_size ATABLE) by (unfold req_size, ATABLE; cbn [Z.eqb]; lia).
  assert (HresB : 0 <= res < 140737479966720) by (revert HN4096 HNceil HRQ C1; clear; unfold ATABLE; intros; lia).
  (* the new block is apart from the fake frame (both are live at the call's end state) *)
  assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite Hfr4; exact Hfin2).
  destruct (alx_layout _ _ _ LAWS ly S _ W mem md ly4 HAR (proj1 (proj2 HJi4))) as (_ & HFA4 & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly4 S4 _ W4 mem4 md4 res ATABLE 0 fpos HAR4 HinN Hfin4) as DFN.
  rewrite (HFA4 0 fpos) in DFN. fold F in DFN. change (fs_frame_bytes 0) with 64 in DFN.
  unfold zdisjoint in DFN. cbn [fst snd] in DFN.
  (* the globals stay writable in the call's memory *)
  assert (GWs4 : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W4) mem4) (rg_src RG + o)).
  { intros o Ho.
    assert (Hin : inG (RA_G RG) (rg_src RG + o))
    by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
        unfold in_zr; cbn [fst snd]; lia).
    apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by (clear - BSR Ho; lia).
    exact (proj1 (HG _ (HGin _ Hin))). }
  assert (GWc4 : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W4) mem4) (rg_capsrc RG + o)).
  { intros o Ho.
    assert (Hin : inG (RA_G RG) (rg_capsrc RG + o))
    by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
    apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by (clear - BCS Ho; lia).
    exact (proj1 (HG _ (HGin _ Hin))). }
  assert (GWn4 : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W4) mem4) (rg_nsrc RG + o)).
  { intros o Ho.
    assert (Hin : inG (RA_G RG) (rg_nsrc RG + o))
    by (apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
    apply GW; [exact Hin|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small by (clear - BNS Ho; lia).
    exact (proj1 (HG _ (HGin _ Hin))). }
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR3m) as (Kc5a & Ku5a & Kg5a & Kgu5a).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR4) as (Kc5 & Ku5 & Kg5 & Kgu5).
  rewrite HBgot, HBcell in Kg5a, Kg5. rewrite HBcell in Kc5a, Kc5. rewrite (palf_got_uar B TLF) in Kgu5a, Kgu5.
  jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS5.
  match type of HS5 with ?ty -> _ => assert (HRK : ty); [|specialize (HS5 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | | | apply Forall_nil].
  - eapply ra_region_kept_img; [exact Hkept4 | exact U249 | |].
    + intros o Ho.
      assert (Hin : inG (RA_G RG) (rg_src RG + o))
      by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
          unfold in_zr; cbn [fst snd]; lia).
      split; [exact (proj1 (HG _ (HGin _ Hin)))|].
      split; [exact (proj1 (proj2 (HG _ (HGin _ Hin)))) | exact (HGerr _ Hin)].
    + exact GWs4.
  - eapply ra_region_kept_img; [exact Hkept4 | exact U257 | |].
    + intros o Ho.
      assert (Hin : inG (RA_G RG) (rg_capsrc RG + o))
      by (apply inG_cons; right; apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
      split; [exact (proj1 (HG _ (HGin _ Hin)))|].
      split; [exact (proj1 (proj2 (HG _ (HGin _ Hin)))) | exact (HGerr _ Hin)].
    + exact GWc4.
  - eapply ra_region_kept_img; [exact Hkept4 | exact U248 | |].
    + intros o Ho.
      assert (Hin : inG (RA_G RG) (rg_nsrc RG + o))
      by (apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
      split; [exact (proj1 (HG _ (HGin _ Hin)))|].
      split; [exact (proj1 (proj2 (HG _ (HGin _ Hin)))) | exact (HGerr _ Hin)].
    + exact GWn4.
  - eapply (region_kept_frame_aj SEGS B Ed ly S2 W _ W4 mem4 _ _ _ 38%nat 0 64 0 0 _ F 0 fpos
      Hkept4 U38d Hfin2);
    [fold F; clear; lia | fold F; change (fs_frame_bytes 0) with 64; clear; lia | clear; lia |].
    intros a Ha [Hx | (Hz0 & _)]; [|exact (Hz0 eq_refl)].
    revert Ha Hx DFN HRQ; clear; unfold ATABLE; intros; lia.
  - eapply ra_region_kept_stack_aj_xR; [exact Hkept4 | exact HJi4 | exact U2d | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at Ed _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
    [exact U241d | exact (val_mem_of_rdword SEGS _ _ _ _ Kg5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg5) | lia].
  - apply (region_kept_val_at Ed _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
    [exact U273d | exact (val_mem_of_rdword SEGS _ _ _ _ Kc5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc5) | lia].
  - apply (region_kept_val_at Ed _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
    [exact U242d | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu5a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu5) | lia].
  - apply (region_kept_val_at Ed _ _ 32 (as_uar_cell B) 4 1);
    [exact U32d | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku5a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku5) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
  remember (havoc Ed 66 (map (getr regs4) CLOB)) as Ee eqn:HEe in HS.
  assert (HEIe : img_env VAL A_LIM Ee) by (rewrite HEe; apply img_env_havoc; [exact HEId | cbv; lia]).
  assert (OLDe : forall m, (m < 66)%nat -> ew Ee m = ew Ed m) by (intros m Hm; rewrite HEe; apply YN3v.ew_havoc_old; exact Hm).
  assert (ABVe : forall m, (82 <= m)%nat -> ew Ee m = ew Ed m) by (intros m Hm; rewrite HEe; apply ew_havoc_above; cbn; lia).
  assert (HAEe : env_agree 32 (Ereg regs ra_extra) Ee) by (rewrite HEe; apply env_agree_havoc_ge; [cbv; lia | exact HAEd]).
  assert (E70 : ew Ee 70 = Z_to_bv 64 res).
  { rewrite HEe. change 70%nat with (66 + 4)%nat.
    rewrite (ew_havoc_new Ed 66 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbv [CLOB]. cbn [map nth]. exact Hres10. }
  clear HEe.
  assert (U70 : bv_unsigned (ew Ee 70) = res) by (rewrite E70; apply unsigned_lit_small; clear - HresB; lia).
  assert (U2e : bv_unsigned (ew Ee 2) = spZ regs) by (rewrite OLDe by lia; exact U2d).
  assert (U38e : bv_unsigned (ew Ee 38) = F) by (rewrite OLDe by lia; exact U38d).
  assert (U32e : bv_unsigned (ew Ee 32) = as_uar_cell B) by (rewrite OLDe by lia; exact U32d).
  assert (U513e : bv_unsigned (ew Ee 513) = SB + F / 8) by (rewrite ABVe by lia; exact U513d).
  assert (U248e : bv_unsigned (ew Ee 248) = rg_nsrc RG) by (rewrite ABVe by lia; exact U248).
  assert (U257e : bv_unsigned (ew Ee 257) = rg_capsrc RG) by (rewrite ABVe by lia; exact U257).
  assert (U249e : bv_unsigned (ew Ee 249) = rg_src RG) by (rewrite ABVe by lia; exact U249).
  assert (U241e : bv_unsigned (ew Ee 241) = VAL (A_OBJ 0)) by (rewrite ABVe by lia; exact U241d).
  assert (U242e : bv_unsigned (ew Ee 242) = VAL (A_OBJ 1)) by (rewrite ABVe by lia; exact U242d).
  assert (U273e : bv_unsigned (ew Ee 273) = VAL (A_OBJ 32)) by (rewrite ABVe by lia; exact U273d).
  assert (U310e : bv_unsigned (ew Ee 310) = rg_nsrc RG + 704) by (rewrite ABVe by lia; exact U310).
  assert (U311e : bv_unsigned (ew Ee 311) = rg_capsrc RG + 612) by (rewrite ABVe by lia; exact U311).
  assert (U312e : bv_unsigned (ew Ee 312) = rg_src RG + 688) by (rewrite ABVe by lia; exact U312).
  assert (E514e : ew Ee 514 = Z_to_bv 64 0) by (rewrite ABVe by lia; rewrite E514; reflexivity).
  assert (E516e : ew Ee 516 = Z_to_bv 64 0) by (rewrite ABVe by lia; exact E516).
  (* the returned block is not NULL: the `beqz a0` at 0x82a9c is not taken *)
  psrr_branch_pi_x RUNPR BRR HS.
  { exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom Ee 70 res E70 ltac:(clear - HresB; lia)) in Hc.
    rewrite (U_lit Ee 0 ltac:(clear; lia)) in Hc. apply Z.eqb_eq in Hc. clear - Hc HN4096. lia. }
  clear Hc.
  (* ---- g_src := res (sd a0,-688(s9)) and g_capsrc := 16 (sw s11,-612(s10)) ----
     the stores address the two cells through the kept auipc registers, so their regions are rebased to the
     registers' atoms for the stores and back to the object atoms for the loads that follow (W_rebase.v). *)
  assert (HFA4' : frame_addr ly4 0 fpos = F) by exact (HFA4 0 fpos).
  pose proof (eq_trans HV8 (eq_sym HH32)) as HSRC32.
  pose proof (eq_trans HV16 (eq_sym HH31)) as HCAP31.
  assert (HSRC32' : VAL (A_HI 32) = VAL (A_OBJ 8) + 688).
  { rewrite HSRC32. symmetry. apply Z.sub_add. }
  assert (HCAP31' : VAL (A_HI 31) = VAL (A_OBJ 16) + 612).
  { rewrite HCAP31. symmetry. apply Z.sub_add. }
  (* the auipc atoms the stores address through need their own band fact, or the token runner's static check
     cannot place their regions against the shadow span *)
  pose proof (st_ok_pi_add_fact Ee _ _ 312 (mkAF 65536 6271664 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U312e, Z.pow_0_r, Z.mod_1_r; clear - BSR; lia)) as HSa.
  clear HS; rename HSa into HS.
  pose proof (st_ok_pi_add_fact Ee _ _ 311 (mkAF 65536 6271664 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U311e, Z.pow_0_r, Z.mod_1_r; clear - BCS; lia)) as HSa.
  clear HS; rename HSa into HS. norm_ss HS.
  prebase HS 0%nat 312%nat (-688) HSRC32.
  prebase HS 1%nat 311%nat (-612) HCAP31.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK7 : sh_ok SEGS Bx [] Ex (mrestrict Hh (ms_mem msx))) by (apply Forall_nil) end.
  paj_run_to_tok_xR RUNTOXR HS HJ4 SHOK7 Bspan 1984.
  { ra_awr_g3F U312e U311e U248e U2e U38e U513e HFA4' fpos F HGin. }
  (* back to the object atoms: the loads of g_nsrc and g_src that follow are PLdHi slots *)
  prebase HS 0%nat 249%nat 688 HSRC32'.
  prebase HS 1%nat 257%nat 612 HCAP31'.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK8 : sh_ok SEGS Bx [] Ex (mrestrict Hh (ms_mem msx))) by (apply Forall_nil) end.
  paj_run_tok_xR RUNXR HS HJ4 SHOK8 Bspan.
  { ra_awr_g3F U249e U257e U248e U2e U38e U513e HFA4' fpos F HGin. }
  (* ---- __asan_memset (s4, 0, 56): the first entry of the new table, at res + AENT * 0.  Its 56 bytes lie in
     the new block, which the journal's start state does not hold, so they are awr_bytes as a tmp block (arm 1
     has them through ra_FP instead; at T = 0 the footprint is empty). ---- *)
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4m.
  assert (HESZ : 0 < AENT * (0 + 1) <= ATABLE) by (clear; unfold AENT, ATABLE; lia).
  assert (HEIN : forall a, res + AENT * 0 <= a < res + AENT * 0 + 56 -> res <= a < res + req_size ATABLE).
  { intros a Ha. revert Ha HRQ; clear; unfold AENT, ATABLE; intros; lia. }
  assert (HnotIn : ~ In (res, ATABLE) (ablocks B ly S)).
  { intros Hin0. rewrite <- Eab in Hin0. apply in_split in Hin0 as (l1 & l2 & El).
    assert (HPdup : Permutation (ablocks B ly4 S4) ((res, ATABLE) :: (res, ATABLE) :: (l1 ++ l2))).
    { eapply Permutation_trans; [exact (HpermZ eq_refl)|]. apply perm_skip.
      rewrite El. symmetry. apply Permutation_middle. }
    pose proof (ra_sep_blocks_perm_x ly4 S4 _ W4 mem4 md4 (res, ATABLE) (res, ATABLE) _ HAR4 HPdup) as Ddup.
    unfold zdisjoint, block_rng in Ddup. cbn [fst snd] in Ddup. revert Ddup HRQ; clear; unfold ATABLE; intros; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3.
  prreg HS (4%bv : bv 5) M4. prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11.
  prreg HS (12%bv : bv 5) M12.
  lazymatch type of M10 with getr ?rg 10 = _ =>
    assert (MA0 : getr rg 10 = w64 (res + AENT * 0)) end.
  { rewrite M10. rewrite (ra_entry_addr (ew Ee 70) (ew Ee 514) res 0 E70 E514e
      ltac:(clear - HresB; lia) ltac:(clear; lia)).
    reflexivity. }
  destruct HJ4 as (HSTK4 & HXO4 & (memS4 & HJi4b & HAG4) & HOUT4). rewrite !Z.add_0_r in HJi4b.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_intrin_at_xR B PST ARx LAWS R_trans WLE_R OSet (SIGMA WS_asan_memset) AMEMSET W4 _ _ RA_STK
      (spZ regs) (ra_FP 0 []) ly S _ W memS4 md [(0, fpos)] ly4 S4 _ _ _ (res + AENT * 0) 0 56 (-128) _ HJi4b).
    - exact MA0.
    - exact M11.
    - exact M12.
    - clear; lia.
    - clear - HN4096; unfold AENT; lia.
    - revert HN4096 HNceil HRQ C1; clear; unfold AENT, ATABLE; intros; lia.
    - unfold spZ at 1. rewrite M2, U2e.
      rewrite unsigned_lit_small by (revert Hslo Hshi H47 Hceil Hstk0 C1; clear; unfold spZ; intros; lia). lia.
    - reflexivity.
    - clear; lia.
    - rewrite WS, Hes. clear; lia.
    - rewrite M3, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite M4, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - exact M1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right; right; left. exists res, ATABLE.
        split; [exact HinN | split; [exact HnotIn | exact (HEIN a Ha)]].
      + pose proof (HEIN a Ha) as Hb.
        revert Hb HNceil HRQ Hceil Hslo Hstk0 C1 WS; clear; unfold ESTACK; intros; lia.
    - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly4 S4 _ W4 _ _ res ATABLE);
      [exact HAR4m | exact HinN | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia].
    - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly4 S4 _ W4 _ _ res ATABLE);
      [exact HAR4m | exact HinN | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia].
    - intros Hpq. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly4 S4 _ W4 _ _ res ATABLE);
      [exact HAR4m | exact HinN | clear; unfold AENT; lia | revert HESZ HRQ; clear; unfold AENT; intros; lia | exact Hpq].
    - exact I. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJi5 & HP5 & Hd10 & Hset & Hfr5 & Hpres5).
  assert (HJ5 : ajournal_gx_xR SEGS B PST ARx R G 0 [] RA_STK (spZ regs) (ra_FP 0 []) ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem5 md5 (0 + 3)).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) _ ly S Hp W mem md [(0, fpos)] ly4 S4 Hp4 W4 mem5 md5 _ memS4 HSTK4 HXO4);
    [rewrite !Z.add_0_r; exact HJi5 | exact HAG4 | intros a Ha _; clear - Ha; lia]. }
  clear HJi5 HJi4b HAG4.
  (* ---- presence.  The realloc changed the world, so the walk's presence invariant is re-anchored at
     (W4, mem4) and the step across the realloc is recorded once, in the form ra_post asks for (apres_kept):
     an image byte off the owned statics and off errno is not inside the new block (alx_client_img), so the
     rule's presence clause carries it. ---- *)
  assert (PKR : apres_kept B W mem W4 mem4).
  { intros a Hi Ho He Hpq. apply (Hpres4 a Hi).
    - intros Hw. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS ly S2 _ W (ms_mem msA) _ a HAR3m Hi) Hw).
    - intros Hw. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS ly4 S4 _ W4 mem4 md4 a HAR4 Hi) Hw).
    - exact He.
    - intros [Hx | (Hz0 & _)]; [|exact (Hz0 eq_refl)].
      destruct (alx_client_img _ _ _ LAWS ly4 S4 _ W4 mem4 md4 a HAR4
        ltac:(left; exists res, ATABLE; split; [exact HinN | exact Hx])) as (_ & Hni). exact (Hni Hi).
    - exact (PRES a Hi Hpq). }
  assert (PRES4a : forall a, in_img SEGS a -> apresent (w_H W4) mem4 a -> apresent (w_H W4) mem4 a)
  by (intros a _ Hpq; exact Hpq).
  pose proof (pres_grow (w_H W4) _ _ _ PRES4a HG0) as PRES4b.
  pose proof (pres_grow (w_H W4) _ _ _ PRES4b HG1) as PRES4c.
  assert (PRES4 : forall a, in_img SEGS a -> apresent (w_H W4) mem4 a -> apresent (w_H W4) mem5 a)
  by (intros a Hi Hpq; exact (Hpres5 a (PRES4c a Hi Hpq))).
  clear PRES PRES4a PRES4b PRES4c HG0 HG1.
  (* ---- back in relay_add after the memset: rebuild the state, keeping all nine regions ---- *)
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR5m.
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly4 S4 _ W4 (ms_mem ms5) _ _ _ HAR4m HinN) as HNoff. unfold off_img in HNoff.
  assert (HED2 : res <= res + AENT * 0 /\ res + AENT * 0 + 56 <= res + req_size ATABLE)
  by (revert HRQ; clear; unfold AENT, ATABLE; intros; lia).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR4m) as (Kc6a & Ku6a & Kg6a & Kgu6a).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR5m) as (Kc6 & Ku6 & Kg6 & Kgu6).
  rewrite HBgot, HBcell in Kg6a, Kg6. rewrite HBcell in Kc6a, Kc6. rewrite (palf_got_uar B TLF) in Kgu6a, Kgu6.
  jafter_call_keep_pi HS 82%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS6.
  match type of HS6 with ?ty -> _ => assert (HRK : ty); [|specialize (HS6 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | | | apply Forall_nil].
    - apply (region_kept_aview Ee (w_H W4) (ms_mem ms5) mem5 249 (rg_src RG)); [exact U249e | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BSR; clear; intros; lia
      | revert Ha BSR HNoff HED2; clear; intros; lia
      | revert Ha BSR Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ee (w_H W4) (ms_mem ms5) mem5 257 (rg_capsrc RG)); [exact U257e | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BCS; clear; intros; lia
      | revert Ha BCS HNoff HED2; clear; intros; lia
      | revert Ha BCS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ee (w_H W4) (ms_mem ms5) mem5 248 (rg_nsrc RG)); [exact U248e | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha BNS; clear; intros; lia
      | revert Ha BNS HNoff HED2; clear; intros; lia
      | revert Ha BNS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Ee (w_H W4) (ms_mem ms5) mem5 38 F); [exact U38e | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha HF4096 HFceil HFhigh C1; clear; intros; lia
      | revert Ha DFN HED2; clear; intros; lia
      | revert Ha HF4096 HFceil HFhigh HFimg Hslo Hshi H47 Hceil Hstk0 C1 WS Hes; clear; intros; lia ].
    - apply (region_kept_aview Ee (w_H W4) (ms_mem ms5) mem5 2 (spZ regs)); [exact U2e | | exact Hpres5].
      intros a Ha. apply Hfr5;
      [ revert Ha Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha HED2 HNceil Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha; clear; intros; lia ].
    - apply (region_kept_val_at Ee _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
      [exact U241e | exact (val_mem_of_rdword SEGS _ _ _ _ Kg6a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg6) | lia].
    - apply (region_kept_val_at Ee _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
      [exact U273e | exact (val_mem_of_rdword SEGS _ _ _ _ Kc6a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc6) | lia].
    - apply (region_kept_val_at Ee _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
      [exact U242e | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu6a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu6) | lia].
    - apply (region_kept_val_at Ee _ _ 32 (as_uar_cell B) 4 1);
      [exact U32e | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku6a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku6) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
  remember (havoc Ee 82 (map (getr regs5) CLOB)) as Ef eqn:HEf in HS.
  assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEIe | cbv; lia]).
  assert (OLDf : forall m, (m < 82)%nat -> ew Ef m = ew Ee m) by (intros m Hm; rewrite HEf; apply YN3v.ew_havoc_old; exact Hm).
  assert (ABVf : forall m, (98 <= m)%nat -> ew Ef m = ew Ee m) by (intros m Hm; rewrite HEf; apply ew_havoc_above; cbn; lia).
  assert (HAEf : env_agree 32 (Ereg regs ra_extra) Ef) by (rewrite HEf; apply env_agree_havoc_ge; [cbv; lia | exact HAEe]).
  clear HEf.
  (* ---- g_nsrc's region moves to the kept auipc register s8 = A_HI 30 (the store `sw s10,-704(s8)`) ---- *)
  assert (HR30 : VAL 248%nat = VAL 310%nat + -704).
  { pose proof HH30 as X1. pose proof HV7 as X2. change (A_HI 30) with 310%nat in X1. change (A_OBJ 7) with 248%nat in X2.
    revert X1 X2. clear. intros. lia. }
  prebase HS 2%nat 310%nat (-704) HR30.
  assert (E70f : ew Ef 70 = Z_to_bv 64 res) by (rewrite OLDf by lia; exact E70).
  assert (U70f : bv_unsigned (ew Ef 70) = res) by (rewrite OLDf by lia; exact U70).
  assert (U2f : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact U2e).
  assert (U38f : bv_unsigned (ew Ef 38) = F) by (rewrite OLDf by lia; exact U38e).
  assert (U32f : bv_unsigned (ew Ef 32) = as_uar_cell B) by (rewrite OLDf by lia; exact U32e).
  assert (U513f : bv_unsigned (ew Ef 513) = SB + F / 8) by (rewrite ABVf by lia; exact U513e).
  assert (U249f : bv_unsigned (ew Ef 249) = rg_src RG) by (rewrite ABVf by lia; exact U249e).
  assert (U257f : bv_unsigned (ew Ef 257) = rg_capsrc RG) by (rewrite ABVf by lia; exact U257e).
  assert (U310f : bv_unsigned (ew Ef 310) = rg_nsrc RG + 704) by (rewrite ABVf by lia; exact U310e).
  assert (U241f : bv_unsigned (ew Ef 241) = VAL (A_OBJ 0)) by (rewrite ABVf by lia; exact U241e).
  assert (U242f : bv_unsigned (ew Ef 242) = VAL (A_OBJ 1)) by (rewrite ABVf by lia; exact U242e).
  assert (U273f : bv_unsigned (ew Ef 273) = VAL (A_OBJ 32)) by (rewrite ABVf by lia; exact U273e).
  assert (E514f : ew Ef 514 = Z_to_bv 64 0) by (rewrite ABVf by lia; exact E514e).
  assert (E33f : ew Ef 33 = Z_to_bv 64 SB) by (rewrite OLDf, OLDe, OLDd, OLDc by lia; exact E33b).
  (* ---- the entry's address s4 as atom 517: its value, band fact, alias, region and shadow entry ---- *)
  destruct (alx_blocks _ _ _ LAWS ly4 S4 _ W4 mem5 md5 res ATABLE HAR5m HinN) as (_ & _ & _ & HTapp2 & HTpres2 & _).
  (* this file turns off zify's mod/div handling, so the alignment is shown by hand *)
  assert (HD8 : (res + AENT * 0) mod 8 = 0).
  { pose proof (Z.div_mod res 16 ltac:(lia)) as HT. rewrite HN16, Z.add_0_r in HT. unfold AENT.
    replace (res + 56 * 0) with ((2 * (res / 16) + 7 * 0) * 8) by (revert HT; clear; intros; lia).
    apply Z.mod_mul. lia. }
  assert (HDB : 4096 <= res + AENT * 0 /\ res + AENT * 0 + 56 <= alloc_ceiling /\ (res + AENT * 0) mod 8 = 0).
  { split; [|split; [|exact HD8]]; revert HN4096 HNceil HED2; clear; unfold AENT; intros; lia. }
  pose proof (st_ok_pi_havoc_hi 517 Ef _ _ [Z_to_bv 64 (res + AENT * 0)] HS
    ltac:(vm_compute; reflexivity)) as HS7.
  clear HS. rename HS7 into HS.
  remember (havoc Ef 517 [Z_to_bv 64 (res + AENT * 0)]) as Eg eqn:HEg in HS.
  assert (HEIg : img_env VAL A_LIM Eg) by (rewrite HEg; apply img_env_havoc_hi; [exact HEIf | cbv; lia]).
  assert (OLDg : forall m, (m < 517)%nat -> ew Eg m = ew Ef m) by (intros m Hm; rewrite HEg; apply YN3v.ew_havoc_old; exact Hm).
  assert (E517 : ew Eg 517 = Z_to_bv 64 (res + AENT * 0))
  by (rewrite HEg; exact (ew_havoc_new _ 517 [Z_to_bv 64 (res + AENT * 0)] 0 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
  assert (HAEg : env_agree 32 (Ereg regs ra_extra) Eg) by (rewrite HEg; apply env_agree_havoc_ge; [cbv; lia | exact HAEf]).
  clear HEg.
  assert (C1b : alloc_ceiling < 2 ^ 63) by (revert C1; clear; intros; lia).
  assert (U517 : bv_unsigned (ew Eg 517) = res + AENT * 0).
  { rewrite E517. apply unsigned_lit_small. revert HDB C1b. clear. intros. lia. }
  assert (E514g : ew Eg 514 = Z_to_bv 64 0) by (rewrite OLDg by lia; exact E514f).
  assert (E70g : ew Eg 70 = Z_to_bv 64 res) by (rewrite OLDg by lia; exact E70f).
  assert (E33g : ew Eg 33 = Z_to_bv 64 SB) by (rewrite OLDg by lia; exact E33f).
  assert (U2g : bv_unsigned (ew Eg 2) = spZ regs) by (rewrite OLDg by lia; exact U2f).
  assert (U38g : bv_unsigned (ew Eg 38) = F) by (rewrite OLDg by lia; exact U38f).
  assert (U513g : bv_unsigned (ew Eg 513) = SB + F / 8) by (rewrite OLDg by lia; exact U513f).
  assert (U249g : bv_unsigned (ew Eg 249) = rg_src RG) by (rewrite OLDg by lia; exact U249f).
  assert (U257g : bv_unsigned (ew Eg 257) = rg_capsrc RG) by (rewrite OLDg by lia; exact U257f).
  assert (U310g : bv_unsigned (ew Eg 310) = rg_nsrc RG + 704) by (rewrite OLDg by lia; exact U310f).
  assert (U241g : bv_unsigned (ew Eg 241) = VAL (A_OBJ 0)) by (rewrite OLDg by lia; exact U241f).
  assert (U242g : bv_unsigned (ew Eg 242) = VAL (A_OBJ 1)) by (rewrite OLDg by lia; exact U242f).
  assert (U273g : bv_unsigned (ew Eg 273) = VAL (A_OBJ 32)) by (rewrite OLDg by lia; exact U273f).
  assert (U32g : bv_unsigned (ew Eg 32) = as_uar_cell B) by (rewrite OLDg by lia; exact U32f).
  pose proof (st_ok_pi_add_fact Eg _ _ 517 (HPTR 3) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U517; change (2 ^ 3) with 8;
          revert HDB C1; clear; intros; lia)) as HS7.
  clear HS; rename HS7 into HS.
  (* s4's value tree is atom 517 (the alias lets the engine address the entry through s4); in arm 2 the table
     pointer in it is the realloc's result, atom 70 *)
  assert (SXng : bv_unsigned (sv_denot Eg (SExt true 32 (SOff 514 0))) = 0).
  { rewrite U_sext32'. change (bv_unsigned (sv_denot Eg (SOff 514 0))) with (U Eg (SOff 514 0)).
    rewrite (U_atom Eg 514 _ E514g) by (clear; lia). apply sx32_small. clear; lia. }
  assert (HAL : sv_denot Eg (SAlu ALU_ADD (SOff 70 0)
      (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 6))
                    (SAlu ALU_SLL (SExt true 32 (SOff 514 0)) (SLit 3)))) = sv_denot Eg (SOff 517 0)).
  { apply bv_eq.
    lazymatch goal with |- bv_unsigned (sv_denot Eg ?x) = bv_unsigned (sv_denot Eg ?y) =>
      change (U Eg x = U Eg y) end.
    rewrite (U_atom Eg 517 _ E517) by (revert HDB C1b; clear; intros; lia).
    rewrite !U_SAlu. cbn [zalu_raw].
    change (U Eg (SExt true 32 (SOff 514 0))) with (bv_unsigned (sv_denot Eg (SExt true 32 (SOff 514 0)))).
    rewrite SXng, (U_atom Eg 70 res E70g) by (clear - HresB; lia).
    rewrite !U_lit by lia.
    change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
    rewrite (ZC (0 * 8)) by (clear; lia).
    rewrite (ZC (0 * 64)) by (clear; lia).
    rewrite (ZC (0 * 64 - 0 * 8)) by (clear; lia).
    rewrite (ZC (res + (0 * 64 - 0 * 8))) by (clear - HresB; lia).
    unfold AENT. clear. lia. }
  pose proof (st_ok_pi_add_alias Eg _ _ _ _ HS HAL) as HS7. clear HS; rename HS7 into HS.
  (* the entry's region: extent its 56 bytes, write window its first word (s->fd) *)
  pose proof (st_ok_pi_add_region Eg _ _ ra_ent_region HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok, ra_ent_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U517; split; [revert HDB C1b; clear; intros; lia|]; split; [revert HDB C1b; clear; intros; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS);
      exact (proj1 (HTpres2 (res + AENT * 0 + o) ltac:(revert Ho HED2; clear; intros; lia)))
    | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, ra_ent_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U517, U249g, U257g, U310g, U38g, U2g, U241g, U273g, U242g, U32g;
    repeat split;
    first [ solve [revert HNoff HED2 BSR BCS BNS; clear; intros; lia]
          | solve [revert DFN HED2; clear; intros; lia]
          | solve [revert HED2 HNceil Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia]
          | solve [revert HNoff HED2 HgotR HcellR HguR HuR PV0 PV1 PV32; clear; intros; lia]
          | lazymatch goal with |- ?g => idtac "ENT-DISJ" g; fail end ])) as HS7.
  clear HS; rename HS7 into HS. norm_ss HS.
  (* ---- the run 0x82ad0-0x82af8: g_nsrc + 1 stored, the entry's shadow checked (a token: the granule is in the
     live block), s->fd = fd stored, a0 = &g_lock; it stops at the pthread_mutex_unlock call ---- *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (SHOK9 : sh_ok SEGS Bx [mkSHE 517 0 56] Ex (mrestrict Hh (ms_mem msx))) end.
  { unfold sh_ok. constructor; [|constructor].
    eapply shent_ok_of_range.
    - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly4 S4 _ W4 _ _ res ATABLE (res + AENT * 0) 56);
      [exact HAR5m | exact HinN | revert HED2; clear; intros; lia | revert HED2; clear; intros; lia].
    - unfold Bx. rewrite (U_atom Eg 33 SB E33g) by (unfold SB; lia). reflexivity.
    - rewrite (U_atom Eg 517 _ E517) by (revert HDB C1b; clear; intros; lia). reflexivity.
    - lia.
    - lia.
    - intros x Hx. cbn in Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      revert Hx HTapp2 HED2; clear; intros; lia. }
  (* the rebased g_nsrc region's new base atom 310 needs its band fact *)
  pose proof (st_ok_pi_add_fact Eg _ _ 310 (mkAF 65536 6271680 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U310g, Z.pow_0_r, Z.mod_1_r; revert BNS; clear; intros; lia))
    as HS7.
  clear HS; rename HS7 into HS.
  (* s4 := SOff 517 0 in the symbolic registers (the alias alone does not reach inside the shadow address) *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Eg ssx msx 20%bv HS) as Q20 end.
  lazymatch type of Q20 with _ = sv_denot _ ?x => let x' := eval vm_compute in x in change x with x' in Q20 end.
  rewrite HAL in Q20.
  pose proof (ra_set_reg Eg _ _ 20%bv (SOff 517 0) HS Q20 eq_refl) as HS7. clear HS Q20; rename HS7 into HS. norm_ss HS.
  paj_run_tok_xR RUNXR HS HJ5 SHOK9 Bspan.
  { apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ra_ent_region] in Ha. rewrite U517 in Ha.
      (* at T = 0 the footprint is empty: the entry's bytes are a tmp block (the new table) *)
      left. split; [|lia]. right; right; left. exists res, ATABLE.
      split; [exact HinN | split; [exact HnotIn | revert Ha HED2; clear; intros; lia]]. }
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249g in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U257g in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U310g in Ha;
      apply HGin; apply inG_cons; right; apply inG_cons; left;
      unfold in_zr; cbn [fst snd]; lia |].
    apply awr_ok_x_of0. ra_awr_tacF U2g U38g U513g HFA4' fpos F. }
  pres_upd PRES4.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msU
  | st_ok _ _ _ (restrict _ ?msx) => rename msx into msU
  end.
  (* ---- the lock as the unlock call finds it: held since the lock call (word 4 = 16, words 0 and 8 zero), and
     kept by every step since - three runs, the realloc (the lock is an image byte of G, which its acall_kept
     keeps), two runs, the memset and the run after it ---- *)
  destruct Hkept4 as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
  assert (HWL : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (res + req_size ATABLE <= 65536 \/ 6270976 <= res) /\
                (res <= res + AENT * 0 /\ res + AENT * 0 + 56 <= res + req_size ATABLE) /\
                (rg_lock RG + 12 <= rg_nsrc RG \/ rg_nsrc RG + 4 <= rg_lock RG) /\
                (rg_lock RG + 12 <= rg_capsrc RG \/ rg_capsrc RG + 4 <= rg_lock RG) /\
                (rg_lock RG + 12 <= rg_src RG \/ rg_src RG + 8 <= rg_lock RG)).
  { split; [exact HWOUT|]. split; [exact HNoff|]. split; [exact HED2|].
    ra_zsep_pick HSEPG 4%nat 5%nat P45. ra_zsep_pick HSEPG 4%nat 6%nat P46. ra_zsep_pick HSEPG 4%nat 7%nat P47.
    split; [exact P45|]. split; [exact P46|exact P47]. }
  assert (KEEPL : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
    aview SEGS (w_H W4) (ms_mem msU) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha.
    assert (HaL : rg_lock RG <= a < rg_lock RG + 12 /\ 65536 <= rg_lock RG /\ rg_lock RG + 12 <= 6270976)
    by (revert Ha BLK; clear; intros; lia).
    assert (HL64 : 0 <= a < 2 ^ 64) by (revert HaL; clear; intros; lia).
    assert (HLsc : ~ (spZ regs + -128 - ESTACK <= a < spZ regs + -128))
    by (revert HaL Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia).
    assert (HLin : inG (RA_G RG) a) by (apply ra_lock_in; revert Ha; clear; intros; lia).
    etransitivity; [exact (aview_kept_out Eg _ (w_H W4) _ _ HFr7 a HL64
      ltac:(ra_out HaL HWL U2g U38g U513g U249g U257g U310g U517))|].
    etransitivity; [exact (Hfr5 a HL64 ltac:(revert HaL HWL; clear; intros; lia) HLsc)|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr6 a HL64
      ltac:(ra_out HaL HWL U2e U38e U513e U249e U257e U248e U248e))|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr5 a HL64
      ltac:(ra_out HaL HWL U2e U38e U513e U312e U311e U248e U248e))|].
    etransitivity; [exact (KA3 a (proj1 (HG a (HGin a HLin))) (proj1 (proj2 (HG a (HGin a HLin)))) (HGerr a HLin))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr4 a HL64
      ltac:(ra_out HaL HWL U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr3 a HL64
      ltac:(ra_out HaL HWL U2d U38d U513d U249 U257 U248 U248))|].
    exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 a HL64
      ltac:(ra_out HaL HWL U2d U38d U513d U249 U257 U248 U248)). }
  assert (LK0u : val_mem SEGS (mrestrict (w_H W4) (ms_mem msU)) (rg_lock RG) 4 0).
  { apply (val_mem_kept SEGS (w_H W) (w_H W4) (ms_mem ms1) (ms_mem msU) (rg_lock RG) 4 0); [|exact LK0].
    intros j Hj. cbn in Hj. rewrite (KEEPL (rg_lock RG + j) ltac:(revert Hj BLK; clear; intros; lia)).
    apply Hfr3; [revert Hj BLK; clear; intros; lia | revert Hj; clear; intros; lia
      | revert Hj BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia]. }
  assert (LK8u : val_mem SEGS (mrestrict (w_H W4) (ms_mem msU)) (rg_lock RG + 8) 4 0).
  { apply (val_mem_kept SEGS (w_H W) (w_H W4) (ms_mem ms1) (ms_mem msU) (rg_lock RG + 8) 4 0); [|exact LK8].
    intros j Hj. cbn in Hj. rewrite (KEEPL (rg_lock RG + 8 + j) ltac:(revert Hj BLK; clear; intros; lia)).
    apply Hfr3; [revert Hj BLK; clear; intros; lia | revert Hj; clear; intros; lia
      | revert Hj BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia]. }
  assert (LK4u : val_mem SEGS (mrestrict (w_H W4) (ms_mem msU)) (rg_lock RG + 4) 4 16).
  { apply (val_mem_kept SEGS (w_H W) (w_H W4) mem3 (ms_mem msU) (rg_lock RG + 4) 4 16); [|exact HLK3].
    intros j Hj. cbn in Hj. exact (KEEPL (rg_lock RG + 4 + j) ltac:(revert Hj BLK; clear; intros; lia)). }
  (* ---- pthread_mutex_unlock (&g_lock) ---- *)
  pmkst HS.
  prreg HS (1%bv : bv 5) UQRA. prreg HS (2%bv : bv 5) UQSP. prreg HS (3%bv : bv 5) UQGP. prreg HS (4%bv : bv 5) UQTP.
  prreg HS (10%bv : bv 5) UQA0.
  assert (HSPu : spZ (ms_regs msU) = spZ regs + -128).
  { unfold spZ at 1. rewrite UQSP, U2g.
    rewrite unsigned_lit_small by (revert Hslo Hshi H47 Hceil Hstk0 C1; clear; unfold spZ; intros; lia). lia. }
  assert (UQA0' : getr (ms_regs msU) 10 = w64 (rg_lock RG)).
  { rewrite UQA0. change 247%nat with (A_OBJ 6).
    rewrite (img_env_atomP Eg (A_OBJ 6) HEIg ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). rewrite HV6. reflexivity. }
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HARu.
  assert (LKVu : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W4) (ms_mem msU) a <> None).
  { intros a Ha. unfold aview.
    destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
    - pose proof (LK0u (Z.to_nat (a - rg_lock RG)) ltac:(revert Ha h1; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert Ha; clear; intros; lia).
      replace (rg_lock RG + (a - rg_lock RG)) with a in X by ring. rewrite X. discriminate.
    - pose proof (LK4u (Z.to_nat (a - (rg_lock RG + 4))) ltac:(revert h1 h2; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert h1; clear; intros; lia).
      replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by ring. rewrite X. discriminate.
    - pose proof (LK8u (Z.to_nat (a - (rg_lock RG + 8))) ltac:(revert Ha h2; clear; intros; lia)) as X.
      rewrite Z2Nat.id in X by (revert h2; clear; intros; lia).
      replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by ring. rewrite X. discriminate. }
  assert (HNOWNu : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly4 S4 a).
  { intros a Ha Ho. destruct (HG a (HGin a (ra_lock_in a Ha))) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly4 S4 _ W4 (ms_mem msU) _ a HARu Hi) Ho). }
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
      (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
         getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W4) mem') (rg_lock RG + 4) 4 0)
      W4 _ _ RA_STK (spZ regs) (ra_FP 0 []) ly S Hp W mem md _ _ _ _ _ _ (-128) _ HG eq_refl HJ5).
    - exact HSPu.
    - reflexivity.
    - first [clear; lia | lia].
    - first [clear; lia | lia].
    - rewrite WS, Hes. clear. lia.
    - rewrite UQGP, OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite UQTP, OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - exact UQRA.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
      destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
    - intros a Ha _. exact (LKVu a ltac:(revert Ha; clear; intros; lia)).
    - intros a Ha HnG. exfalso. apply HnG. apply HGin. apply ra_lock_in. revert Ha; clear; intros; lia.
    - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
      + exact UQA0'.
      + revert BLK; clear; intros; lia.
      + exact HLA.
      + revert BLK; clear; intros; lia.
      + exact LK0u.
      + exact LK4u.
      + exact LK8u.
      + intros a Ha. split; [exact (LKVu a Ha)|]. rewrite HSPu.
        revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia.
      + intros a Ha. split; [|split].
        * apply GW; [apply ra_lock_in; revert Ha; clear; intros; lia|].
          apply (hidden_not_img SEGS W4 (Z_to_bv 64 a)). rewrite unsigned_lit_small by (revert Ha BLK; clear; intros; lia).
          exact (proj1 (HG a (HGin a (ra_lock_in a ltac:(revert Ha; clear; intros; lia))))).
        * exact (HNOWNu a ltac:(revert Ha; clear; intros; lia)).
        * rewrite HSPu. revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia.
      + intros a Ha HKx. exact (proj2 (proj2 (HG a (HGin a (ra_lock_in a ltac:(revert Ha; clear; intros; lia))))) (proj1 (proj2 HKx))). }
  cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & (HUA0 & HUL6) & Hfr6 & Hpres6).
  pose proof (pres_trans _ _ _ _ PRES4
    (fun a (_ : in_img SEGS a) (H : apresent (w_H W4) (ms_mem msU) a) => Hpres6 a H)) as P.
  clear PRES4; rename P into PRES4.
  (* ---- back in relay_add, the lock free: rebuild the state, keeping all ten regions ---- *)
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARu) as (Kc7a & Ku7a & Kg7a & Kgu7a).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR6) as (Kc7 & Ku7 & Kg7 & Kgu7).
  rewrite HBgot, HBcell in Kg7a, Kg7. rewrite HBcell in Kc7a, Kc7. rewrite (palf_got_uar B TLF) in Kgu7a, Kgu7.
  jafter_call_keep_pi HS 98%nat regs6 (mrestrict (w_H W4) mem6) HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat HS8.
  match type of HS8 with ?ty -> _ => assert (HRK : ty); [|specialize (HS8 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | | | | apply Forall_nil].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 517 (res + AENT * 0)); [exact U517 | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha HDB C1b; clear; intros; lia
      | revert Ha HWL BLK; clear; intros; lia
      | revert Ha HDB Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 249 (rg_src RG)); [exact U249g | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha BSR; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BSR Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 257 (rg_capsrc RG)); [exact U257g | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha BCS; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BCS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 310 (rg_nsrc RG + 704)); [exact U310g | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha BNS; clear; intros; lia
      | revert Ha HWL; clear; intros; lia
      | revert Ha BNS Hslo Hceil Hstk0 C1; clear; unfold ESTACK; intros; lia ].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 38 F); [exact U38g | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha HF4096 HFceil HFhigh C1; clear; intros; lia
      | revert Ha HWL BLK; clear; intros; lia
      | revert Ha HF4096 HFceil HFhigh HFimg Hslo Hshi H47 Hceil Hstk0 C1 WS Hes; clear; intros; lia ].
    - apply (region_kept_aview Eg (w_H W4) (ms_mem msU) mem6 2 (spZ regs)); [exact U2g | | exact Hpres6].
      intros a Ha. apply Hfr6;
      [ revert Ha Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; intros; lia
      | revert Ha; clear; intros; lia ].
    - apply (region_kept_val_at Eg _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
      [exact U241g | exact (val_mem_of_rdword SEGS _ _ _ _ Kg7a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg7) | lia].
    - apply (region_kept_val_at Eg _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
      [exact U273g | exact (val_mem_of_rdword SEGS _ _ _ _ Kc7a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc7) | lia].
    - apply (region_kept_val_at Eg _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
      [exact U242g | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu7a) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu7) | lia].
    - apply (region_kept_val_at Eg _ _ 32 (as_uar_cell B) 4 1);
      [exact U32g | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku7a) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku7) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS8. rename HS8 into HS.
  remember (havoc Eg 98 (map (getr regs6) CLOB)) as Eh eqn:HEh in HS.
  assert (HEIh : img_env VAL A_LIM Eh) by (rewrite HEh; apply img_env_havoc; [exact HEIg | cbv; lia]).
  assert (OLDh : forall m, (m < 98)%nat -> ew Eh m = ew Eg m) by (intros m Hm; rewrite HEh; apply YN3v.ew_havoc_old; exact Hm).
  assert (ABVh : forall m, (114 <= m)%nat -> ew Eh m = ew Eg m) by (intros m Hm; rewrite HEh; apply ew_havoc_above; cbn; lia).
  assert (HAEh : env_agree 32 (Ereg regs ra_extra) Eh) by (rewrite HEh; apply env_agree_havoc_ge; [cbv; lia | exact HAEg]).
  clear HEh.
  (* ---- g_wake[1] at the bltz: -1 since the entry (awake_at), kept by every step - relay_add reads it, never
     writes it.  Arm 2's chain has the realloc in it, where g_wake is kept as an image byte off the owned
     statics and off errno (HWKI / HWKO and the placement's apartness from errno). ---- *)
  pose proof (proj1 (Forall_forall _ _) HIG (rg_wake RG + 4, 4) ltac:(do 4 right; left; reflexivity)) as BWK.
  cbn [fst snd] in BWK.
  assert (HWK : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (res + req_size ATABLE <= 65536 \/ 6270976 <= res) /\
                (res <= res + AENT * 0 /\ res + AENT * 0 + 56 <= res + req_size ATABLE) /\
                (rg_lock RG + 12 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_lock RG) /\
                (rg_nsrc RG + 4 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_nsrc RG) /\
                (rg_capsrc RG + 4 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_capsrc RG) /\
                (rg_src RG + 8 <= rg_wake RG + 4 \/ rg_wake RG + 4 + 4 <= rg_src RG)).
  { split; [exact HWOUT|]. split; [exact HNoff|]. split; [exact HED2|].
    ra_zsep_pick HSEPG 4%nat 9%nat Q1. ra_zsep_pick HSEPG 5%nat 9%nat Q2.
    ra_zsep_pick HSEPG 6%nat 9%nat Q3. ra_zsep_pick HSEPG 7%nat 9%nat Q4.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|exact Q4]. }
  ra_zsep_pick HSEPG 8%nat 9%nat QWE.
  assert (NOWK : forall ly0 S0 Hq0 W0 m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 ->
    forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> ~ aowned B ly0 S0 a).
  { intros ly0 S0 Hq0 W0 m0 md0 HA a Ha Ho.
    pose proof (HWKI (a - (rg_wake RG + 4)) ltac:(revert Ha; clear; intros; lia)) as Hi.
    pose proof (HWKO (a - (rg_wake RG + 4)) ltac:(revert Ha; clear; intros; lia)) as Hno.
    replace (rg_wake RG + 4 + (a - (rg_wake RG + 4))) with a in Hi, Hno by ring.
    exact (Hno (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HA Hi) Ho)). }
  assert (WKC : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
    aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W) mem a).
  { intros a Ha.
    assert (HaW : rg_wake RG + 4 <= a < rg_wake RG + 8 /\ 65536 <= rg_wake RG + 4 /\ rg_wake RG + 4 + 4 <= 6270976)
    by (revert Ha BWK; clear; intros; lia).
    assert (HW64 : 0 <= a < 2 ^ 64) by (revert HaW; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= a < spZ regs + -128))
    by (revert HaW Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia).
    assert (HWIa : in_img SEGS a).
    { pose proof (HWKI (a - (rg_wake RG + 4)) ltac:(revert HaW; clear; intros; lia)) as Hi.
      replace (rg_wake RG + 4 + (a - (rg_wake RG + 4))) with a in Hi by ring. exact Hi. }
    assert (HWOa : ~ Exists (in_zr a) (as_owned_static B)).
    { pose proof (HWKO (a - (rg_wake RG + 4)) ltac:(revert HaW; clear; intros; lia)) as Hno.
      replace (rg_wake RG + 4 + (a - (rg_wake RG + 4))) with a in Hno by ring. exact Hno. }
    assert (HWEa : ~ (as_errno B <= a < as_errno B + 4)) by (revert HaW QWE; clear; intros; lia).
    etransitivity; [exact (Hfr6 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eg _ (w_H W4) _ _ HFr7 a HW64
      ltac:(ra_out HaW HWK U2g U38g U513g U249g U257g U310g U517))|].
    etransitivity; [exact (Hfr5 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr6 a HW64
      ltac:(ra_out HaW HWK U2e U38e U513e U249e U257e U248e U248e))|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr5 a HW64
      ltac:(ra_out HaW HWK U2e U38e U513e U312e U311e U248e U248e))|].
    etransitivity; [exact (KA3 a HWIa HWOa HWEa)|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr4 a HW64
      ltac:(ra_out HaW HWK U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr3 a HW64
      ltac:(ra_out HaW HWK U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 a HW64
      ltac:(ra_out HaW HWK U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (Hfr3 a HW64 ltac:(revert HaW HWK; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 a HW64
      ltac:(ra_out HaW HWK U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 a HW64
      ltac:(ra_out HaW HWK U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (HRAW a HW64 (NOWK _ _ _ _ _ _ HARa a Ha) (NOWK _ _ _ _ _ _ HARb a Ha) HWCW)|].
    exact (aview_kept_out E _ (w_H W) _ _ HFr a HW64 ltac:(ra_out HaW HWK Usp Usp Usp Usp Usp Usp Usp)). }
  assert (WK5 : val_mem SEGS (mrestrict (w_H W4) mem6) (rg_wake RG + 4) 4 (2 ^ 32 - 1)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W4) mem mem6 (rg_wake RG + 4) 4 (2 ^ 32 - 1)); [|exact HWAKE].
    intros k Hk. cbn in Hk. exact (WKC (rg_wake RG + 4 + k) ltac:(revert Hk; clear; intros; lia)). }
  (* ---- the regions for the rest: the entry's and the globals' windows closed (no more stores to them; a plain
     run writes only awr bytes), the fake frame's window opened again (the calls kept it read-only) ---- *)
  assert (U2h : bv_unsigned (ew Eh 2) = spZ regs) by (rewrite OLDh by lia; exact U2g).
  assert (U38h : bv_unsigned (ew Eh 38) = F) by (rewrite OLDh by lia; exact U38g).
  assert (U513h : bv_unsigned (ew Eh 513) = SB + F / 8) by (rewrite ABVh by lia; exact U513g).
  assert (U512h : bv_unsigned (ew Eh 512) = FL) by (rewrite ABVh, OLDg, ABVf, ABVe, OLDd, ABVc by lia; exact U512).
  assert (U517h : bv_unsigned (ew Eh 517) = res + AENT * 0) by (rewrite ABVh by lia; exact U517).
  assert (U249h : bv_unsigned (ew Eh 249) = rg_src RG) by (rewrite ABVh by lia; exact U249g).
  assert (U257h : bv_unsigned (ew Eh 257) = rg_capsrc RG) by (rewrite ABVh by lia; exact U257g).
  assert (U310h : bv_unsigned (ew Eh 310) = rg_nsrc RG + 704) by (rewrite ABVh by lia; exact U310g).
  assert (U241h : bv_unsigned (ew Eh 241) = VAL (A_OBJ 0)) by (rewrite ABVh by lia; exact U241g).
  assert (U242h : bv_unsigned (ew Eh 242) = VAL (A_OBJ 1)) by (rewrite ABVh by lia; exact U242g).
  assert (U273h : bv_unsigned (ew Eh 273) = VAL (A_OBJ 32)) by (rewrite ABVh by lia; exact U273g).
  assert (U32h : bv_unsigned (ew Eh 32) = as_uar_cell B) by (rewrite OLDh by lia; exact U32g).
  ra_reshape HS 0%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 1%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 2%nat 0 0 ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  ra_reshape HS 3%nat (-704) (-704) ltac:(intros o Ho; exfalso; revert Ho; clear; intros; lia).
  destruct (alx_frames _ _ _ LAWS ly4 S4 _ W4 mem6 md6 0 fpos HAR6 Hfin4) as (_ & _ & HFpres6 & HFSpres6).
  change (fs_frame_bytes 0) with 64 in HFpres6, HFSpres6. change (64 / 8) with 8 in HFSpres6.
  rewrite HFA4' in HFpres6, HFSpres6.
  ra_reshape HS 4%nat 0 64 ltac:(intros o Ho; cbn [base_val]; rewrite U38h; apply (apresent_writable SEGS);
    exact (proj1 (HFpres6 (F + o) ltac:(revert Ho; clear; intros; lia)))).
  (* the fake frame's shadow, writable again (the release poisons it), no chunks *)
  pose proof (st_ok_pi_add_region Eh _ _ (fshadow_region 513 0 0 8 []) HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok, fshadow_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    change (fs_frame_bytes 0 / 8) with 8; rewrite U513h;
    split; [revert HF8lo HF8hi; clear; unfold SB; intros; lia|]; split; [revert HF8lo HF8hi; clear; unfold SB; intros; lia|];
    split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres6; rewrite <- SB_SHADOW_OFF in HFSpres6;
    apply (proj1 (HFSpres6 o ltac:(revert Ho; clear; intros; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0 / 8) with 8;
    rewrite U513h, U517h, U249h, U257h, U310h, U38h, U2h, U241h, U273h, U242h, U32h;
    repeat split;
    first [ solve [revert HTapp2 HED2 HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia]
          | solve [revert BSR BCS BNS HF8lo; clear; unfold SB; intros; lia]
          | solve [revert HFapp HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia]
          | solve [revert Hslo Hshi H47 Hceil Hstk0 C1 WS HF8hi; clear; unfold SB; intros; lia]
          | solve [revert HgotR HcellR HguR HuR PV0 PV1 PV32 HF8lo; clear; unfold SB; intros; lia]
          | lazymatch goal with |- ?g => idtac "SH-DISJ" g; fail end ])) as HS9.
  clear HS; rename HS9 into HS. norm_ss HS.
  (* g_wake[1], read-only, holding 2^32 - 1 *)
  assert (U245h : bv_unsigned (ew Eh 245) = rg_wake RG + 4).
  { change 245%nat with (A_OBJ 4). rewrite <- HV4. exact (HEIh (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). }
  pose proof (st_ok_pi_add_region Eh _ _ (YP09.mkRegion (Some 245%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit (2 ^ 32 - 1)))])
    HS ltac:(vm_compute; reflexivity)
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U245h; split; [revert BWK; clear; intros; lia|]; split; [revert BWK; clear; intros; lia|]; split;
    [ intros o Ho; exfalso; revert Ho; clear; intros; lia
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Eh _ (rg_wake RG + 4) 0 4 (SLit (2 ^ 32 - 1)) (2 ^ 32 - 1));
      [ reflexivity | clear; zside | clear; zside | rewrite Z.add_0_r; exact WK5 ] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U245h, U513h, U517h, U249h, U257h, U310h, U38h, U2h, U241h, U273h, U242h, U32h;
    ra_zsep_pick HSEPG 0%nat 9%nat W0; ra_zsep_pick HSEPG 1%nat 9%nat W1; ra_zsep_pick HSEPG 2%nat 9%nat W2;
    ra_zsep_pick HSEPG 3%nat 9%nat W3;
    repeat split;
    first [ solve [revert HWK BWK; clear; intros; lia]
          | solve [revert BWK HF8lo; clear; unfold SB; intros; lia]
          | solve [revert W0; clear; intros; lia] | solve [revert W1; clear; intros; lia]
          | solve [revert W2; clear; intros; lia] | solve [revert W3; clear; intros; lia]
          | lazymatch goal with |- ?g => idtac "WK-DISJ" g; fail end ])) as HS9.
  clear HS; rename HS9 into HS. norm_ss HS.
  (* ---- 0x82afc-0x82b10, a plain run on the inner journal: unpoison the local c (shadow byte 4 := 1), c = 0,
     read g_wake[1]; it stops at `bltz a0` ---- *)
  destruct HJ6 as (HSTK6 & HXO6 & (memS6 & HJi6 & HAG6) & HOUT6). rewrite !Z.add_0_r in HJi6.
  paj_run_sh_x RUNPR HS HJi6.
  { intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      lazymatch type of Hr with
      | context [ew _ 2] => rewrite U2h in Hr; left; revert Hr; clear; unfold RA_STK, ASTACK, RA_FRAME; intros; lia
      | context [ew _ 38] => rewrite U38h in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        rewrite HFA4'; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd];
        revert Hr; clear; intros; lia
      | context [ew _ 513] => rewrite U513h in Hr; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        rewrite HFA4'; change (fs_frame_bytes 0) with 64;
        right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
        revert Hr; clear; intros; lia
      | _ => exfalso; revert Hr; clear; intros; lia
      end
    | ]).
    destruct Hin. }
  pres_upd PRES4.
  (* the run went on through `bltz` (taken: g_wake[1] = -1 is known), the retired magic, `beqz s2` (s2 = F) and the
     shadow poison, and stops at the flag store `sb zero,0(a0)`, a0 = FL: seat the flag byte, then the release *)
  lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
  destruct (FFL _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin4) as (HFLp6 & HFLo6 & (HFLapp6 & HFLimg6) & (HFL40966 & HFLz6 & HFLc6)) end.
  lazymatch goal with HJx : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
  destruct (alx_frames _ _ _ LAWS _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin4) as (_ & _ & HFpres7 & HFSpres7) end.
  change (fs_frame_bytes 0) with 64 in HFLp6, HFLo6, HFLapp6, HFLimg6, HFL40966, HFLz6, HFLc6, HFpres7, HFSpres7.
  change (64 / 8) with 8 in HFSpres7.
  rewrite HFA4' in HFpres7, HFSpres7.
  assert (HLYF : ly_F ly4 = ly_F ly).
  { pose proof (HFA4 0 0) as X. unfold frame_addr in X. revert X; clear; intros; lia. }
  assert (HFLA : flag_addr ly4 0 fpos = FL).
  { change FL with (flag_addr ly 0 fpos). unfold flag_addr. revert HLYF; clear; intros; lia. }
  rewrite HFLA in HFLp6, HFLo6, HFLapp6, HFLimg6, HFL40966, HFLz6, HFLc6.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U512h; split; [revert HFL40966 HFLc6 C1; clear; intros; lia|]; split; [revert HFL40966 HFLc6 C1; clear; intros; lia|];
    split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by (revert Ho; clear; intros; lia); exact HFLp6)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U512h, U245h, U513h, U517h, U249h, U257h, U310h, U38h, U2h, U241h, U273h, U242h, U32h;
    repeat split;
    first [ solve [revert HFL40966 HFLz6 HFLc6 BSR BCS BNS BWK HgotR HcellR HguR HuR PV0 PV1 PV32
                   Hslo Hshi H47 Hceil Hstk0 C1 WS HF8lo HF8hi HFq HF8 HFceil; clear; unfold zone2, off_img, SB in *; intros; lia]
          | lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
              let Hlt := fresh in let Hge := fresh in let Hlt2 := fresh in let Hge2 := fresh in
              destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; revert Hlt; clear; intros; lia|];
              destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; revert Hge2; clear; intros; lia];
              first [ exact (proj2 (HFpres7 FL ltac:(revert Hge Hlt2; clear; intros; lia)) HFLo6)
                    | exact (proj2 (HTpres2 FL ltac:(revert Hge Hlt2 HED2; clear; intros; lia)) HFLo6) ] end
          | lazymatch goal with |- ?g => idtac "FLAGGOAL" g; fail end ])) as HS9 end.
  clear HS; rename HS9 into HS. norm_ss HS.
  (* ---- the flag store (the fake frame released: stack_free_state), the epilogue, to the ret ---- *)
  paj_run_flag_sh_x RUNFR HS HJi6.
  { first [clear; lia | lia]. }
  { intros a (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. rewrite HFLA.
    repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      lazymatch type of Hr with
      | context [ew _ 2] => rewrite U2h in Hr; left; left; revert Hr; clear; unfold RA_STK, ASTACK, RA_FRAME; intros; lia
      | context [ew _ 512] => rewrite U512h in Hr; right; revert Hr; clear; intros; lia
      | context [ew _ 38] => rewrite U38h in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        rewrite HFA4'; change (fs_frame_bytes 0) with 64; left; unfold in_zr; cbn [fst snd];
        revert Hr; clear; intros; lia
      | context [ew _ 513] => rewrite U513h in Hr; left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
        rewrite HFA4'; change (fs_frame_bytes 0) with 64;
        right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
        revert Hr; clear; intros; lia
      | _ => exfalso; revert Hr; clear; intros; lia
      end
    | ]).
    destruct Hin. }
  { intros msr HSr. rewrite HFLA.
    lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512h
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
    rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
  pres_upd PRES4.
  (* ---- what the last two runs (the release and the flag store) keep: every byte but the frame, the fake frame,
     its shadow and its flag ---- *)
  assert (KEND : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> ~ (F <= a < F + 64) ->
    ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL -> aview SEGS (w_H W4) (ms_mem ms7) a = aview SEGS (w_H W4) mem6 a).
  { intros a Ha K1 K2 K3 K4.
    assert (NW : forall E0 rs, (forall r, In r rs -> ~ (base_val E0 (YP09.r_base r) + YP09.r_wlo r <= a < base_val E0 (YP09.r_base r) + YP09.r_whi r)) ->
      ~ in_wrange E0 rs a) by (intros E0 rs Hn (r & Hin & Hr); exact (Hn r Hin Hr)).
    rewrite (aview_kept_out Eh _ (w_H W4) _ _ HFr9 a Ha).
    2:{ apply NW. intros r Hin.
        lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
        cbn [In] in Hin.
        repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2h, ?U38h, ?U513h, ?U512h;
          revert K1 K2 K3 K4; clear; intros; lia | ]).
        destruct Hin. }
    exact (aview_kept_out Eh _ (w_H W4) _ _ HFr8 a Ha ltac:(apply NW; intros r Hin;
        lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
        cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2h, ?U38h, ?U513h, ?U512h;
          revert K1 K2 K3 K4; clear; intros; lia | ]);
        destruct Hin)). }
  (* ---- the values the regions hold at the ret: g_src = res, g_capsrc = 16, g_nsrc = 1, s->fd = fd ---- *)
  assert (E70h : ew Eh 70 = Z_to_bv 64 res) by (rewrite OLDh by lia; exact E70g).
  assert (E514h : ew Eh 514 = Z_to_bv 64 0) by (rewrite ABVh by lia; exact E514g).
  assert (U10h : ew Eh 10 = Z_to_bv 64 fd)
  by (rewrite OLDh, OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
  assert (SXnh : bv_unsigned (sv_denot Eh (SExt true 32 (SOff 514 0))) = 0).
  { rewrite U_sext32'. change (bv_unsigned (sv_denot Eh (SOff 514 0))) with (U Eh (SOff 514 0)).
    rewrite (U_atom Eh 514 _ E514h) by (clear; lia). apply sx32_small. clear; lia. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth Ex ssx msx 3 _ HS eq_refl) as RQ3;
    pose proof (st_ok_pi_region_nth Ex ssx msx 4 _ HS eq_refl) as RQ4;
    pose proof (st_ok_pi_region_nth Ex ssx msx 5 _ HS eq_refl) as RQ5;
    pose proof (st_ok_pi_region_nth Ex ssx msx 6 _ HS eq_refl) as RQ6 end.
  lazymatch type of RQ4 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eh m n (rg_src RG) cs lo hi wlo whi 0 8%N (SOff 70 0) res RQ4 U249h ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E70h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(revert HresB; clear; intros; cbn; lia) ltac:(cbn; lia)) as VSRC end.
  lazymatch type of RQ5 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eh m n (rg_capsrc RG) cs lo hi wlo whi 0 4%N (SLit 16) 16 RQ5 U257h ltac:(left; reflexivity)
      ltac:(first [reflexivity | cbn [sv_denot]; reflexivity])
      ltac:(cbn; lia) ltac:(cbn; lia)) as VCAP end.
  lazymatch type of RQ3 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eh m n (res + AENT * 0) cs lo hi wlo whi 0 4%N (SOff 10 0) fd RQ3 U517h
      ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite U10h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(revert Hpos Rfd; clear; intros; cbn; lia) ltac:(cbn; lia)) as VENT end.
  assert (HNS1 : sv_denot Eh (SAlu ALU_ADD (SExt true 32 (SOff 514 0)) (SLit 1)) = Z_to_bv 64 1).
  { apply bv_eq.
    lazymatch goal with |- bv_unsigned (sv_denot Eh ?x) = _ => change (U Eh x = bv_unsigned (Z_to_bv 64 1)) end.
    rewrite U_SAlu. cbn [zalu_raw].
    change (U Eh (SExt true 32 (SOff 514 0))) with (bv_unsigned (sv_denot Eh (SExt true 32 (SOff 514 0)))).
    rewrite SXnh, U_lit by lia.
    first [ rewrite (ZC (0 + 1)) by (clear; lia) | rewrite (ZC 1) by (clear; lia) ].
    rewrite unsigned_lit_small by (clear; lia). reflexivity. }
  lazymatch type of RQ6 with region_ok _ _ ?m (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region Eh m n (rg_nsrc RG + 704) cs lo hi wlo whi (-704) 4%N
      (SAlu ALU_ADD (SExt true 32 (SOff 514 0)) (SLit 1)) 1 RQ6 U310h ltac:(left; reflexivity)
      HNS1 ltac:(clear; cbn; lia) ltac:(cbn; lia)) as VNS end.
  rewrite Z.add_0_r in VSRC, VCAP, VENT. replace (rg_nsrc RG + 704 + -704) with (rg_nsrc RG) in VNS by ring.
  (* ---- facts for ra_post.  (1) errno's four bytes, kept from the entry to the ret.  Across the realloc they are
     kept by the RULE'S OWN errno clause (Herr4), not by its acall_kept, which excepts errno ---- *)
  pose proof (proj1 (Forall_forall _ _) HIG (as_errno B, 4) ltac:(do 5 right; left; reflexivity)) as BE2.
  cbn [fst snd] in BE2.
  assert (HWE2 : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                 (res + req_size ATABLE <= 65536 \/ 6270976 <= res) /\
                 (res <= res + AENT * 0 /\ res + AENT * 0 + 56 <= res + req_size ATABLE) /\
                 (rg_lock RG + 12 <= as_errno B \/ as_errno B + 4 <= rg_lock RG) /\
                 (rg_nsrc RG + 4 <= as_errno B \/ as_errno B + 4 <= rg_nsrc RG) /\
                 (rg_capsrc RG + 4 <= as_errno B \/ as_errno B + 4 <= rg_capsrc RG) /\
                 (rg_src RG + 8 <= as_errno B \/ as_errno B + 4 <= rg_src RG)).
  { split; [exact HWOUT|]. split; [exact HNoff|]. split; [exact HED2|].
    ra_zsep_pick HSEPG 4%nat 8%nat Q1. ra_zsep_pick HSEPG 5%nat 8%nat Q2.
    ra_zsep_pick HSEPG 6%nat 8%nat Q3. ra_zsep_pick HSEPG 7%nat 8%nat Q4.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|exact Q4]. }
  assert (ERC : forall i, 0 <= i < 4 ->
    aview SEGS (w_H W4) (ms_mem ms7) (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
  { intros i Hi.
    assert (HaW : as_errno B <= as_errno B + i < as_errno B + 4 /\ 65536 <= as_errno B /\ as_errno B + 4 <= 6270976)
    by (revert Hi BE2; clear; intros; lia).
    assert (HW64 : 0 <= as_errno B + i < 2 ^ 64) by (revert HaW; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= as_errno B + i < spZ regs + -128))
    by (revert HaW Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia).
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + i) ltac:(clear - Hi; lia)) as HaI.
    etransitivity.
    { apply KEND; [exact HW64 | revert HaW HWOUT; clear; intros; lia | revert HaW HFimg; clear; intros; lia
                  | revert HaW HWOUT; clear; intros; lia | intros Heq; apply HFLimg6; rewrite <- Heq; exact HaI]. }
    etransitivity; [exact (Hfr6 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eg _ (w_H W4) _ _ HFr7 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2g U38g U513g U249g U257g U310g U517))|].
    etransitivity; [exact (Hfr5 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr6 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2e U38e U513e U249e U257e U248e U248e))|].
    etransitivity; [exact (aview_kept_out Ee _ (w_H W4) _ _ HFr5 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2e U38e U513e U312e U311e U248e U248e))|].
    etransitivity; [exact (Herr4 i Hi)|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr4 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr3 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (aview_kept_out Ed _ (w_H W) _ _ HFr2 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2d U38d U513d U249 U257 U248 U248))|].
    etransitivity; [exact (Hfr3 (as_errno B + i) HW64 ltac:(revert HaW HWE2; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr1 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (aview_kept_out Eb _ (w_H W) _ _ HFr0 (as_errno B + i) HW64
      ltac:(ra_out HaW HWE2 U2b U38 U513 U2b U2b U2b U2b))|].
    etransitivity; [exact (HRAW (as_errno B + i) HW64
      (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARa HEO i Hi)
      (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARb HEO i Hi) HWCW)|].
    exact (aview_kept_out E _ (w_H W) _ _ HFr (as_errno B + i) HW64 ltac:(ra_out HaW HWE2 Usp Usp Usp Usp Usp Usp Usp)). }
  idtac "A2-ERRNO".
  (* (2) the lock: words 0 and 8 from the unlock call's entry (LK0u / LK8u), word 4 from its post (HUL6) *)
  assert (LKEND : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
    aview SEGS (w_H W4) (ms_mem ms7) a = aview SEGS (w_H W4) mem6 a).
  { intros a Ha.
    assert (HaI : in_img SEGS a) by exact (proj1 (HG a (HGin a (ra_lock_in a Ha)))).
    apply KEND; [revert Ha BLK; clear; intros; lia | revert Ha BLK HWOUT; clear; intros; lia
                | revert Ha BLK HFimg; clear; intros; lia | revert Ha BLK HWOUT; clear; intros; lia
                | intros Heq; apply HFLimg6; rewrite <- Heq; exact HaI]. }
  assert (LKU : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W4) (ms_mem msU) a).
  { intros a Ha Hn. apply (Hfr6 a ltac:(revert Ha BLK; clear; intros; lia) Hn).
    revert Ha BLK Hslo Hshi H47 Hceil Hstk0 C1 WS; clear; unfold ESTACK; intros; lia. }
  assert (LKF : alock_at RG W4 (ms_mem ms7) false).
  { unfold alock_at. split; [|split; [|split]].
    - apply (val_mem_kept SEGS (w_H W4) (w_H W4) (ms_mem msU) (ms_mem ms7) (rg_lock RG) 4 0); [|exact LK0u].
      intros j Hj. cbn in Hj. rewrite (LKEND (rg_lock RG + j) ltac:(revert Hj; clear; intros; lia)).
      exact (LKU (rg_lock RG + j) ltac:(revert Hj; clear; intros; lia) ltac:(revert Hj; clear; intros; lia)).
    - apply (val_mem_kept SEGS (w_H W4) (w_H W4) mem6 (ms_mem ms7) (rg_lock RG + 4) 4 0); [|exact HUL6].
      intros j Hj. cbn in Hj. exact (LKEND (rg_lock RG + 4 + j) ltac:(revert Hj; clear; intros; lia)).
    - apply (val_mem_kept SEGS (w_H W4) (w_H W4) (ms_mem msU) (ms_mem ms7) (rg_lock RG + 8) 4 0); [|exact LK8u].
      intros j Hj. cbn in Hj. rewrite (LKEND (rg_lock RG + 8 + j) ltac:(revert Hj; clear; intros; lia)).
      exact (LKU (rg_lock RG + 8 + j) ltac:(revert Hj; clear; intros; lia) ltac:(revert Hj; clear; intros; lia)).
    - intros i Hi. unfold arm. apply GW; [apply ra_lock_in; lia|].
      apply (hidden_not_img SEGS). rewrite unsigned_lit_small.
      + exact (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia))))).
      + pose proof (pa_segs_low (rg_lock RG + i) (proj1 (HG _ (HGin _ (ra_lock_in (rg_lock RG + i) ltac:(lia)))))).
        unfold kLowMemEnd in *. lia. }
  idtac "A2-LOCK".
  (* (3) the new entry's 52 bytes after s->fd: zero since the memset, kept by the run to the unlock (whose entry
     window is s->fd only), the unlock, the release and the flag store *)
  assert (HTSH : res + req_size ATABLE <= SB + F / 8 \/ SB + F / 8 + 8 <= res)
  by (revert HTapp2 HF8lo HF8hi HFq HF8 HFceil C1; clear; unfold SB, in_app, kLowShadowBeg, kHighMemBeg in *; intros; lia).
  assert (HTST : res + req_size ATABLE + 16512 <= spZ regs)
  by (revert HNceil Hslo Hceil Hstk0 WS; clear; intros; lia).
  assert (HZB : (6270976 < spZ regs - 128 /\ (F + 64 <= 65536 \/ 6270976 <= F) /\ 6270976 < SB + F / 8) /\
                (res + req_size ATABLE <= 65536 \/ 6270976 <= res) /\ (res + req_size ATABLE <= F \/ F + 64 <= res) /\
                (res + req_size ATABLE <= SB + F / 8 \/ SB + F / 8 + 8 <= res) /\ res + req_size ATABLE + 16512 <= spZ regs /\
                65536 <= rg_lock RG /\ rg_lock RG + 12 <= 6270976 /\
                65536 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= 6270976 /\ 65536 <= rg_capsrc RG /\ rg_capsrc RG + 4 <= 6270976 /\
                65536 <= rg_src RG /\ rg_src RG + 8 <= 6270976).
  { split; [exact HWOUT|]. split; [exact HNoff|]. split; [exact DFN|]. split; [exact HTSH|]. split; [exact HTST|].
    revert BLK BNS BCS BSR; clear; intros; lia. }
  assert (ZER : forall j, 0 <= j < 52 ->
    aview SEGS (w_H W4) (ms_mem ms7) (res + AENT * 0 + 4 + j) = Some 0).
  { intros j Hj.
    assert (HaZ : res + AENT * 0 + 4 <= res + AENT * 0 + 4 + j < res + AENT * 0 + 56 /\ res <= res + AENT * 0 /\
                  res + AENT * 0 + 56 <= res + req_size ATABLE)
    by (revert Hj HED2; clear; intros; lia).
    assert (HW64 : 0 <= res + AENT * 0 + 4 + j < 2 ^ 64) by (revert HaZ HDB C1b; clear; intros; lia).
    assert (HWCW : ~ (spZ regs + -128 - ESTACK <= res + AENT * 0 + 4 + j < spZ regs + -128))
    by (revert HaZ HZB; clear; unfold ESTACK; intros; lia).
    etransitivity.
    { apply KEND; [exact HW64 | revert HaZ HZB; clear; intros; lia | revert HaZ HZB; clear; intros; lia
                  | revert HaZ HZB; clear; intros; lia
                  | intros Heq; exact (proj2 (HTpres2 FL ltac:(rewrite <- Heq; revert HaZ; clear; intros; lia)) HFLo6) ]. }
    etransitivity; [exact (Hfr6 _ HW64 ltac:(revert HaZ HZB; clear; intros; lia) HWCW)|].
    etransitivity; [exact (aview_kept_out Eg _ (w_H W4) _ _ HFr7 _ HW64
      ltac:(ra_out HaZ HZB U2g U38g U513g U249g U257g U310g U517))|].
    replace (res + AENT * 0 + 4 + j) with (res + AENT * 0 + (4 + j)) by ring.
    rewrite (Hset (4 + j) ltac:(revert Hj; clear; intros; lia)). reflexivity. }
  idtac "A2-ZER".
  assert (GNEW : garr8 SEGS (arm W4 (ms_mem ms7)) (res + AENT * 0) (bzs (entry_bytes (ra_new fd)))).
  { apply (ra_new_entry_garr8 W4 (ms_mem ms7) (res + AENT * 0) fd).
    - split; [exact Hpos | exact (proj2 Rfd)].
    - exact VENT.
    - exact ZER. }
  idtac "A2-GNEW".
  (* (5) the end state: the new table block live and present; the globals writable *)
  assert (EabF4 : ablocks B ly4 (stack_free_state 0 fpos S4) = ablocks B ly4 S4)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  pose proof (proj1 HJi6) as HAR7.
  assert (HinT7 : In (res, ATABLE) (ablocks B ly4 (stack_free_state 0 fpos S4))) by (rewrite EabF4; exact HinN).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ res ATABLE HAR7 HinT7) as (_ & _ & _ & _ & HTpres7 & _).
  assert (GWany : forall m a, inG (RA_G RG) a -> writable_at SEGS (mrestrict (w_H W4) m) a).
  { intros m a Ha. apply GW; [exact Ha|]. apply (hidden_not_img SEGS). rewrite unsigned_lit_small.
    - exact (proj1 (HG _ (HGin _ Ha))).
    - pose proof (pa_segs_low a (proj1 (HG _ (HGin _ Ha)))). unfold kLowMemEnd in *. lia. }
  (* ---- the return ---- *)
  prreg HS (10%bv : bv 5) Rr10. prreg HS (1%bv : bv 5) Rr1.
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold ra_post_xR.
  lazymatch type of HJi6 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Hpx _ _ _ ?kx =>
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyx, Sx, Hpx, r, m, d, kx end end.
  split; [cbn [ms_regs]; rewrite Rr1, OLDh, OLDg, OLDf, OLDe, OLDd, OLDc, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
  split.
  { cbn [ms_mem]. eapply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] RA_STK (spZ regs) (ra_FP 0 []) ly S Hp W mem md []).
    all: [> lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs); exact HJi6 | exact HAG6
         | intros a Ha; lia]. }
  split. { eapply (aregs_preserved_of_st_ok SEGS _ Eh _ _ regs ra_extra HS); [exact HAEh | vm_compute; reflexivity]. }
  split. { intros a Hi Ho He Ha. exact (PRES4 a Hi (PKR a Hi Ho He Ha)). }
  split. { pose proof HJi6 as (_ & _ & _ & _ & _ & Hfr' & _). cbn [app] in Hfr'. exact Hfr'. }
  split.
  { assert (MOseat : mo_le MT S S2 0) by (rewrite ES2; exact (MO_FR S fS2)).
    assert (MOrel : mo_le MT S4 (stack_free_state 0 fpos S4) 0) by (unfold stack_free_state; exact (MO_FR S4 _)).
    pose proof (mle_station MT S S2 S4 0 (mo_malloc MT ATABLE + mo_free MT) MLAW MOseat Hmle4) as M1a.
    pose proof (mle_station MT S S4 (stack_free_state 0 fpos S4) (0 + (mo_malloc MT ATABLE + mo_free MT)) 0 MLAW M1a
      MOrel) as M2a.
    apply (mle_weaken MT S _ _ (ra_cost MT 0) MLAW M2a). unfold ra_cost. cbn [Z.eqb]. clear; lia. }
  split.
  { (* the room: the realloc's post (HRM4), then the fake frame's release (RPF) *)
    unfold stack_free_state. apply RPF. exact HRM4. }
  split. { cbn [ms_mem]. exact LKF. }
  split.
  { right. split; [exact Hpos|]. split.
    - cbn [ms_regs]. rewrite Rr10. reflexivity.
    - exists res. split.
      + eapply (arelay_append B RG ly S W mem ly4 (stack_free_state 0 fpos S4) W4 (ms_mem ms7) 0 res [] fd HREL).
        * exact (proj1 (HNEW Hpos)).
        * exact (proj2 (HNEW Hpos)).
        * split; [exact Hpos | exact (proj2 Rfd)].
        * exact HinT7.
        * intros Hne. exfalso. exact (Hne eq_refl).
        * intros b Hb. rewrite EabF4.
          apply (Permutation_in _ (Permutation_sym (HpermZ eq_refl))). right. rewrite Eab. exact Hb.
        * exact VSRC.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; right; apply inG_cons; right; apply inG_cons; left.
          unfold in_zr; cbn [fst snd]; lia.
        * exact VNS.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; left. unfold in_zr; cbn [fst snd]; lia.
        * exact VCAP.
        * intros i Hi. unfold arm. apply GWany.
          apply inG_cons; right; apply inG_cons; right; apply inG_cons; left. unfold in_zr; cbn [fst snd]; lia.
        * exact GNEW.
        * (* the old table bytes: none, the table was empty *)
          intros x Hx. exfalso. cbn [length] in Hx. change (Z.of_nat 0) with 0 in Hx.
          revert Hx; clear; unfold AENT; intros; lia.
        * (* the rest of the table: present, so visible *)
          intros x Hx. cbn [length] in Hx. change (Z.of_nat 0) with 0 in Hx.
          apply (aview_some_of_apresent SEGS).
          exact (proj1 (HTpres7 x ltac:(revert Hx HRQ; clear; unfold AENT, ATABLE; intros; lia))).
        * (* the old entries' footprints: none *)
          intros r Hr. destruct Hr.
      + left. split; [reflexivity|].
        rewrite EabF4. eapply Permutation_trans; [exact (HpermZ eq_refl)|]. rewrite Eab. apply Permutation_refl. }
  (* errno *)
  exact ERC.
Qed.
End raR.
(* the strict walk is its R twin at R := wle (route R's rule: one walk text; part 3c removed the temporary
   memnorm premise) *)
Theorem pb_relay_add_x : ra_spec_x B PST ARx MT RP G RG CTX A_relay_addP.
Proof.
eapply pb_relay_add_xR with (R := @wle _) (RO := fun _ => True) (HAD := fun _ _ _ _ _ _ => True);
  first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] | intros; exact I  | apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC ].
Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_relay_add's statement is the
   AR walk's, byte-identical, now a corollary of pb_relay_add_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS; the other
   hypotheses are the AR walk's.  Bridges: W_contract_x ra_spec_x_AR0 (the conclusion); W_sites_x alock_realizes_x_of_AR0
   / aunlock_realizes_x_of_AR0 / aintrin_realizes_x_of_AR0 and W_journal_x arealloc_cf_rule_c_x_of_AR0 (the callees);
   ARi0_hp0 (HP0); W_kit_x AR_imgc / AR_blkn (IMGC / BLKN); W_frame_x WFL_AR at WFx := Wf (as_universe B), and SFREE /
   SMALLOC from model_laws / stack_malloc_progressP as W_frame_x.v's SFREE_AR / SMALLOC_AR prove them; OWNLOW is
   YG0s.v's AR_owned_low_law_ok; the three frame laws (ASM0 / ASF / FFL) at ARi0 from their AR forms, the ghost list
   kept []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM0 : astack_malloc_pres SEGS B 0.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
(* the meter does not charge the fake frame: its seat and its release are set_fs steps, and a set_fs step costs nothing *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HG : gx_ok SEGS B G.
(* relay_add's globals lie in writable segments: writable in every memory where they are not hidden *)
Hypothesis GW : forall (H : word -> bool) (m : word -> option byte) a,
inG (RA_G RG) a -> H (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict H m) a.
(* runtime entries (R5: RT_pthread_mutex_lock.v, RT_pthread_mutex_unlock.v), the allocator's realloc site rule
   (W_journal.v, the live-state instance) and the memset intrinsic (the donor's form, the relocated core) *)
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
(* the allocator rules' caller-context table (W_journal.v Section hc), relay_add's spec's CTX; the realloc rule is
   the _c form, which takes the call's context `In (raZ regsT :: spine ch) CTX` *)
Variable CTX : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX (SIGMA WS_realloc).
(* the instance's malloc ceiling admits the table: MMAX = cf_malloc_max = 2^30 - 2^20 at the instance, an instance fact like AREALLOC *)
Hypothesis HMMAX : ATABLE < MMAX.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA WS_asan_memset).
(* placement: the objects relay_add reads by PLdHi and the kept auipc registers it stores through
   (fuzz_reply.asan: g_lock 0x5d8ac0, g_nsrc 0x5d87a0, g_capsrc 0x5d8800, g_src 0x5d87c0, g_wake + 4 0xa1fa4;
   s8 = 0x5d8a60, s10 = 0x5d8a64, s9 = 0x5d8a70); the pinned placement discharges them by vm_compute *)
Hypothesis HV6 : VAL (A_OBJ 6) = rg_lock RG.
Hypothesis HLA : rg_lock RG mod 4 = 0.
Hypothesis HV7 : VAL (A_OBJ 7) = rg_nsrc RG.
Hypothesis HV16 : VAL (A_OBJ 16) = rg_capsrc RG.
Hypothesis HV8 : VAL (A_OBJ 8) = rg_src RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
Hypothesis HH30 : VAL (A_HI 30) - 704 = rg_nsrc RG.
Hypothesis HH31 : VAL (A_HI 31) - 612 = rg_capsrc RG.
Hypothesis HH32 : VAL (A_HI 32) - 688 = rg_src RG.
(* ... and they lie in the image band (W_relay_finish.v's HIG; vm_compute at the pinned placement) *)
Hypothesis HIG : Forall (fun r => 65536 <= fst r /\ fst r + snd r <= 6270976)
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_capsrc RG, 4); (rg_src RG, 8); (rg_wake RG + 4, 4); (as_errno B, 4)].
(* the INSTANCE fact that errno's four bytes (tp - 164, a writable .bss cell) lie outside as_owned_static - decided
   once by vm_compute against the instance's concrete list; with W_frame.v's errno_not_aowned and
   aj_stack_malloc_pres_at_raw it carries errno's view across the fake-frame seat.  (A walk whose G contains
   G_SL gets this from gx_ok instead; relay_add's G need not contain errno.) *)
Hypothesis HEO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (as_errno B + i)) (as_owned_static B).
(* ... and the same two facts for g_wake[1] (0xa1fa4, a writable .data cell relay_add only READS): its bytes are
   image bytes outside as_owned_static, so the fake-frame seat keeps them (aj_stack_malloc_pres_at_raw); decided
   by vm_compute against the instance's segments and concrete list *)
Hypothesis HWKI : forall i, 0 <= i < 4 -> in_img SEGS (rg_wake RG + 4 + i).
Hypothesis HWKO : forall i, 0 <= i < 4 -> ~ Exists (in_zr (rg_wake RG + 4 + i)) (as_owned_static B).
(* the cells relay_add reads and writes are pairwise apart (the pinned placement decides it by vm_compute at
   fr_globals / PB_fr, as W_relay_finish.v's HSEPG does) *)
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 1), 8); (VAL (A_OBJ 32), 8); (as_uar_cell B, 4);
 (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_capsrc RG, 4); (rg_src RG, 8); (as_errno B, 4); (rg_wake RG + 4, 4)].
Theorem pb_relay_add : ra_spec B MT G RG CTX A_relay_addP.
Proof.
apply ra_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (WFL : ARx_wf_law SEGS (ARi0 SEGS B) (Wf (as_universe B)))
  by (intros ly S Hp W mem md H; exact (WFL_AR SEGS B ly S Hp W mem md (proj1 H))).
assert (SFREE : forall s cid pos, Wf (as_universe B) s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2)
  by (intros s cid pos HWF Hin; exact (proj2 (ml_stack_free _ ML s cid pos HWF Hin))).
assert (SMALLOC : forall s cid, Wf (as_universe B) s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
  exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
  frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s))
  by (intros s cid HWF Hcid Hcnt; eapply SMALLOC_AR; eassumption).
assert (OWNLOW : ARx_owned_low_law SEGS B (ARi0 SEGS B))
  by (intros ly S Hp W mem md a H Ho; exact (YG0s.AR_owned_low_law_ok SEGS B ly S W mem md a (proj1 H) Ho)).
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; exact (AR_imgc B ly S Hp W mem md (proj1 H))).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; exact (AR_blkn B ly S Hp W mem md p n (proj1 H) Hin)).
assert (ASM0x : astack_malloc_pres_x SEGS B (ARi0 SEGS B) 0).
{ intros ly S Hp W regs mem md pos S' ((HAR & HP) & Hr) Hcnt Hpath.
  eapply SRr_mono; [exact (ASM0 ly S W regs mem md pos S' (conj HAR Hr) Hcnt Hpath)|].
  intros W' c' _ (EW & regs' & mem' & md' & Hc & HAR' & Hrest).
  split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact (conj HAR' HP) | exact Hrest]. }
assert (ASFx : astack_free_law_x SEGS B (ARi0 SEGS B)).
{ intros ly S Hp W mem md mem' md' cid pos (HAR & HP) Hin H1 H2 H3 H4 H5 H6 H7 _.
  exact (conj (ASF ly S W mem md mem' md' cid pos HAR Hin H1 H2 H3 H4 H5 H6 H7) HP). }
assert (FFLx : frame_flag_lawP_x SEGS B (ARi0 SEGS B))
  by (intros ly S Hp W mem md cid pos (HAR & _) Hin; exact (FFL ly S W mem md cid pos HAR Hin)).
assert (ALOCKx : alock_realizes_x B (ARi0 SEGS B) (SIGMA WS_pthread_mutex_lock))
  by (apply alock_realizes_x_of_AR0; exact ALOCK).
assert (AUNLOCKx : aunlock_realizes_x B (ARi0 SEGS B) (SIGMA WS_pthread_mutex_unlock))
  by (apply aunlock_realizes_x_of_AR0; exact AUNLOCK).
assert (AREALLOCx : arealloc_cf_rule_c_x SEGS B [] (ARi0 SEGS B) MT MMAX RP_AR CTX (SIGMA WS_realloc))
  by (apply arealloc_cf_rule_c_x_of_AR0; exact AREALLOC).
assert (RPFx : forall S f k, rp_RM RP_AR S k -> rp_RM RP_AR (set_fs f S) k) by (intros S f k _; apply rp_RM_AR).
assert (RMMx : forall S k k', (k <= k')%nat -> rp_RM RP_AR S k' -> rp_RM RP_AR S k) by (intros S k k' _ _; apply rp_RM_AR).
assert (AMEMSETx : aintrin_realizes_x SEGS B (ARi0 SEGS B) OSet (SIGMA WS_asan_memset))
  by (apply aintrin_realizes_x_of_AR0; exact AMEMSET).
eapply pb_relay_add_x; eassumption.
Qed.
(* the walk's axiom audit, in the build log beside the theorem (the unit-level audit is oft's, on the statements) *)
Print Assumptions pb_relay_add.
End cAR.
End b.
End a.
