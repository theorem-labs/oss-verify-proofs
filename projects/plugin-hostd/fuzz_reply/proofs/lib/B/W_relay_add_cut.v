(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the image-B walk of fuzz_reply's relay_add
   (fuzz_reply.asan-ubsan 0x82af4 .. 0x82ca0, 107 instructions), over the image-B kit lib/B
   (a working branch), in the form of lib/B/W_relay_remove_cx.v (a working branch
   df8beed2cfa).  The file fixes the Section hypotheses, the entry context, the cut predicates over concrete machine
   states and the statement of every segment, so that the segments are proved in parallel; it proves only the
   composition ra_all and small shared lemmas.

   relay_add (fd) is relay.c:410-433: nothing for fd < 0 (returns -1); else under g_lock a full table grows to 16
   entries with realloc (only from the empty table: |es| < 4 <= 16), the entry fd, 0, ... is appended (memset, then
   s->fd = fd), g_nsrc counts it, g_lock is released, wake () runs; returns 0.  Its contract is lib/B W_contract.v
   Section w5: ra_spec B MT G RG CTX (BASE + AF_fr_relay_add), post ra_post.  The kit's comment there quotes image A
   (0x82950, a 128-byte frame and a fake frame); image B's code below is a fresh walk.

   IMAGE B (measured on the objdump of the pinned image fuzz_reply.asan-ubsan, sha256 10ffb5f9202ae2bd...):
     0x82af4-0x82b14  prologue: sp -= 64; ra, s0..s6 saved at 56(sp) .. 0(sp).  NO fake frame.
     0x82b18          s1 = -1;  0x82b1c `bltz a0, 0x82c18` (fd < 0: return -1).
     0x82b20-0x82b38  s0 = fd; s2 = the shadow offset (GOT slot 0x9df50 -> the cell); pthread_mutex_lock (&g_lock).
     0x82b3c          RAH (back from the lock): s3, s5, s4 = auipc images of g_nsrc - 484, g_capsrc - 576,
                      g_src - 500; a0 = g_nsrc, a1 = g_capsrc; `bne a0,a1, 0x82b90` (not full -> RAA).
     0x82b54          `beqz a0, 0x82b6c` (empty: s6 = 16); else the int32 doubling guard
                      `lui a1,0x40000; addw a1,a0,a1; bltz a1 -> unimp` (TRAP 0x82b60) and s6 = 2 g_nsrc.
     0x82b70-0x82b80  realloc (g_src, 56 s6); 0x82b84 `beqz a0, 0x82c44` (the error path: unlock, fprintf (stderr),
                      return -1 - refuted, the realloc rule forces success); g_src = a0, g_capsrc = s6.
     0x82b90          RAA (the append): s5 = g_nsrc, s4 = g_src, s1 = s4 + 56 s5; the UBSan pointer checks
                      `snez a0,s4; seqz a1,s1; beq a0,a1 -> unimp` (TRAP 0x82bb0) and
                      `slti a0,s5,0; sltu a1,s1,s4; xor; xori 1; beqz -> unimp` (TRAP 0x82bc4);
                      __asan_memset (s1, 0, 56) 0x82bd4; `addiw a0,s5,1; blt a0,s5 -> unimp` (TRAP 0x82bdc);
                      g_nsrc = a0; `beqz s4 -> unimp` (TRAP 0x82be4); `andi a0,s1,7; bnez -> unimp` (TRAP 0x82bec);
                      the shadow check of s1 (0x82bf0-0x82bfc; slow path 0x82c84-0x82c88; the error path
                      __asan_report_store4 0x82c90 not reached); s1->fd = fd 0x82c00;
                      pthread_mutex_unlock (&g_lock) 0x82c0c; wake () 0x82c10; s1 = 0; epilogue; ret.
   One `unimp` (0x82c80) and SIX trap edges to it: 0x82b60, 0x82bb0, 0x82bc4, 0x82bdc, 0x82be4, 0x82bec.

   CUT POINTS (offsets from lib/B W_listing.v AF_fr_relay_add = 0x7b0; text base 0x82344)
     RAH   0x82b3c  the lock taken, nothing else changed (the relay as at the entry);
     RAA   0x82b90  the table exists at T1 with the entry's es (grown by realloc when T = 0), the lock held;
     RAU   0x82c04  the entry appended (es ++ [ra_new fd]), the lock held.
   SEGMENTS
     ENT   0x82af4 -> RAH | ra_post (fd < 0)    prologue, the fd < 0 arm and return, the shadow offset, the lock
     HELD  RAH -> RAA                           the three globals, `bne`, the empty arm's realloc (or the TRAP arm,
                                                refuted: g_nsrc = g_capsrc <> 0 contradicts |es| < 4 < 16)
     APP   RAA -> RAU                           the append: memset, the five later traps, the shadow check, stores
     TAIL  RAU -> ra_post (fd >= 0)             unlock, wake, the epilogue, the return
   Every segment concludes `SRr SEGS W1 c1 (aPOST cx)` and takes its continuation in the same form, so the
   composition (ra_all) is plain application.

   The walk's journal is at RA_G RG (relay_add's own globals, W_contract.v RA_G), lifted to the caller's G at the
   two returns by ajournal_gx_G_mono with ra_spec's premise `forall a, inG (RA_G RG) a -> inG G a` (ra_lift).
   wake's contract is W6's lib/B/W_wake_c.v (Section hypothesis WAKE). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_wake_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- Rebasing a region: lib/A W_rebase.v (a working branch 25efee4c09e) with the prefix ra_, a local copy
   (that file is not on the kit branch).  A PLdHi load addresses a global through its object atom, a store through
   the kept auipc register; ra_st_ok_pi_rebase switches a region's base atom between the two. ---- *)
Section rebase. Context {fx : FPState}.
Variable segs : list Segment.
Variable val : nat -> Z.
Definition ra_shift_chunk (d : Z) (c : YP09.chunk) : YP09.chunk := YP09.mkChunk (YP09.c_off c + d) (YP09.c_val c).
Definition ra_rebase_region (b : nat) (d : Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (Some b) (YP09.r_lo r + d) (YP09.r_hi r + d) (YP09.r_wlo r + d) (YP09.r_whi r + d)
(map (ra_shift_chunk d) (YP09.r_chunks r)).
Fixpoint ra_map_nth {X : Type} (f : X -> X) (i : nat) (l : list X) : list X :=
match l, i with
| [], _ => []
| x :: l', O => f x :: l'
| x :: l', S i' => x :: ra_map_nth f i' l'
end.
Definition ra_ss_rebase (i b : nat) (d : Z) (ss : sstate) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ra_map_nth (ra_rebase_region b d) i (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition ra_same_extent (E : env) (r r' : YP09.region) : Prop :=
base_val E (YP09.r_base r') + YP09.r_lo r' = base_val E (YP09.r_base r) + YP09.r_lo r /\
base_val E (YP09.r_base r') + YP09.r_hi r' = base_val E (YP09.r_base r) + YP09.r_hi r.
Lemma ra_same_extent_rebase : forall E r b d,
base_val E (YP09.r_base r) = base_val E (Some b) + d -> ra_same_extent E r (ra_rebase_region b d r).
Proof. intros E r b d H. unfold ra_same_extent, ra_rebase_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. lia. Qed.
Lemma ra_extent_disjoint_same_l : forall E r r' r2, ra_same_extent E r r' ->
extent_disjoint E r r2 -> extent_disjoint E r' r2.
Proof. intros E r r' r2 [H1 H2] H. unfold extent_disjoint in *. lia. Qed.
Lemma ra_extent_disjoint_same_r : forall E r r' r2, ra_same_extent E r r' ->
extent_disjoint E r2 r -> extent_disjoint E r2 r'.
Proof. intros E r r' r2 [H1 H2] H. unfold extent_disjoint in *. lia. Qed.
Lemma ra_all_disjoint_same_l : forall E r r' rs, ra_same_extent E r r' -> all_disjoint E r rs -> all_disjoint E r' rs.
Proof.
intros E r r' rs Hs. induction rs as [|r2 rs IH]; cbn; [auto|].
intros [H1 H2]. split; [exact (ra_extent_disjoint_same_l E r r' r2 Hs H1) | exact (IH H2)].
Qed.
Lemma ra_all_disjoint_map_nth : forall E (f : YP09.region -> YP09.region) x i rs r,
nth_error rs i = Some r -> ra_same_extent E r (f r) -> all_disjoint E x rs -> all_disjoint E x (ra_map_nth f i rs).
Proof.
intros E f x i rs. revert i. induction rs as [|r0 rs IH]; intros i r Hn Hs H; [destruct i; exact H|].
destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. split; [exact (ra_extent_disjoint_same_r E r0 (f r0) x Hs H1) | exact H2].
- split; [exact H1|]. exact (IH i r Hn Hs H2).
Qed.
Lemma ra_pairwise_disjoint_map_nth : forall E (f : YP09.region -> YP09.region) i rs r,
nth_error rs i = Some r -> ra_same_extent E r (f r) -> pairwise_disjoint E rs -> pairwise_disjoint E (ra_map_nth f i rs).
Proof.
intros E f i rs. revert i. induction rs as [|r0 rs IH]; intros i r Hn Hs H; [destruct i; exact H|].
destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. split; [exact (ra_all_disjoint_same_l E r0 (f r0) rs Hs H1) | exact H2].
- split; [exact (ra_all_disjoint_map_nth E f r0 i rs r Hn Hs H1) | exact (IH i r Hn Hs H2)].
Qed.
Lemma ra_Forall_map_nth : forall {X : Type} (P : X -> Prop) (f : X -> X) i l x0,
nth_error l i = Some x0 -> (P x0 -> P (f x0)) -> Forall P l -> Forall P (ra_map_nth f i l).
Proof.
intros X P f i l. revert i. induction l as [|x l IH]; intros i x0 Hn Hf H; [destruct i; exact H|].
inversion H as [|? ? Hx Hl]; subst. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. constructor; [exact (Hf Hx) | exact Hl].
- constructor; [exact Hx | exact (IH i x0 Hn Hf Hl)].
Qed.
Lemma ra_region_ok_rebase : forall E m r b d,
base_val E (YP09.r_base r) = base_val E (Some b) + d -> region_ok segs E m r -> region_ok segs E m (ra_rebase_region b d r).
Proof.
intros E m r b d Hb (H1 & H2 & H3 & H4). unfold region_ok, ra_rebase_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [lia|]. split; [lia|]. split.
- intros o Ho. replace (base_val E (Some b) + o) with (base_val E (YP09.r_base r) + (o - d)) by lia. apply H3. lia.
- apply Forall_map. eapply Forall_impl; [|exact H4]. intros c Hc i Hi.
  unfold ra_shift_chunk, YP09.c_len in *. cbn [YP09.c_off YP09.c_val] in *.
  replace (base_val E (Some b) + (YP09.c_off c + d)) with (base_val E (YP09.r_base r) + YP09.c_off c) by lia.
  exact (Hc i Hi).
Qed.
Lemma ra_st_ok_rebase : forall E ss ms i r b d,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) = base_val E (Some b) + d ->
regions_wf (ra_map_nth (ra_rebase_region b d) i (ss_mem ss)) = true ->
st_ok segs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ra_map_nth (ra_rebase_region b d) i (ss_mem ss)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r b d (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (M1 & M2 & M3) & S9) Hn Hb Hwf.
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
do 7 (split; [assumption|]). split; [|exact S9].
split; [exact Hwf|]. split.
- exact (ra_Forall_map_nth _ (ra_rebase_region b d) i (ss_mem ss) r Hn (ra_region_ok_rebase E (ms_mem ms) r b d Hb) M2).
- exact (ra_pairwise_disjoint_map_nth E (ra_rebase_region b d) i (ss_mem ss) r Hn (ra_same_extent_rebase E r b d Hb) M3).
Qed.
Lemma ra_st_ok_pi_rebase : forall E ss ms i r b d,
st_ok_pi segs val E ss ms -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) = base_val E (Some b) + d ->
regions_wf (ra_map_nth (ra_rebase_region b d) i (ss_mem ss)) = true ->
st_ok_pi segs val E (ra_ss_rebase i b d ss) ms.
Proof.
intros E ss ms i r b d HS Hn Hb Hwf. unfold st_ok_pi, abs_ss, setpc, ra_ss_rebase in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (ra_st_ok_rebase E (mkSST (val A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss))
ms i r b d HS Hn Hb Hwf).
Qed.
Lemma ra_base_val_img : forall A_LIM E a b d, img_env val A_LIM E ->
(A_TEXT <= a < A_LIM)%nat -> (A_TEXT <= b < A_LIM)%nat -> val a = val b + d ->
base_val E (Some a) = base_val E (Some b) + d.
Proof. intros A_LIM E a b d HE Ha Hb H. cbn [base_val]. rewrite (HE a Ha), (HE b Hb). exact H. Qed.
End rebase.
(* ra_prebase HS i b d HREL: in HS : st_ok_pi segs val E ss ms, move region i (whose base is an image atom a) to base
   atom b, given HREL : val a = val b + d (or val b + d = val a); the new state is normalised by vm_compute. *)
Ltac ra_prebase HS i b d HREL :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with H : img_env val _ E |- _ => H | _ => fail "ra_prebase: no img_env hypothesis for" E end in
let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
let HS' := fresh "HSr" in
pose proof (ra_st_ok_pi_rebase segs val E ss ms i r b d HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [YP09.r_base]; apply (ra_base_val_img val _ E _ b d HEI); [cbv; lia | cbv; lia | first [exact HREL | symmetry; exact HREL | lia]])
  ltac:(vm_compute; reflexivity)) as HS';
clear HS; rename HS' into HS;
let ss2 := eval vm_compute in (ra_ss_rebase i b d ss) in change (ra_ss_rebase i b d ss) with ss2 in HS
end.

(* ---- Separation of a list of cells (base, length), picked by index: never lia over the whole list. ---- *)
Fixpoint ra_apart_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ ra_apart_from b r end.
Fixpoint ra_apart (l : list (Z * Z)) : Prop := match l with [] => True | b :: r => ra_apart_from b r /\ ra_apart r end.
Lemma ra_apart_from_In : forall b l c, ra_apart_from b l -> In c l -> fst b + snd b <= fst c \/ fst c + snd c <= fst b.
Proof.
intros b l c. induction l as [|x l IH]; cbn; [tauto|]. intros [Hx Hl] [<- | Hc]; [exact Hx | exact (IH Hl Hc)].
Qed.
Lemma ra_apart_nth : forall l i j a b, ra_apart l -> (i < j)%nat -> nth_error l i = Some a -> nth_error l j = Some b ->
fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Proof.
induction l as [|x l IH]; intros i j a b Hs Hij Ha Hb; [destruct i; discriminate|].
destruct Hs as [Hx Hl]. destruct i as [|i].
- cbn in Ha. injection Ha as <-. destruct j as [|j]; [lia|]. cbn in Hb.
  exact (ra_apart_from_In x l b Hx (nth_error_In l j Hb)).
- destruct j as [|j]; [lia|]. cbn in Ha, Hb. exact (IH i j a b Hl ltac:(lia) Ha Hb).
Qed.
Ltac ra_pick H i j D := pose proof (ra_apart_nth _ i j _ _ H ltac:(clear; lia) eq_refl eq_refl) as D; cbn [fst snd] in D.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's program counters (listing slot = (addr - 0x82344) / 4; AF_fr_relay_add = 0x7b0). ---- *)
Definition A_relay_add : Z := AF_fr_relay_add.             (* 0x82af4, the entry *)
Definition A_relay_addP : Z := BASE + A_relay_add.
Definition A_ra_held : Z := AF_fr_relay_add + 0x48.        (* 0x82b3c, back from pthread_mutex_lock *)
Definition A_ra_app : Z := AF_fr_relay_add + 0x9c.         (* 0x82b90, the append *)
Definition A_ra_unlock : Z := AF_fr_relay_add + 0x110.     (* 0x82c04, the unlock tail *)
(* The callee-saved registers in their frame slots 0(sp) (s6) .. 56(sp) (ra), sp = the entry sp - 64. *)
Definition RA_SAVED : list (bv 5) := [22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].
(* The auipc register images: s3 (0x82b3c, A_HI 28) = g_nsrc - 484, s5 (0x82b40, A_HI 29) = g_capsrc - 576,
   s4 (0x82b4c, A_HI 30) = g_src - 500. *)
Definition RA_HI_NSRC : Z := 484.
Definition RA_HI_CAPSRC : Z := 576.
Definition RA_HI_SRC : Z := 500.

(* wake's contract is W6's lib/B/W_wake_c.v (a working branch 34e402d7967, taken by path): wk_spec B RG
   at BASE + AF_fr_wake (0x82484), journal at G = [] (wake writes no global and no block), presence of image bytes
   kept, g_wake[1] still -1, errno kept; its walk is a Theorem Labs lane's pb_wake. *)

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* the allocator rules' caller-context table (W_contract.v Section w5's CTX; W_journal.v Section hc, the _c rules) *)
Variable CTX : list (list Z).

(* ---- The Section hypotheses every segment file copies (in this order, with these names). ----
     LAWS     : AR_laws SEGS B
     TL       : PALib B
     MTL      : ameter_laws MT
     HG       : gx_ok SEGS B (RA_G RG)
     HWK      : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
                in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
     HNROM    : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a
     HROMO    : rom_out SEGS B (RA_G RG)
     MO_FR    : forall s f, mo_le MT s (set_fs f s) 0
     HV3      : VAL (A_OBJ 3) = rg_lock RG
     HV4      : VAL (A_OBJ 4) = rg_nsrc RG
     HV5      : VAL (A_OBJ 5) = rg_src RG
     HV13     : VAL (A_OBJ 13) = rg_capsrc RG
     HH28     : VAL (A_HI 28) + RA_HI_NSRC = rg_nsrc RG
     HH29     : VAL (A_HI 29) + RA_HI_CAPSRC = rg_capsrc RG
     HH30     : VAL (A_HI 30) + RA_HI_SRC = rg_src RG
     HRGA     : ra_aligned RG
     HRGP     : ra_apart (ra_cells RG)
     HMMAX    : ATABLE < MMAX
     ALOCK    : alock_realizes B (SIGMA WS_pthread_mutex_lock)
     AUNLOCK  : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock)
     AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX (SIGMA WS_realloc)
     AMEMSET  : aintrin_realizes SEGS B OSet (SIGMA WS_asan_memset)
     WAKE     : wk_spec B RG (BASE + AF_fr_wake)
   ALOCK / AUNLOCK / AREALLOC / AMEMSET restate the published contracts (lib/B W_sites.v, W_journal.v, the donor's
   Reusable/YG0d.v) at the B call pcs; AREALLOC is the caller-context form (W_journal.v Section hc), whose premise
   `In (raZ regsT :: spine ch) CTX` the realloc call takes from ra_spec's `In [pc + 144] CTX` (B's relay_add keeps no
   frame pointer: ch = [], ra = entry + 144); WAKE is W6's lib/B/W_wake_c.v.  HV* / HH* / HRGA / HRGP / HNROM are placement
   facts, decided TRUE at the pin (PB_fr, fr_globals_b) at the end of this file; HG / HWK / HROMO name the allocator
   instance's owned statics and errno (HROMO is W4's form: rom_view survives the realloc, W_journal.v
   acall_kept_rom_view); MTL / MO_FR / HMMAX are the meter's laws (MO_FR is KF-COUNT #4's text: a set_fs - wake's fake
   frame seat - costs nothing) and the realloc request bound. *)

(* the global cells relay_add's walk reads or writes, and the two cells of the shadow offset, pairwise apart *)
Definition ra_cells (rg : rep_globals) : list (Z * Z) :=
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 30), 8); (rg_lock rg, 12); (rg_nsrc rg, 4); (rg_capsrc rg, 4); (rg_src rg, 8);
 (rg_wake rg + 4, 4)].
Definition ra_aligned (rg : rep_globals) : Prop :=
rg_lock rg mod 4 = 0 /\ rg_nsrc rg mod 4 = 0 /\ rg_capsrc rg mod 4 = 0 /\ rg_src rg mod 8 = 0.

(* ---- The entry context: everything ra_spec quantifies over at the entry. ---- *)
Record racx : Type := mkRacx {
  axregs : bvmap 5 word;
  axly : alayout; axS : astate; axW : world SEGS; axmem : word -> option byte; axmd : Model;
  axch : list (Z * Z * Z);
  axfd : Z; axT : Z; axes : list rentry }.

Definition asp0 (cx : racx) : Z := spZ (axregs cx).
Definition aFP (cx : racx) : list (Z * Z) := ra_FP (axT cx) (axes cx).
Definition aPOST (cx : racx) : world SEGS -> config -> Prop :=
ra_post B MT G RG (axregs cx) (axly cx) (axS cx) (axW cx) (axmem cx) (axmd cx) (axfd cx) (axT cx) (axes cx).

(* ABASE: exactly ra_spec's premises at the entry, in its order. *)
Definition ABASE (cx : racx) : Prop :=
afn_pre SEGS B RA_STK (axly cx) (axS cx) (axW cx) (axregs cx) (axmem cx) (axmd cx) (axch cx) /\
asp0 cx mod 32 = 0 /\ count_cid 0 (frames (axS cx)) < fs_frames 0 /\
getr (axregs cx) 10 = Z_to_bv 64 (axfd cx) /\ - 2 ^ 31 <= axfd cx < 2 ^ 31 /\
alock_at RG (axW cx) (axmem cx) false /\ awake_at RG (axW cx) (axmem cx) /\ rom_view SEGS (axW cx) (axmem cx) /\
ra_rel B RG (axly cx) (axS cx) (axW cx) (axmem cx) (axT cx) (axes cx) /\
(0 <= axfd cx -> (length (axes cx) < 4)%nat /\ ~ In (axfd cx) (map re_fd (axes cx))) /\
(forall a, inG (RA_G RG) a -> inG G a) /\
(forall a, inG (RA_G RG) a -> ~ (as_errno B <= a < as_errno B + 4)) /\
(0 <= axfd cx -> axT cx = 0 -> blocks_bytes (axS cx) + ATABLE <= LIVE_MAX) /\
In [A_relay_addP + 144] CTX /\
mo_ok MT (axS cx) (ra_cost MT (axT cx)).

(* ---- The frame: after the prologue, sp = the entry sp - 64, the eight saved registers in their slots. ---- *)
Definition ra_saved (cx : racx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 8)%nat ->
val_mem SEGS (arm W1 m1) (asp0 cx - RA_FRAME + 8 * Z.of_nat i) 8 (bv_unsigned (getr (axregs cx) (nth i RA_SAVED 0%bv))).

(* The registers every cut holds: sp, gp, tp and s7 .. s11 (never saved by relay_add, kept in their registers). *)
Definition aregs_base (cx : racx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = asp0 cx - RA_FRAME /\
getr regs1 3 = getr (axregs cx) 3 /\ getr regs1 4 = getr (axregs cx) 4 /\
getr regs1 23 = getr (axregs cx) 23 /\ getr regs1 24 = getr (axregs cx) 24 /\
getr regs1 25 = getr (axregs cx) 25 /\ getr regs1 26 = getr (axregs cx) 26 /\
getr regs1 27 = getr (axregs cx) 27.
(* ... and, after the lock: s0 = fd and s2 = the shadow offset (ld through the GOT at 0x82b24-0x82b2c). *)
Definition aregs_held (cx : racx) (regs1 : bvmap 5 word) : Prop :=
aregs_base cx regs1 /\ getr regs1 8 = w64 (axfd cx) /\ getr regs1 18 = w64 SHADOW_OFF.

(* errno's four bytes keep their view from (W, mem) to (W', mem') (ra_post's last conjunct, in its orientation). *)
Definition aerrno_kept (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i).

(* ALIVE: the journal from the entry (at RA_G, the stack RA_STK and the footprint ra_FP) owning no frame, the .rodata
   view (wake's premise), the presence of image bytes (ra_post's apres_kept), the saved registers, g_lock held,
   g_wake[1] = -1, the fake-frame count of the entry, errno's view as at the entry (ra_post's errno conjunct). *)
Definition ALIVE (cx : racx) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
@ajournal_gx _ SK SEGS B (RA_G RG) 0 [] RA_STK (asp0 cx) (aFP cx)
  (axly cx) (axS cx) (axW cx) (axmem cx) (axmd cx) [] ly1 S1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (axW cx) (axmem cx) W1 m1 /\
ra_saved cx W1 m1 /\ alock_at RG W1 m1 true /\ awake_at RG W1 m1 /\ frames S1 = frames (axS cx) /\
aerrno_kept (axW cx) (axmem cx) W1 m1.

(* ---- The cut predicates. ---- *)
(* RAH (0x82b3c): the lock taken; the allocator state, the relay and the live blocks as at the entry. *)
Definition RAH (cx : racx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 m1 md1,
c1 = cfg_at SEGS (BASE + A_ra_held) regs1 m1 md1 /\
aregs_held cx regs1 /\ 0 <= axfd cx /\
ALIVE cx (axly cx) (axS cx) W1 m1 md1 0 /\
ra_rel B RG (axly cx) (axS cx) W1 m1 (axT cx) (axes cx).

(* RAA (0x82b90): the table at T1 holds the entry's es (T1 = T, or the realloc's block when T = 0), g_capsrc = 16;
   s3 / s4 the auipc images of g_nsrc and g_src; the meter charged the realloc (ra_cost) when T = 0. *)
Definition RAA (cx : racx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_app) regs1 m1 md1 /\
aregs_held cx regs1 /\
getr regs1 19 = w64 (rg_nsrc RG - RA_HI_NSRC) /\ getr regs1 20 = w64 (rg_src RG - RA_HI_SRC) /\
0 <= axfd cx /\
ALIVE cx ly1 S1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (axes cx) /\
mo_le MT (axS cx) S1 (ra_cost MT (axT cx)) /\
((axT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (axly cx) (axS cx))) \/
 (axT cx <> 0 /\ T1 = axT cx /\ ablocks B ly1 S1 = ablocks B (axly cx) (axS cx))).

(* RAU (0x82c04, after `sw s0,0(s1)`): the entry ra_new fd appended (the table at T1 holds es ++ [ra_new fd],
   g_nsrc = |es| + 1), the lock still held; the held registers (s0 = fd: wake's afn_pre reads the frame-pointer
   chain from s0, achain_low; s1 .. s6 are restored from the frame by the epilogue). *)
Definition RAU (cx : racx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_unlock) regs1 m1 md1 /\
aregs_held cx regs1 /\ 0 <= axfd cx /\
ALIVE cx ly1 S1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (axes cx ++ [ra_new (axfd cx)]) /\
mo_le MT (axS cx) S1 (ra_cost MT (axT cx)) /\
((axT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (axly cx) (axS cx))) \/
 (axT cx <> 0 /\ T1 = axT cx /\ ablocks B ly1 S1 = ablocks B (axly cx) (axS cx))).

(* ---- The segment statements. ---- *)
(* ENT: the prologue 0x82af4-0x82b14, the fd < 0 test 0x82b1c (fd < 0: the epilogue 0x82c18 and the return, all in
   this segment), the shadow offset 0x82b24-0x82b2c and pthread_mutex_lock (&g_lock) 0x82b38 -> RAH. *)
Definition ra_ent_stmt : Prop :=
forall cx,
ABASE cx ->
(forall W2 c2, RAH cx W2 c2 -> SRr SEGS W2 c2 (aPOST cx)) ->
SRr SEGS (axW cx) (cfg_at SEGS A_relay_addP (axregs cx) (axmem cx) (axmd cx)) (aPOST cx).

(* HELD: RAH 0x82b3c -> the loads of g_nsrc / g_capsrc, `bne` 0x82b50 (not full: -> RAA); full: `beqz` 0x82b54 (the
   empty table: s6 = 16; the other arm, with its TRAP 0x82b60, is refuted: |es| < 4 < 16), realloc (g_src = 0,
   896) 0x82b80, `beqz a0` 0x82b84 (the error path to fprintf NOT taken: res >= 4096), the stores of g_src and
   g_capsrc -> RAA. *)
Definition ra_held_stmt : Prop :=
forall cx W1 c1,
ABASE cx -> RAH cx W1 c1 ->
(forall W2 c2, RAA cx W2 c2 -> SRr SEGS W2 c2 (aPOST cx)) ->
SRr SEGS W1 c1 (aPOST cx).

(* APP: RAA 0x82b90 -> s1 = g_src + 56 g_nsrc, TRAPS 0x82bb0 / 0x82bc4, __asan_memset (s1, 0, 56) 0x82bd4,
   TRAP 0x82bdc, g_nsrc += 1, TRAPS 0x82be4 / 0x82bec, the shadow check 0x82bf0-0x82bfc (slow path 0x82c84-0x82c88; the
   error path 0x82c90 NOT taken), s1->fd = fd 0x82c00 -> RAU. *)
Definition ra_app_stmt : Prop :=
forall cx W1 c1,
ABASE cx -> RAA cx W1 c1 ->
(forall W2 c2, RAU cx W2 c2 -> SRr SEGS W2 c2 (aPOST cx)) ->
SRr SEGS W1 c1 (aPOST cx).

(* TAIL: RAU 0x82c04 -> pthread_mutex_unlock (&g_lock) 0x82c0c, wake () 0x82c10 (WAKE, at G = []), s1 = 0, the
   epilogue 0x82c18-0x82c3c and the return -> ra_post's fd >= 0 arm. *)
Definition ra_tail_stmt : Prop :=
forall cx W1 c1,
ABASE cx -> RAU cx W1 c1 ->
SRr SEGS W1 c1 (aPOST cx).

(* The walk: the segments give relay_add's contract. *)
Lemma ra_all : ra_ent_stmt -> ra_held_stmt -> ra_app_stmt -> ra_tail_stmt -> ra_spec B MT G RG CTX A_relay_addP.
Proof.
intros ENT HELD APP TAIL W ly S regs mem md ch fd T es H1 H2 H3 H4 H5 H6 H7 H7r H8 H9 H10 H11 H12 H12c H13.
set (cx := mkRacx regs ly S W mem md ch fd T es).
assert (HB : ABASE cx)
  by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H7r (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H12c H13)))))))))))))).
apply (ENT cx HB). intros W2 c2 HR. apply (HELD cx W2 c2 HB HR). intros W3 c3 HA. apply (APP cx W3 c3 HB HA).
intros W4 c4 HU. exact (TAIL cx W4 c4 HB HU).
Qed.

(* ---- Shared lemmas. ---- *)
(* The walk's journal at RA_G is a journal at the caller's G (ra_spec's premise). *)
Lemma ra_lift : forall cx XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ABASE cx ->
@ajournal_gx _ SK SEGS B (RA_G RG) XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
@ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros cx XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HB HJ.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGin & _).
exact (ajournal_gx_G_mono SEGS B (RA_G RG) G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGin HJ).
Qed.
Lemma ra_lock_in : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG (RA_G RG) a.
Proof. intros a Ha. unfold RA_G, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma ra_nsrc_in : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> inG (RA_G RG) a.
Proof. intros a Ha. unfold RA_G, inG. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma ra_capsrc_in : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG (RA_G RG) a.
Proof.
intros a Ha. unfold RA_G, inG. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma ra_src_in : forall a, rg_src RG <= a < rg_src RG + 8 -> inG (RA_G RG) a.
Proof.
intros a Ha. unfold RA_G, inG. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma ra_inG_cases : forall a, inG (RA_G RG) a ->
rg_lock RG <= a < rg_lock RG + 12 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_src RG <= a < rg_src RG + 8.
Proof.
intros a Ha. unfold RA_G in Ha.
apply inG_cons in Ha; destruct Ha as [Hz|Ha]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|].
apply inG_cons in Ha; destruct Ha as [Hz|Ha]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|].
apply inG_cons in Ha; destruct Ha as [Hz|Ha]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|].
apply inG_cons in Ha; destruct Ha as [Hz|Ha]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|].
exfalso; exact (inG_nil a Ha).
Qed.
(* errno's cell: four image bytes below kLowMemEnd (PALib's api_env), none of relay_add's globals (ra_spec's premise). *)
Lemma ra_errno_low : PALib B -> forall i, 0 <= i < 4 ->
0 <= as_errno B + i < kLowMemEnd /\ in_img SEGS (as_errno B + i).
Proof.
intros TL i Hi. destruct TL as [_ _ _ HENV _ _ _]. destruct HENV as ((He0 & He1) & HEI & _).
split; [lia | apply HEI; lia].
Qed.
Lemma ra_errno_notG : forall cx, ABASE cx -> forall i, 0 <= i < 4 -> ~ inG (RA_G RG) (as_errno B + i).
Proof.
intros cx HB i Hi HG. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGerr & _).
apply (HGerr _ HG). lia.
Qed.
Lemma ra_errno_step : forall W m W1 m1 W2 m2, aerrno_kept W m W1 m1 ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
aerrno_kept W m W2 m2.
Proof. intros W m W1 m1 W2 m2 H1 H2 i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.
Lemma ra_errno_refl : forall W m, aerrno_kept W m W m.
Proof. intros W m i Hi. reflexivity. Qed.
End c.
End b.
End a.

(* ---- The placement facts of the walk, decided at the pin: PB_fr (lib/B W_img.v) and fr_globals_b (W_rep.v). ---- *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ra_hv_fr :
pa_val (PAImg := PB_fr) (A_OBJ 3) = rg_lock fr_globals_b /\ pa_val (PAImg := PB_fr) (A_OBJ 4) = rg_nsrc fr_globals_b /\
pa_val (PAImg := PB_fr) (A_OBJ 5) = rg_src fr_globals_b /\ pa_val (PAImg := PB_fr) (A_OBJ 13) = rg_capsrc fr_globals_b /\
pa_val (PAImg := PB_fr) (A_HI 28) + RA_HI_NSRC = rg_nsrc fr_globals_b /\
pa_val (PAImg := PB_fr) (A_HI 29) + RA_HI_CAPSRC = rg_capsrc fr_globals_b /\
pa_val (PAImg := PB_fr) (A_HI 30) + RA_HI_SRC = rg_src fr_globals_b.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma ra_aligned_fr : ra_aligned fr_globals_b.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma ra_cells_fr : ra_apart (ra_cells (PI := PB_fr) fr_globals_b).
Proof.
unfold ra_cells. cbn [ra_apart ra_apart_from fst snd].
assert (E0 : pa_val (PAImg := PB_fr) (A_OBJ 0) = 0x9df50) by (vm_compute; reflexivity).
assert (E30 : pa_val (PAImg := PB_fr) (A_OBJ 30) = 0xa6638) by (vm_compute; reflexivity).
rewrite E0, E30. cbn [fr_globals_b rg_lock rg_nsrc rg_capsrc rg_src rg_wake].
repeat split; first [left; lia | right; lia].
Qed.
Lemma ra_nrom_fr : forall a, inG (RA_G fr_globals_b) a -> ~ in_rom (pa_segs (PAImg := PB_fr)) a.
Proof.
intros a Ha (sg & Hin & Hw & Hr).
assert (HA : 0x5d8d20 <= a < 0x5d904c).
{ unfold RA_G in Ha. cbn [fr_globals_b rg_lock rg_nsrc rg_capsrc rg_src] in Ha.
  repeat (apply inG_cons in Ha; destruct Ha as [Hz|Ha]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|]).
  exfalso; exact (inG_nil a Ha). }
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) (pa_segs (PAImg := PB_fr))))
  by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) _ sg Hin).
rewrite Hw in H.
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez Hin Hw Ha.
vm_compute in H. repeat (destruct H as [H|H]; [inversion H; subst; lia|]). destruct H.
Qed.
End fr.
