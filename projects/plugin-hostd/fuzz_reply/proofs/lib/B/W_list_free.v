(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of plugin-hostd/fuzz_reply's list_free.
   THE KIT RELOCATES, THE WALKS DO NOT: this is a fresh walk over lib/B/W_listing.v, not a relocation of
   lib/A/W_list_free.v.  Image B does not inline list_drop (image A does): it CALLS it in a loop, and UBSan
   trap mode adds two inline trap branches.  Contract: lib/B/W_contract.v lf_spec / lf_spec_g (:314 / :499 of the
   generated kit 67c07b3d6e6).

   B list_free (0x86678, 71 instructions, frame 48; b-list_free.s (sha256 f149a58aa07c; internal record)):
     0x86678..0x86694  prologue: sp -= 48; ra s0 s1 s2 s3 s4 at 40 32 24 16 8 0; s0 = LA
     0x86698..0x8669c  TRAP S1 (ALIGN8 on LA): andi a0,a0,7; bnez a0 -> 0x8675c unimp
     0x866a0..0x866a8  s2 = the shadow base, through the GOT slot and the dynamic-address cell
     0x866ac..0x866bc  s1 = LA + 8; s3 = (LA + 8) / 8 + s2; the shadow byte of l->n; bnez -> partial check
     0x866c0..0x866c4  a0 = l->n; beqz a0 -> 0x86700 (the loop is not entered)
     0x866c8..0x866cc  s4 = ((LA + 8) mod 8) + 3, the partial-check constant
     0x866d0 LOOP      addiw a1,a0,-1
     0x866d4           TRAP S5 (int32 -1 overflow): bge a1,a0 -> 0x8675c unimp
     0x866d8..0x866dc  a0 = LA; jal 0x85b50 = BASE + AF_fr_list_drop: list_drop(l, n - 1)
     0x866e0 RET       the shadow byte of l->n again; bnez -> partial check
     0x866e8..0x866f0  a0 = l->n; bnez a0 -> 0x866d0 (the loop) else 0x86700
     0x86700 DONE      s1 = LA / 8 + s2; the shadow byte of l->v; free(l->v); l->v = 0; l->cap = 0
     0x8673c..0x86758  epilogue and ret
   The two trap branches are refuted from the function's own pre with lib/B/W_traps.v (a Theorem Labs lane):
     0x8669c  trap_align8 at a = s0 = LA,   from lf_spec's `LA mod 8 = 0`
     0x866d4  trap_decw   at x = a0 = l->n, from alist_at's `hl_n l <= hl_cap l < 2 ^ 30` (0 < n at the loop head)
   The ASan partial-check edges (0x86760, 0x866f4, 0x86774, 0x86784, 0x8678c) never run: the shadow of the
   list head is zero in every allocator state (lf_spec's `azs LA 16`), which the engine's shadow entries
   (sh_ok) decide inside paj_run_tok.

   ONE proof, over the GENERIC allocator relation ARx (a Theorem Labs lane's route (b), step 3): Section c proves
   pb_list_free_x : lf_spec_x B PST ARx MT RP G (W_contract_x.v), Section g pb_list_free_g_x over gx_prog_x.  Sections
   cAR / gAR re-derive the AR theorems pb_list_free and pb_list_free_g (statements unchanged) at ARx := ARi0,
   PST := [].  Section hypotheses of the generic form, with what owes them:
   - LAWS / HP0 / BLKN / PSTR / MLAW / TL : the relation's laws, the empty hidden-head set, a live block's size is
     not negative (W_kit_x.v's; alist_at's vector bound reads it), the ROM bytes off PST, the meter's laws, PALib;
   - RP : the room record of the texts (W_journal_x.v roomp; the room round, kit candidate 13): lf_spec_x's room and
     live-count premises and the free rules' (Section c's comment says how the walk threads them);
   - AFREE / AFREEN : afree_cf_rule_c_x / afree_null_cf_rule_c_x at RP and the caller-context table CTX (the allocator
     parameter of GUIDE section 3.1: free(l->v), or free(NULL) when the list never had a vector), with
     HCTX_lf_exit (list_free + 0xa0) and HCTX_ld_free (list_drop + 0x9c, for list_drop's own free);
   - AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove) (W_sites_x.v), the __asan_memmove intrinsic's contract,
     which list_drop's walk takes; it reaches this file through list_drop's theorem;
   - HG / HGR / HRO / GX_ROM / GX_W / GSHV : gx_prog G, the lane's side conditions on the program globals
     (a vm_compute at PB_fr for a concrete G); they also give gx_prog [(LA, 16)] for the callee.
   No callee-contract hypothesis: each list_drop call is lib/B/W_list_drop.v pb_list_drop_ro_x (a Theorem Labs lane's room form,
   ROOM-6B 8aef363b876, of a Theorem Labs lane's pb_list_drop 345ecd33c8d), the kit's ldrop_spec_x (W_contract.v Section w1, :691; its
   post keeps errno's view), instantiated at the CALLEE's own globals G' = [(LA, 16)] (gx_prog G' gives its HG,
   GRT and, through rom_out, ROMS) and lifted to this walk's G with W_journal.v ajournal_gx_G_mono (W2's
   convention, W_contract.v:739-744: there is no ldrop_spec_g, so the caller fixes G).
   No MISSING PREMISE hypothesis: every premise of ldrop_spec comes from lf_spec's own pre.  LA mod 8 = 0 and
   LF_STK = 48 + LDROP_STK are in the kit's statement; the memmove premise AREC * (n - 1 - i) < 2 ^ 32 is 0 < 2 ^ 32
   at list_free's call, i = n - 1.

   Reuse search (the three-clause script), reuse-list_free.txt (sha256 b0d267fe3b15; internal record) and
   clause3-list_free.txt (sha256 bfecd4e188a6; internal record), verbatim (the A entry is the search key only; this walk uses no image-A address):
     ### reuse search for list_free (run 2026-10-29T09:37:58Z)
     entry A: 0x86080  entry B: 0x86678  (static t symbol: no trampoline, no real_f slot)
     --- (1) by name: proof-index list_free
     ### clause (3) for list_free: pattern ((Theorem|Lemma) [A-Za-z0-9_']*list_free\b)|(\b(0x)?0*86080\b)|(\b(0x)?0*86678\b) over 2530 unique proofs/plugin-hostd trees of 12328 cold/* refs
   Rule-24 lookup (lookup-list_free.txt (sha256 8b9ad78e83f5; internal record), CONFIRMED by a second agent): the released proofs of list_free
   are the plain (lib/Prog) and ubsan (lib/U/Prog) images only; no asan-ubsan proof, and no hit by the B
   addresses; so this is a fresh B walk. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_list_drop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
(* the lib/B sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) step 3): no sink instance is a hint after this *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_list_free : Z := AF_fr_list_free.
Definition A_list_freeP : Z := BASE + A_list_free.
Definition A_lf_loop : Z := AF_fr_list_free + 0x58.   (* 0x866d0: the loop head *)
Definition A_lf_ret : Z := AF_fr_list_free + 0x68.    (* 0x866e0: the return address of the list_drop call *)
Definition A_lf_done : Z := AF_fr_list_free + 0x88.   (* 0x86700: after the loop *)
Definition LF_FRAME : Z := 48.
(* the frame's six slots, from sp up: s4 s3 s2 s1 s0 ra (0x8667c-0x86690) *)
Definition lf_saved : list Z := [20; 19; 18; 9; 8; 1].

(* ---- the list struct: v at +0, n at +8, cap at +12, all writable ---- *)
Definition lf_lreg (m : nat) (cv cn cc : sv) : YP09.region :=
YP09.mkRegion (Some m) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 cv); YP09.mkChunk 8 (CVal 4 cn); YP09.mkChunk 12 (CVal 4 cc)].
Lemma lf_lreg_ok : forall E W mem m LA cv cn cc v n cap,
bv_unsigned (ew E m) = LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 ->
sv_denot E cv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E cn = Z_to_bv 64 n -> 0 <= n < 2 ^ 32 ->
sv_denot E cc = Z_to_bv 64 cap -> 0 <= cap < 2 ^ 32 ->
val_mem SEGS (arm W mem) LA 8 v -> val_mem SEGS (arm W mem) (LA + 8) 4 n -> val_mem SEGS (arm W mem) (LA + 12) 4 cap ->
awr W mem LA 16 -> region_ok SEGS E (arm W mem) (lf_lreg m cv cn cc).
Proof.
intros E W mem m LA cv cn cc v n cap Hm H0 H1 Hv Rv Hn Rn Hc Rc Mv Mn Mc Hw. unfold region_ok, lf_lreg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hm.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
- apply (chunk_ok_val SEGS E _ LA 0 8 cv v); [exact Hv | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Mv].
- apply (chunk_ok_val SEGS E _ LA 8 4 cn n); [exact Hn | cbn; lia | cbn; lia | exact Mn].
- apply (chunk_ok_val SEGS E _ LA 12 4 cc cap); [exact Hc | cbn; lia | cbn; lia | exact Mc].
Qed.
Lemma lf_disj : forall LA g, (forall a, LA <= a < LA + 16 -> ~ (g <= a < g + 8)) -> LA + 16 <= g \/ g + 8 <= LA.
Proof.
intros LA g H. destruct (Z_le_gt_dec (LA + 16) g) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (g + 8) LA) as [H2|H2]; [right; exact H2|]. exfalso. apply (H (Z.max LA g)); lia.
Qed.
(* ---- list surgery: dropping the LAST record (image B calls list_drop(l, n - 1)) ---- *)
Lemma lf_firstn_last : forall {A} (l : list A) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
intros A l. induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|]. destruct k as [|k]; [reflexivity|].
cbn [firstn nth]. rewrite (IH k d) by (cbn in Hk; lia). reflexivity.
Qed.
Lemma lf_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk; [rewrite firstn_nil; reflexivity|].
destruct n as [|n]; [lia|]. cbn [firstn]. destruct k as [|k]; [reflexivity|].
cbn [nth]. apply IH. lia.
Qed.
Lemma lf_perm_drop : forall (l1 l2 A Bm R : list (Z * Z)) x,
Permutation (l1 ++ x :: l2) (A ++ (Bm ++ [x]) ++ R) -> Permutation (l1 ++ l2) (A ++ Bm ++ R).
Proof.
intros l1 l2 A Bm R x H. apply (Permutation_app_inv l1 l2 [] (A ++ Bm ++ R) x).
rewrite app_nil_l. eapply Permutation_trans; [exact H|]. rewrite <- !app_assoc. cbn [app].
rewrite (app_assoc A Bm (x :: R)), (app_assoc A Bm R). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma lf_perm_drop2 : forall (l1 l2 A Bm R : list (Z * Z)) x,
Permutation (l1 ++ x :: l2) ((A ++ (Bm ++ [x])) ++ R) -> Permutation (l1 ++ l2) ((A ++ Bm) ++ R).
Proof.
intros l1 l2 A Bm R x H. rewrite <- (app_assoc A Bm R). apply (lf_perm_drop l1 l2 A Bm R x).
rewrite <- (app_assoc A (Bm ++ [x]) R) in H. exact H.
Qed.
(* the room round (W_contract_x.v lf_spec_x / ldrop_spec_x on cand13): a free keeps the live counts under their bounds
   (one block fewer, ReplyCnt.v acnt_del_le); list_free's room budget is one free per text (each inside a list_drop
   call) and one for the vector *)
Lemma lf_cnt_del : forall RP0 l1 (x : Z * Z) l2, cnt_ok RP0 (l1 ++ x :: l2) -> cnt_ok RP0 (l1 ++ l2).
Proof.
intros RP0 l1 x l2 H. unfold cnt_ok in *.
apply (cnt_ok_pk_mono RP0 (fun _ => 0%nat) (fun _ => 0%nat) (l1 ++ x :: l2) (l1 ++ l2)); [|exact H].
intros P. cbv beta. rewrite !Nat.add_0_r. apply acnt_del_le.
Qed.
Lemma lf_rm_cast : forall RP0 S0 (m m' : nat), rp_RM RP0 S0 m -> m = m' -> rp_RM RP0 S0 m'.
Proof. intros RP0 S0 m m' H <-. exact H. Qed.
Lemma lf_rk : forall l, Z.to_nat (lf_cost MT_rk l) = Datatypes.S (length (hl_recs l)).
Proof. intros l. unfold lf_cost, hl_n. cbn [mo_free MT_rk]. lia. Qed.
(* ---- bytes kept: a region of the memory that a run or a call did not touch ---- *)
Lemma lf_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.
(* writability across a step that keeps presence: W_frame.v's writable_kept *)
Lemma lf_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma lf_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.
Lemma lf_region_kept2 : forall E (W W2 : world SEGS) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 n b lo hi wlo whi cs Hn Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hv. exact Ha.
- apply Hw. exact Ha.
Qed.
Lemma lf_len_text_recs : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
induction l as [|r l IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
(* the int32 decrement the loop computes (0x866d0 addiw a1,a0,-1), as an unsigned value *)
Lemma lf_U_decw : forall E x j, Sg E x = j -> 0 < j < 2 ^ 31 -> U E (SAluw ALU_ADD x (SLit (-1))) = j - 1.
Proof.
intros E x j Hx Hj.
assert (Hs : Sg E (SAluw ALU_ADD x (SLit (-1))) = j - 1).
{ rewrite S_SAluw, U_SLit. cbn [zalu_raw]. rewrite (trap_mod32_of_S E x j Hx).
  rewrite (trap_swrap32 _ (j - 1)); [apply swrap32_id; lia|].
  change (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1). rewrite Z.add_mod_idemp_l by lia.
  replace (j + (2 ^ 32 - 1)) with (j - 1 + 1 * 2 ^ 32) by lia. apply Z_mod_plus_full. }
rewrite U_of_S, Hs. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Lemma lf_S_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> Sg E (SOff n 0) = v.
Proof.
intros E n v H Hv. rewrite S_of_U, (U_atom E n v H) by lia. apply swrap64_id. unfold half64. lia.
Qed.

(* ---- THE WALK OVER THE GENERIC RELATION (a Theorem Labs lane's route (b), step 3; lib/A/W_list_free.v's template at
   a working branch 16f29d9fe81): list_free over any ARx with its laws, stated as W_contract_x.lf_spec_x.  The
   Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation), HP0 (the unit's hidden-head
   set is empty in every ARx state: a Theorem Labs lane's ruling; list_drop's walk, called here, reads block shadow through
   it), BLKN (W_kit_x.v Section g's: a live block's size is not negative, which alist_at's vector bound reads), PSTR (the ROM bytes are off the program statics PST: W_journal_x.ajournal_gx_rom_view_x's premise), and the
   allocator's free rules in their caller-context form (W_journal_x Section hc, `Variable CTX`; a Theorem Labs lane's ruling
   (c)).  Image B's list_free calls free once, at the exit (free(l->v), or free(NULL)), handing the rule the chain []
   (s0 holds the list head LA, an image address), so the call's trace is the singleton [its return address], the
   closed fact HCTX_lf_exit; each list_drop call frees once inside list_drop, whose walk (W_list_drop.v
   pb_list_drop_ro_x) takes HCTX_ld_free.  There is no free in B's loop (A's HCTX_lf_loop has no B counterpart).
   RP is the room record of the texts (W_journal_x.v roomp, the rules' and the specs'): the loop invariant carries the
   room left (m + 1 + kr: one free per text left, each inside a list_drop call, and one for the vector) and the live
   counts at the loop head, which only fall (each list_drop call drops one block, lf_cnt_del); each list_drop call
   hands ldrop_spec_x the room 1 + (m - 1 + 1 + kr), and the exit's free hands the rule 1 + kr and its stack room
   (aj_stack_room_x). ---- *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis MLAW : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis HRO : rom_out SEGS B G.
Hypothesis GX_ROM : forall a, inG G a -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Hypothesis GX_W : forall a, inG G a -> forall m, writable_at SEGS m a.
Hypothesis GSHV : forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> 0 < n ->
(forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* fuzz_reply.asan-ubsan objdump: 0x86714 jal __interceptor_trampoline_free; returns to 0x86718 = list_free 0x86678 + 0xa0 *)
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xa0] CTX.
(* fuzz_reply.asan-ubsan objdump: 0x85be8 jal __interceptor_trampoline_free; returns to 0x85bec = list_drop 0x85b50 + 0x9c *)
Hypothesis HCTX_ld_free : In [BASE + AF_fr_list_drop + 0x9c] CTX.
(* the __asan_memmove intrinsic's contract (W_sites_x.v), which list_drop's theorem takes *)
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* each list_drop call: lib/B/W_list_drop.v pb_list_drop_ro_x at globals G' that satisfy gx_prog_x (its ROMS is
   rom_out's three clauses, reordered: W_journal.v rom_out) *)
Lemma lf_ldrop_x : forall G', gx_prog_x B ARx G' -> ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop).
Proof.
intros G' (HG' & HGR' & HRO' & _).
eapply pb_list_drop_ro_x; eassumption.
Qed.

Lemma lf_LA_range : forall LA, (forall a, LA <= a < LA + 16 -> inG G a) ->
0x10000 <= LA /\ LA + 16 <= 0x5fc000 /\
(LA + 16 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= LA) /\ (LA + 16 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= LA) /\
(forall a, LA <= a < LA + 16 -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros LA HLG.
pose proof (pa_img_range LA (proj1 (HG LA (HLG LA ltac:(lia))))) as H1.
pose proof (pa_img_range (LA + 15) (proj1 (HG (LA + 15) (HLG (LA + 15) ltac:(lia))))) as H2.
split; [lia|]. split; [lia|].
split; [apply lf_disj; intros a Ha; exact (proj1 (proj2 (HGR a (HLG a Ha))))|].
split; [apply lf_disj; intros a Ha; exact (proj2 (proj2 (HGR a (HLG a Ha))))|].
intros a Ha. exact (proj1 (HGR a (HLG a Ha))).
Qed.
(* errno's four bytes lie in the image (PALib's api_env): off the list head (gx_rt) and below every frame *)
Lemma lf_errno_facts : forall (sp LA : Z), alloc_ceiling <= sp - LF_STK -> (forall a, LA <= a < LA + 16 -> inG G a) ->
forall i, 0 <= i < 4 ->
0 <= as_errno B + i < 2 ^ 64 /\ ~ (LA <= as_errno B + i < LA + 16) /\ ~ (sp - LF_STK <= as_errno B + i < sp).
Proof.
intros sp LA Hsp HLG i Hi. pose proof (pal_env B TL) as ((HE0 & HE1) & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). rewrite C5 in HE1.
split; [lia|]. split.
- intros Hin. exact (proj1 (HGR _ (HLG _ Hin)) ltac:(lia)).
- unfold LF_STK, ASTACK in *. lia.
Qed.
Lemma lf_inG_lo : forall a, inG G a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (pa_segs_low a (proj1 (HG a Ha))). Qed.
(* the blocks a list's predicate names are live blocks *)
Lemma lf_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b n, In (b, n) (list_blks l) -> In (b, n) (ablocks B ly S).
Proof.
intros ly S W mem LA l lines HL b n Hin. unfold list_blks in Hin.
pose proof HL as (_ & _ & _ & _ & _ & Hvc & _ & _ & HFA).
apply in_app_or in Hin as [Hin | Hin].
- destruct (Z.eqb_spec (hl_cap l) 0) as [He|He]; [destruct Hin|].
  destruct Hin as [Heq | []]. injection Heq as <- <-.
  destruct Hvc as [[H0 _] | (_ & Hv & _)]; [lia | exact Hv].
- apply in_map_iff in Hin as (r & Heq & Hr). injection Heq as <- <-.
  exact (proj1 (proj1 (Forall_forall _ _) HFA r Hr)).
Qed.
Lemma lf_blk_bounds_x : forall ly S Hp (W : world SEGS) mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> 4096 <= b /\ b + req_size n <= alloc_ceiling.
Proof.
intros ly S Hp W mem md b n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & H1 & H2 & _). auto.
Qed.
Lemma lf_blk_writable_x : forall ly S Hp (W : world SEGS) mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n ->
writable_at SEGS (mrestrict (w_H W) mem) (b + i).
Proof.
intros ly S Hp W mem md b n HAR Hin i Hi.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & _ & _ & Hpp & _).
apply (apresent_writable SEGS). exact (proj1 (Hpp (b + i) ltac:(lia))).
Qed.
(* A list's predicate at another memory: the heap bytes it reads are kept (a block's byte is never an image
   byte, so never one of the head's 16), and the head's four facts are given (a walk re-reads them off the
   state's own region after a run or a call). *)
Lemma lf_alist_relocate_x : forall ly S Hp (W : world SEGS) mem md mem' LA l lines,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) ->
(forall a, 4096 <= a < alloc_ceiling -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
val_mem SEGS (arm W mem') LA 8 (hl_v l) -> val_mem SEGS (arm W mem') (LA + 8) 4 (hl_n l) ->
val_mem SEGS (arm W mem') (LA + 12) 4 (hl_cap l) -> awr W mem' LA 16 ->
alist_at B ly S W mem' LA l lines.
Proof.
intros ly S Hp W mem md mem' LA l lines HAR HL HGL KH Mv' Mn' Mc' Hw'.
pose proof HL as (Mv & Mn & Mc & Hw & Hnc & Hvc & Hnd & Hnv & HFA).
assert (NOIMG : forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n -> ~ (LA <= b + j < LA + 16)).
{ intros b n j Hin Hj Hc.
  destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (b + j) HAR ltac:(left; exists b, n; split; [exact Hin | lia])) as [_ Hni].
  exact (Hni (proj1 (HG (b + j) (HGL (b + j) Hc)))). }
assert (GK : forall b n bs, In (b, n) (ablocks B ly S) -> Z.of_nat (length bs) <= req_size n ->
  garr8 SEGS (arm W mem) b bs -> garr8 SEGS (arm W mem') b bs).
{ intros b n bs Hin Hlen Hg. destruct (lf_blk_bounds_x ly S Hp W mem md b n HAR Hin) as [Hb1 Hb2].
  unfold arm in *. apply (lf_garr8_kept (w_H W) (w_H W) mem mem'); [|exact Hg].
  intros j Hj. apply KH; [lia|]. exact (NOIMG b n j Hin ltac:(lia)). }
split; [exact Mv'|]. split; [exact Mn'|]. split; [exact Mc'|]. split; [exact Hw'|].
split; [exact Hnc|].
split.
{ destruct Hvc as [Hz | (Hcp & Hin & Hjl & Hg)]; [left; exact Hz|].
  right. split; [exact Hcp|]. split; [exact Hin|]. split; [exact Hjl|].
  apply (GK _ _ _ Hin); [|exact Hg].
  pose proof (BLKN ly S Hp W mem md _ _ HAR Hin) as Hn0.
  assert (Rq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
  by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap l) 0); [unfold AREC in *; lia | reflexivity]).
  rewrite Rq. unfold bzs. rewrite length_map, length_app, lf_len_text_recs.
  unfold hl_n, AREC in *. lia. }
split; [exact Hnd|]. split; [exact Hnv|].
rewrite Forall_forall in HFA |- *. intros r Hr. destruct (HFA r Hr) as (Hin & Hg & H1 & H2).
split; [exact Hin|]. split; [|split; [exact H1 | exact H2]].
apply (GK _ _ _ Hin); [|exact Hg].
assert (Rq : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
rewrite Rq. unfold bzs. rewrite length_map, length_app. cbn [length]. lia.
Qed.

(* ---- the entry (0x86678) ---- *)
Definition lf_Bx : sv := SOff 35 0.
Definition lf_regions0 : smem :=
[ stack_region LF_FRAME; got_regionP; bcell_regionP 35; lf_lreg 10 (SOff 32 0) (SOff 33 0) (SOff 34 0) ].
Definition lf_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 (0x5fc000 - 16) 0);
(33%nat, mkAF 0 (2 ^ 30 - 1) 0); (34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_lf0 : sstate := mkSS A_list_free sr_atoms lf_regions0 None lf_facts0.
Definition lf_SH0 : list shent := [ mkSHE 10 0 16 ].
Definition lf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lf_extra (l : hlist) : list word := map (Z_to_bv 64) [hl_v l; hl_n l; hl_cap l; SB].

Lemma lf_entry_x : forall W ly S Hp regs mem md ch LA (l : hlist) lines,
afn_pre_x SEGS B ARx LF_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_extra l))) ss_lf0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_freeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS lf_Bx lf_SH0 (Eimg (Ereg regs (lf_extra l))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & DG & DC & _).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & _).
assert (WS : LF_STK = 16496) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_extra l))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw'. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw'. }
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct HL as (_ & _ & _ & _ & _ & [[_ ->] | (Hcp & Hin & _)] & _); [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
split.
- unfold ss_lf0, A_list_freeP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lf_regions0, stack_region, got_regionP, bcell_regionP, LF_FRAME.
repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 lf_Bx SB);
[cbn [sv_denot lf_Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* apply (lf_lreg_ok E W mem 10 LA _ _ _ (hl_v l) (hl_n l) (hl_cap l)).
-- rewrite E10. apply unsigned_lit_small. lia.
-- lia.
-- lia.
-- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- exact Hv64.
-- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- exact Mv.
-- exact Mn.
-- exact Mc.
-- exact Hw.
+ apply pairwise_disjoint_of_extents. unfold lf_regions0, lf_lreg, stack_region, got_regionP, bcell_regionP, extent_of_region, LF_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
rewrite (VB 10%nat LA E10) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HLA1 HLA2 DG DC. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HLA1 HLA2 Hn0 Hcap HnZ. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lf_SH0. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E lf_Bx 10 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZS).
+ unfold U, lf_Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
Qed.

(* ---- the three cuts inside the body (0x866d0 loop, 0x866e0 after the call, 0x86700 after the loop) ----
   Atoms: 0..31 the current registers; 32 v, 33 cap, 34 the current l->n, 35..40 the entry's s4 s3 s2 s1 s0 ra
   (the frame's six slots, from sp up). *)
Definition lf_frame (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall i, (i < 6)%nat ->
val_mem SEGS (arm W mem) (sp0 - 48 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))).
Definition lf_regsL (regs regs0 : bvmap 5 word) (LA : Z) : Prop :=
getr regs 2 = Z_to_bv 64 (spZ regs0 - 48) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 8 = Z_to_bv 64 LA /\ getr regs 9 = Z_to_bv 64 (LA + 8) /\ getr regs 18 = Z_to_bv 64 SB /\
getr regs 19 = Z_to_bv 64 ((LA + 8) / 8 + SB) /\
getr regs 21 = getr regs0 21 /\ getr regs 22 = getr regs0 22 /\ getr regs 23 = getr regs0 23 /\
getr regs 24 = getr regs0 24 /\ getr regs 25 = getr regs0 25 /\ getr regs 26 = getr regs0 26 /\
getr regs 27 = getr regs0 27.
Definition lf_sp0 (sp0 : Z) : Prop := sp0 mod 16 = 0 /\ alloc_ceiling + LF_STK <= sp0 <= 2 ^ 47.
Definition lf_xl (v cap c : Z) (regs0 : bvmap 5 word) : list word :=
map (Z_to_bv 64) [v; cap; c] ++ map (fun r => getr regs0 (Z_to_bv 5 r)) lf_saved.
Definition lf_stackL : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0 (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SOff (35 + i) 0))) (seq 0 6)).
Definition lf_BxL : sv := SOff 18 0.
Definition lf_srL : list sv :=
sr_set (sr_set sr_atoms 9%bv (SOff 8 8))
19%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 18 0)).
Definition lf_lregL : YP09.region := lf_lreg 8 (SOff 32 0) (SOff 34 0) (SOff 33 0).
Definition lf_factsL : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 0x10000 (0x5fc000 - 16) 0); (18%nat, mkAF SB SB 0);
(34%nat, mkAF 0 (2 ^ 30 - 1) 0) ] [] [].
Definition ss_lfL (pc : Z) : sstate := mkSS pc lf_srL [lf_stackL; lf_lregL] None lf_factsL.
Definition lf_SHL : list shent := [ mkSHE 8 0 16 ].

Lemma lf_ew_saved : forall regs regs0 v cap c i, (i < 6)%nat ->
ew (Eimg (Ereg regs (lf_xl v cap c regs0))) (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)).
Proof.
intros regs regs0 v cap c i Hi. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (35 + i)%nat with (32 + (3 + i))%nat by lia. rewrite ew_Ereg_extra.
do 6 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma lf_ew_regs : forall regs extra i, (i < 6)%nat ->
ew (Eimg (Ereg regs extra)) (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)).
Proof.
intros regs extra i Hi.
do 6 (destruct i as [|i]; [rewrite Eimg_low by (unfold A_TEXT; cbn; lia); apply ew_Ereg_nat; vm_compute; reflexivity|]). lia.
Qed.
Lemma lf_stackL_ok : forall E W mem sp0 regs0,
bv_unsigned (ew E 2) = sp0 - 48 -> 0 <= sp0 - 48 -> sp0 <= 2 ^ 64 ->
(forall i, (i < 6)%nat -> ew E (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0))) ->
lf_frame W mem sp0 regs0 -> region_ok SEGS E (arm W mem) lf_stackL.
Proof.
intros E W mem sp0 regs0 Hsp Hlo Hhi Hew Hfr. unfold region_ok, lf_stackL.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hsp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply (chunk_ok_val SEGS E _ (sp0 - 48) (8 * Z.of_nat i) 8 (SOff (35 + i) 0) (bv_unsigned (getr regs0 (Z_to_bv 5 (nth i lf_saved 0))))).
- cbn [sv_denot]. rewrite (Hew i ltac:(lia)), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- change (8 * Z.of_N 8) with 64. exact Hr.
- cbn. lia.
- exact (Hfr i ltac:(lia)).
Qed.
(* the list's derived registers s1 and s3, with LA in atom a and the shadow base in atom b *)
Lemma lf_den_regs : forall E {a b : nat} LA, ew E a = Z_to_bv 64 LA -> ew E b = Z_to_bv 64 SB -> 0 <= LA < 2 ^ 60 ->
sv_denot E (SOff a 8) = Z_to_bv 64 (LA + 8) /\
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 8) (SLit 3)) (SOff b 0)) = Z_to_bv 64 ((LA + 8) / 8 + SB).
Proof.
intros E a b LA H8 H18 HLA.
assert (U8 : forall c, 0 <= c <= 8 -> U E (SOff a c) = LA + c) by (intros c Hc; apply (U_atom_off E a LA c H8); lia).
assert (U18 : U E (SOff b 0) = SB) by (apply (U_atom E b SB H18); unfold SB; lia).
assert (Usrl : forall c, 0 <= c <= 8 -> U E (SAlu ALU_SRL (SOff a c) (SLit 3)) = (LA + c) / 8).
{ intros c Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite U8 by lia. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (D8 : 0 <= (LA + 8) / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
split; rewrite denot_lit_U; f_equal.
- apply U8. lia.
- rewrite U_SAlu. cbn [zalu_raw]. rewrite Usrl by lia. rewrite U18. apply zcanon_id. unfold M64, SB. lia.
Qed.
Lemma lf_set_srL : forall E pc rs fs regs m LA,
st_ok_pi SEGS VAL E (mkSS pc sr_atoms rs None fs) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)) ->
ew E 8 = Z_to_bv 64 LA -> ew E 18 = Z_to_bv 64 SB -> 0 <= LA < 2 ^ 60 ->
getr regs 9 = Z_to_bv 64 (LA + 8) -> getr regs 19 = Z_to_bv 64 ((LA + 8) / 8 + SB) ->
st_ok_pi SEGS VAL E (mkSS pc lf_srL rs None fs) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)).
Proof.
intros E pc rs fs regs m LA H0 H8 H18 HLA R9 R19.
destruct (lf_den_regs E LA H8 H18 HLA) as (D9 & D19).
pose proof (ast_ok_pi_set_reg_fp E _ _ 9%bv (SOff 8 8) H0 eq_refl ltac:(rewrite D9; symmetry; exact R9)) as H1.
pose proof (ast_ok_pi_set_reg_fp E _ _ 19%bv _ H1 eq_refl ltac:(rewrite D19; symmetry; exact R19)) as H2.
exact H2.
Qed.
Lemma lf_shent8_x : forall E ly S Hp W mem md LA,
ARx ly S Hp W mem md -> azs B LA 16 -> ew E 8 = Z_to_bv 64 LA -> ew E 18 = Z_to_bv 64 SB ->
0x10000 <= LA -> LA + 16 <= 0x5fc000 ->
shent_ok SEGS lf_BxL E (mrestrict (w_H W) mem) (mkSHE 8 0 16).
Proof.
intros E ly S Hp W mem md LA HAR HZS H8 H18 HL1 HL2.
apply (shent_ok_of_range SEGS (w_H W) mem E lf_BxL 8 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZS).
+ unfold lf_BxL. rewrite (U_atom E 18 SB H18) by (unfold SB; lia). reflexivity.
+ rewrite (U_atom E 8 LA H8) by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
Qed.

Lemma lf_cut_x : forall pc W ly S Hp mem md regs regs0 LA v cap c,
ARx ly S Hp W mem md -> lf_regsL regs regs0 LA -> lf_sp0 (spZ regs0) -> lf_frame W mem (spZ regs0) regs0 ->
0x10000 <= LA -> LA + 16 <= 0x5fc000 -> azs B LA 16 ->
val_mem SEGS (arm W mem) LA 8 v -> val_mem SEGS (arm W mem) (LA + 8) 4 c -> val_mem SEGS (arm W mem) (LA + 12) 4 cap ->
awr W mem LA 16 -> 0 <= v < 2 ^ 64 -> 0 <= c <= cap -> cap < 2 ^ 30 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_xl v cap c regs0))) (ss_lfL pc)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
sh_ok SEGS lf_BxL lf_SHL (Eimg (Ereg regs (lf_xl v cap c regs0))) (mrestrict (w_H W) mem).
Proof.
intros pc W ly S Hp mem md regs regs0 LA v cap c HAR HR Hsp0 Hfr HL1 HL2 HZS Mv Mn Mc Hw Hv64 Hc Hcap.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & _).
destruct Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LF_STK = 16496) by reflexivity.
assert (Hsp48 : (spZ regs0 - 48) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_xl v cap c regs0))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 48)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw'. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw'. }
split.
- unfold ss_lfL. apply (lf_set_srL E pc _ _ regs _ LA); [| exact E8 | exact E18 | lia | exact R9 | exact R19].
apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ constructor; [|constructor; [|constructor]].
* apply (lf_stackL_ok E W mem (spZ regs0) regs0 Usp ltac:(lia) ltac:(lia)); [|exact Hfr].
intros i Hi. subst E. exact (lf_ew_saved regs regs0 v cap c i Hi).
* apply (lf_lreg_ok E W mem 8 LA _ _ _ v c cap).
-- rewrite E8. apply unsigned_lit_small. lia.
-- lia.
-- lia.
-- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- exact Hv64.
-- cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- exact Mv.
-- exact Mn.
-- exact Mc.
-- exact Hw.
+ apply pairwise_disjoint_of_extents. unfold lf_stackL, lf_lregL, lf_lreg, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 8%nat LA E8) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hsp1 Hsp2 C1 HL1 HL2 WS. clear. unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lf_factsL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E8, E18, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hsp1 Hsp2 C1 HL1 HL2 Hc Hcap Hsp48 WS. clear.
unfold SB, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lf_SHL. constructor; [|constructor].
exact (lf_shent8_x E ly S Hp W mem md LA HAR HZS E8 E18 HL1 HL2).
Qed.

(* ---- one call of list_drop, journal to journal (the form of lib/A/W_source_reset.v aj_gx_call / sr_call_lf) ---- *)
Definition lf_G1 (x : Z) : list (Z * Z) := [(x, 16)].
Lemma lf_G1_in : forall x a, inG (lf_G1 x) a <-> x <= a < x + 16.
Proof.
intros x a. unfold lf_G1, inG. rewrite Exists_cons, Exists_nil. unfold in_zr. cbn [fst snd].
split; [intros [H | []]; lia | intros H; left; lia].
Qed.
Lemma lf_keep_hi_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H Wc) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (lf_inG_lo a (Hsub a Hc)). unfold kLowMemEnd in *. lia.
Qed.
Lemma lf_frames_of_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 -> frames S2 = frames Sc.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
Qed.
Lemma lf_gx_call_x : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ apply Hcallee. exact (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi
    Hsp Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G STK sp0 0 [] FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k
  STK1 (sp0 + o) 0 [] FP1 [] ly2 S2 Hp2 W2 mem2 md2 k1 HJ);
[ exact (ajournal_gx_G_mono_x SEGS B PST ARx G1 G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 HGsub HJ1)
| lia | lia | lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.

(* ---- the loop's state ---- *)
Definition lf_blks (l : hlist) (m : nat) : list (Z * Z) :=
(if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++
map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (firstn m (hl_recs l)).
Definition lf_inv_x (W : world SEGS) ly S (Hp : list Z) regs0 mem0 md0 (LA : Z) (l : hlist) (lines : bool) (m kr : nat)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regs : bvmap 5 word) memc mdc (kk : Z) : Prop :=
ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk /\
lf_regsL regs regs0 LA /\ lf_frame Wc memc (spZ regs0) regs0 /\
(exists lc, hl_v lc = hl_v l /\ hl_cap lc = hl_cap l /\ hl_recs lc = firstn m (hl_recs l) /\
  alist_at B lyc Sc Wc memc LA lc lines) /\
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l m ++ rest)) /\
frames Sc = frames S /\ mo_le MT S Sc ((hl_n l - Z.of_nat m) * mo_free MT) /\ apres_kept B W mem0 Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) /\
rp_RM RP Sc (m + 1 + kr) /\ cnt_ok RP (ablocks B lyc Sc).
Definition lf_ctx_x W ly S (Hp : list Z) regs0 mem0 md0 ch LA (l : hlist) lines : Prop :=
afn_pre_x SEGS B ARx LF_STK ly S Hp W regs0 mem0 md0 ch /\ alist_at B ly S W mem0 LA l lines /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\ LA mod 8 = 0 /\
rom_view SEGS W mem0 /\ mo_ok MT S (lf_cost MT l).

Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                      | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* the writable bytes of the entry state's four regions: the frame, and the list head (bytes of G) *)
Ltac lf_awr0 Usp U10 HLG :=
  cbn [ss_mem add_cond];
  apply awr_ok_x_cons_awr0; [awr_any; try exact Usp|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lreg base_val]; rewrite U10;
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HLG; lia.
(* the same at the three body cuts: the frame region has no writable window there *)
Ltac lf_awrL Usp U8 HLG :=
  cbn [ss_mem add_cond];
  apply awr_ok_x_cons_awr0; [awr_any; try exact Usp|];
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregL lf_lreg base_val]; rewrite U8;
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HLG; lia.

(* ---- 0x866dc jal list_drop: the callee's contract at ITS own globals, lifted to this walk's journal ---- *)
Lemma lf_call_drop_x : forall (LA : Z) (lc : hlist) (lines : bool) (i : nat)
(Wc : world SEGS) regsT memT sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k raw (kr : nat),
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 -> rom_view SEGS Wc memT ->
LA mod 8 = 0 -> AREC * (hl_n lc - 1 - Z.of_nat i) < 2 ^ 32 -> lf_sp0 sp0 ->
ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK sp0 FP ly S Hp W0 mem0 md0 [] lyc Sc Hpc Wc memT mdc k ->
alist_at B lyc Sc Wc memT LA lc lines ->
(i < length (hl_recs lc))%nat -> mo_ok MT Sc (mo_free MT) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
getr regsT 10 = w64 LA -> getr regsT 11 = w64 (Z.of_nat i) -> spZ regsT = sp0 + -48 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsT < alloc_ceiling ->
(forall b n, In (b, n) (list_blks lc) -> forall j, 0 <= j < req_size n -> inFP FP (b + j)) ->
SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_drop)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK sp0 FP ly S Hp W0 mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 aregs_preserved regsT regs2 /\
 alist_at B ly2 S2 W2 mem2 LA (ldrop_list lc i) lines /\
 (exists b1 b2, ablocks B lyc Sc = b1 ++ (fst (nth i (hl_recs lc) (0, [])),
   Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
 apres_kept B Wc memT W2 mem2 /\
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H Wc) memT (as_errno B + j)) /\
 frames S2 = frames Sc /\ mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + -48 - LDROP_STK <= a < sp0 + -48) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memT a)).
Proof.
intros LA lc lines i Wc regsT memT sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k raw kr
HGL HZS HROM HLA8 HCAP Hsp0 HJ HL Hi HMO HRM HCNT H10 H11 Hsp Hgp Htp Hra Hraw Hra4 Hs0 HFP.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HGL) as (HLA1 & HLA2 & _).
destruct Hsp0 as (Hal & Hsp1 & Hsp2).
assert (WS : LF_STK = 16496) by reflexivity. assert (WD : LDROP_STK = 16448) by reflexivity.
assert (Hsub : forall a, inG (lf_G1 LA) a -> inG G a)
by (intros a Ha; apply HGL; exact (proj1 (lf_G1_in LA a) Ha)).
assert (HP1 : gx_prog_x B ARx (lf_G1 LA))
by (exact (gx_prog_sub_x B ARx (lf_G1 LA) G Hsub (conj HG (conj HGR (conj HRO (conj GX_ROM (conj GX_W GSHV))))))).
(* the vector lies in the heap, so off this frame; when cap = 0 the range is empty *)
assert (HVEC : forall a, hl_v lc <= a < hl_v lc + AREC * hl_cap lc -> 4096 <= a < alloc_ceiling).
{ intros a Ha. pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
  destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Ha; unfold AREC in Ha; lia|].
  destruct (lf_blk_bounds_x lyc Sc Hpc Wc memT mdc _ _ HARc Hin) as [Hb1 Hb2].
  assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
  by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
  rewrite Rq in Hb2. lia. }
eapply SRr_mono.
{ eapply (lf_gx_call_x (lf_G1 LA) Wc regsT memT (BASE + AF_fr_list_drop) LF_STK sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k
    LDROP_STK [(hl_v lc, hl_v lc + AREC * hl_cap lc);
      (fst (nth i (hl_recs lc) (0, [])), fst (nth i (hl_recs lc) (0, [])) + req_size (Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1))]
    (-48) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 k1 =>
       alist_at B ly2 S2 W2 mem2 LA (ldrop_list lc i) lines /\
       (exists b1 b2, ablocks B lyc Sc = b1 ++ (fst (nth i (hl_recs lc) (0, [])),
         Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
       apres_kept B Wc memT W2 mem2 /\
       (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H Wc) memT (as_errno B + j)) /\
       mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr)
    Hsub HJ Hsp ltac:(reflexivity) ltac:(lia) ltac:(unfold LDROP_STK, LDROP_FRAME, ASTACK; lia)
    ltac:(unfold LDROP_STK, LF_STK, LDROP_FRAME, ASTACK; lia) Hgp Htp Hra Hraw Hra4
    ltac:(apply achain_low; exact Hs0)).
  - intros HPRE1. eapply SRr_mono.
    { exact (lf_ldrop_x (lf_G1 LA) HP1 Wc lyc Sc Hpc regsT memT mdc [] LA lc lines i HPRE1 H10 H11 HL Hi
        HLA8 ltac:(lia) HCAP HZS
        ltac:(intros a Ha; split; [apply (proj2 (lf_G1_in LA a)); exact Ha | rewrite Hsp; lia])
        ltac:(intros a Ha; pose proof (HVEC a Ha); rewrite Hsp; lia) HMO kr HRM HCNT HROM). }
    cbv beta. unfold ldrop_post_x.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPK & HER & HAL & HBS & HML & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, 1.
    split; [rewrite Hra; reflexivity|]. split; [rewrite <- Hsp; exact HJ2|].
    split; [exact HP2|]. split; [exact HAL | split; [exact HBS | split; [exact HPK | split; [exact HER |
      split; [exact HML | exact HRM2]]]]].
  - intros a Ha. left. split.
    + destruct Ha as (r & Hr & Hra2). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra2.
      * pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
        destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Hra2; unfold AREC in Hra2; lia|].
        assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
        by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
        replace a with (hl_v lc + (a - hl_v lc)) by lia.
        apply (HFP (hl_v lc) (AREC * hl_cap lc)); [unfold list_blks; apply in_or_app; left;
          rewrite (proj2 (Z.eqb_neq (hl_cap lc) 0) ltac:(lia)); left; reflexivity | rewrite Rq; lia].
      * set (r := nth i (hl_recs lc) (0, [])) in *.
        replace a with (fst r + (a - fst r)) by lia.
        apply (HFP (fst r) (Z.of_nat (length (snd r)) + 1)); [unfold list_blks; apply in_or_app; right;
          exact (in_map (fun q : Z * list byte => (fst q, Z.of_nat (length (snd q)) + 1)) _ r (nth_In _ _ Hi)) | lia].
    + destruct Ha as (r & Hr & Hra2). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra2.
      * pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
        destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Hra2; unfold AREC in Hra2; lia|].
        assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
        by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
        exists (hl_v lc), (AREC * hl_cap lc). split; [exact Hin | rewrite Rq; lia].
      * set (r := nth i (hl_recs lc) (0, [])) in *.
        pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & HFA).
        exists (fst r), (Z.of_nat (length (snd r)) + 1).
        split; [exact (proj1 (proj1 (Forall_forall _ _) HFA r (nth_In _ _ Hi))) | lia]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJa & HJb & HP & HAL & HBS & HPK & HER & HML & HRM2).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJa|]. split; [exact HP|]. split; [exact HAL|].
split; [exact HBS|]. split; [exact HPK|]. split; [exact HER|].
split; [exact (lf_frames_of_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb)|]. split; [exact HML|]. split; [exact HRM2|].
intros a Ha Hno. exact (lf_keep_hi_x (lf_G1 LA) LDROP_STK (sp0 + -48) _ lyc Sc Hpc Wc memT mdc ly2 S2 Hp2 W2 mem2 md2 k1
  Hsub HJb a Ha Hno).
Qed.

(* W_kit's prreg without the normalisation: the register's symbolic value stays as the engine wrote it
   (lib/A/W_list_free.v's prreg_raw) *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* the list head's four facts, read off a body cut's own region after a run or a call *)
Lemma lf_head_of_region : forall E (W : world SEGS) mem LA v c cap,
region_ok SEGS E (mrestrict (w_H W) mem) lf_lregL ->
bv_unsigned (ew E 8) = LA -> ew E 32 = Z_to_bv 64 v -> ew E 34 = Z_to_bv 64 c -> ew E 33 = Z_to_bv 64 cap ->
0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 32 -> 0 <= cap < 2 ^ 32 ->
val_mem SEGS (arm W mem) LA 8 v /\ val_mem SEGS (arm W mem) (LA + 8) 4 c /\
val_mem SEGS (arm W mem) (LA + 12) 4 cap /\ awr W mem LA 16.
Proof.
intros E W mem LA v c cap HR U8 E32 E34 E33 Hv Hc Hcap.
assert (V0 : val_mem SEGS (mrestrict (w_H W) mem) (LA + 0) (N.to_nat 8) v).
{ eapply (field_of_region E _ 8 LA); [exact HR | exact U8 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (V8 : val_mem SEGS (mrestrict (w_H W) mem) (LA + 8) (N.to_nat 4) c).
{ eapply (field_of_region E _ 8 LA); [exact HR | exact U8 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (V12 : val_mem SEGS (mrestrict (w_H W) mem) (LA + 12) (N.to_nat 4) cap).
{ eapply (field_of_region E _ 8 LA); [exact HR | exact U8 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite Z.add_0_r in V0. unfold arm.
split; [exact V0|]. split; [exact V8|]. split; [exact V12|].
intros i Hi. destruct HR as (_ & _ & RLw & _).
cbn [lf_lregL lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U8 in RLw. exact (RLw i Hi).
Qed.

(* ---- one turn of the loop: 0x866d0 -> list_drop -> 0x866e0 -> 0x866d0 (or 0x86700) ---- *)
Lemma lf_iter_x : forall (m : nat) W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> (1 <= m <= length (hl_recs l))%nat ->
lf_inv_x W ly S Hp regs0 mem0 md0 LA l lines m kr Wc lyc Sc Hpc regs memc mdc kk ->
getr regs 10 = w64 (Z.of_nat m) ->
(forall Wc' lyc' Sc' Hpc' regs' memc' mdc' kk',
   lf_inv_x W ly S Hp regs0 mem0 md0 LA l lines (m - 1) kr Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ->
   ((m - 1)%nat <> 0%nat -> getr regs' 10 = w64 (Z.of_nat (m - 1))) ->
   SRr SEGS Wc' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + if (m - 1 =? 0)%nat then A_lf_done else A_lf_loop)) memc' (seg_rom SEGS)) mdc')
     (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr)) ->
SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) memc (seg_rom SEGS)) mdc)
  (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros m W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX Hm HINV H10 HK.
destruct HCTX as (HPRE & HL & HLG & HZS & HLA8 & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra0 & Hra04 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity. assert (WD : LDROP_STK = 16448) by reflexivity.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & (lc & Hlcv & Hlccap & Hlcrecs & HLc) & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hlcn : hl_n lc = Z.of_nat m) by (unfold hl_n; rewrite Hlcrecs, length_firstn; lia).
pose proof HLc as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
rewrite Hlcn in Mn, Hn0.
assert (Hcap0 : 0 < hl_cap lc) by lia.
assert (Hvin : In (hl_v lc, AREC * hl_cap lc) (ablocks B lyc Sc))
by (destruct Hvc as [[Hc0 _] | (_ & Hin & _)]; [lia | exact Hin]).
destruct (lf_blk_bounds_x lyc Sc Hpc Wc memc mdc _ _ HARc Hvin) as [Hvb1 Hvb2].
assert (Rqv : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
rewrite Rqv in Hvb2.
assert (Hv64 : 0 <= hl_v lc < 2 ^ 64) by (unfold alloc_ceiling, AREC in *; lia).
(* the records of lc are records of l, so its blocks are in this walk's footprint *)
assert (HSUBB : forall b n, In (b, n) (list_blks lc) -> In (b, n) (list_blks l)).
{ unfold list_blks. rewrite Hlcv, Hlccap, Hlcrecs. intros b n Hin. apply in_app_or in Hin as [H|H].
  - apply in_or_app. left. exact H.
  - apply in_or_app. right. apply in_map_iff in H as (r & <- & Hr).
    apply (in_map (fun q : Z * list byte => (fst q, Z.of_nat (length (snd q)) + 1))).
    rewrite <- (firstn_skipn m (hl_recs l)). apply in_or_app. left. exact Hr. }
assert (HFP : forall b n, In (b, n) (list_blks lc) -> forall j, 0 <= j < req_size n -> inFP (blk_FP (list_blks l)) (b + j))
by (intros b n Hin j Hj; exact (inFP_ablocks_fp (list_blks l) b n j (HSUBB b n Hin) Hj)).
(* the meter: one free fits in what is left of lf_cost *)
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) ((hl_n l - Z.of_nat m) * mo_free MT) (mo_free MT) MLAW HMO HMLE MF0).
  unfold lf_cost. pose proof HL as (_ & _ & _ & _ & (Hn0' & _) & _).
  assert (Hmn : Z.of_nat m <= hl_n l) by (unfold hl_n; lia). nia. }
(* ---- the cut at the loop head ---- *)
destruct (lf_cut_x A_lf_loop Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v lc) (hl_cap lc) (Z.of_nat m)
  HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hv64 ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v lc) (hl_cap lc) (Z.of_nat m) regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat m)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = getr regs0 21) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = getr regs0 22) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regs0 23) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs0 24) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = getr regs0 25) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat m)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (ESV : forall i, (i < 6)%nat -> ew E (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
clear HE.
unfold A_lf_loop.
(* 0x866d0 addiw a1,a0,-1; 0x866d4 bge a1,a0 -> the UBSan int32 trap, never taken *)
paj_run_tok_x RUN HS HJ SHOK lf_Bspan. { lf_awrL Usp U8 HLG. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) |- _ => rename Hf into HFr1 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) |- _ => rename Hgr into HGr1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms1) HFr1 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
psrr_branch_tok RUN BR HS SHOK lf_Bspan.
- exfalso. rewrite (trap_decw E (SOff 10 0) (Z.of_nat m) (lf_S_atom E 10 (Z.of_nat m) E10 ltac:(lia)) ltac:(lia)) in Hc.
  discriminate.
- (* 0x866d8 mv a0,s0; 0x866dc jal list_drop *)
  paj_run_to_tok_x RUNTO HS HJ SHOK lf_Bspan AF_fr_list_drop. { lf_awrL Usp U8 HLG. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ => rename Hf into HFr2 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ => rename Hgr into HGr2 end.
  lazymatch type of HFr2 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) (ms_mem ms1) a).
  { intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite U8 in Hr; lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg_raw HS (9%bv : bv 5) Q9. prreg_raw HS (11%bv : bv 5) Q11. prreg_raw HS (19%bv : bv 5) Q19.
  destruct (lf_den_regs E LA E8 E18 ltac:(lia)) as (D9 & D19).
  (* the list's predicate and errno's view at the call site *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
  destruct (lf_head_of_region E Wc (ms_mem ms2) LA (hl_v lc) (Z.of_nat m) (hl_cap lc) RL1 U8 E32 E34 E33
    Hv64 ltac:(lia) ltac:(lia)) as (VL0 & VL8 & VL12 & HAWR).
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha Hno; rewrite (K2 a Ha Hno); exact (K1 a Ha Hno)).
  assert (HLc2 : alist_at B lyc Sc Wc (ms_mem ms2) LA lc lines).
  { apply (lf_alist_relocate_x lyc Sc Hpc Wc memc mdc (ms_mem ms2) LA lc lines HARc HLc HLG);
    [ intros a Hh Hno; exact (K12 a ltac:(unfold alloc_ceiling in *; lia) Hno)
    | exact VL0 | rewrite Hlcn; exact VL8 | exact VL12 | exact HAWR ]. }
  assert (HROM2 : rom_view SEGS Wc (ms_mem ms2))
  by (exact (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO PSTR HROM)).
  assert (ERR2 : forall j, 0 <= j < 4 -> aview SEGS (w_H Wc) (ms_mem ms2) (as_errno B + j) = aview SEGS (w_H W) mem0 (as_errno B + j)).
  { intros j Hj. destruct (ERF j Hj) as (Fa & Fb & Fc).
    rewrite (K12 (as_errno B + j) ltac:(lia) Fb). exact (HERR j Hj). }
  assert (HAPK2 : apres_kept B W mem0 Wc (ms_mem ms2)).
  { intros a Hi Hno Herr Hpp.
    lazymatch goal with Hg1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)),
                        Hg2 : mem_grows (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ =>
      exact (lf_apresent_grows _ _ _ a Hg2 (lf_apresent_grows _ _ _ a Hg1 (HAPK a Hi Hno Herr Hpp))) end. }
  assert (Hi1 : ((m - 1) < length (hl_recs lc))%nat) by (rewrite Hlcrecs, length_firstn; lia).
  (* the room: list_drop's free is one of the m frees left for the texts *)
  assert (HRMc : rp_RM RP Sc (1 + (m - 1 + 1 + kr))) by (apply (lf_rm_cast RP Sc _ _ HRM); clear - Hm; lia).
  eapply SRr_bind.
  { eapply (lf_call_drop_x LA lc lines (m - 1) Wc (ms_regs ms2) (ms_mem ms2) (spZ regs0)
      (blk_FP (list_blks l)) ly S Hp W mem0 md0 lyc Sc Hpc _ _ (getr (ms_regs ms2) 1) (m - 1 + 1 + kr)%nat
      HLG HZS HROM2 HLA8 ltac:(rewrite Hlcn; unfold AREC; lia) Hsp0 HJ HLc2 Hi1 HMOf HRMc HCNT).
    - rewrite Q10, E8. reflexivity.
    - rewrite Q11. rewrite denot_lit_U.
      rewrite (lf_U_decw E (SOff 10 0) (Z.of_nat m) (lf_S_atom E 10 (Z.of_nat m) E10 ltac:(lia)) ltac:(lia)).
      unfold w64. f_equal. lia.
    - unfold spZ at 1. rewrite Q2, Usp. lia.
    - rewrite Q3, E3. exact Hgp.
    - rewrite Q4, E4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1, unsigned_lit_small by lia. lia.
    - unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia.
      clear - HLA1 HLA2 C1. lia.
    - exact HFP. }
  cbv beta. intros W2 c2 Hwle2
    (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HP2 & HAL2 & HBS2 & HPK2 & HER2 & HFR2 & HML2 & HRM2 & KH2).
  rewrite Q1.
  pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  (* ---- the state at 0x866e0, afresh: the dropped list, one record shorter ---- *)
  set (lc' := ldrop_list lc (m - 1)) in *.
  assert (Hlc'v : hl_v lc' = hl_v l) by (subst lc'; cbn [ldrop_list hl_v]; exact Hlcv).
  assert (Hlc'cap : hl_cap lc' = hl_cap l) by (subst lc'; cbn [ldrop_list hl_cap]; exact Hlccap).
  assert (Hlc'recs : hl_recs lc' = firstn (m - 1) (hl_recs l)).
  { subst lc'. cbn [ldrop_list hl_recs]. rewrite Hlcrecs, firstn_firstn.
    replace (Nat.min (m - 1) m) with (m - 1)%nat by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). rewrite app_nil_r. reflexivity. }
  assert (Hlc'n : hl_n lc' = Z.of_nat (m - 1)) by (unfold hl_n; rewrite Hlc'recs, length_firstn; lia).
  pose proof HAL2 as (Mv2 & Mn2 & Mc2 & Hw2 & (Hn02 & Hcap2) & _).
  rewrite Hlc'n in Mn2, Hn02. rewrite Hlc'v in Mv2. rewrite Hlc'cap in Mc2, Hcap2.
  (* the blocks: the record the call freed is the last of lc *)
  assert (HPERM2 : forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) ->
    Permutation (ablocks B ly2 S2) (lf_blks l (m - 1) ++ rest)).
  { intros rest Hpp. pose proof (HPERM rest Hpp) as Hp1. destruct HBS2 as (b1 & b2 & Ea1 & Ea2).
    rewrite Ea1 in Hp1. rewrite Ea2.
    assert (Hnth : nth (m - 1) (hl_recs lc) (0, []) = nth (m - 1) (hl_recs l) (0, []))
    by (rewrite Hlcrecs; apply lf_nth_firstn; lia).
    rewrite Hnth in Hp1. unfold lf_blks in Hp1 |- *.
    assert (Hfl : firstn m (hl_recs l) = firstn (m - 1) (hl_recs l) ++ [nth (m - 1) (hl_recs l) (0, [])])
    by (replace m with (Datatypes.S (m - 1)) at 1 by lia; apply lf_firstn_last; lia).
    rewrite Hfl in Hp1.
    rewrite map_app in Hp1. cbn [map] in Hp1.
    exact (lf_perm_drop2 b1 b2 _ _ rest _ Hp1). }
  assert (HFRS2 : frames S2 = frames S) by (rewrite HFR2; exact HFRS).
  (* the live counts: the call freed one block *)
  assert (HCNT2 : cnt_ok RP (ablocks B ly2 S2)).
  { destruct HBS2 as (b1 & b2 & Ea1 & Ea2). rewrite Ea2. rewrite Ea1 in HCNT. exact (lf_cnt_del RP b1 _ b2 HCNT). }
  assert (HML2' : mo_le MT S S2 ((hl_n l - Z.of_nat (m - 1)) * mo_free MT)).
  { replace ((hl_n l - Z.of_nat (m - 1)) * mo_free MT) with ((hl_n l - Z.of_nat m) * mo_free MT + mo_free MT)
    by (replace (Z.of_nat (m - 1)) with (Z.of_nat m - 1) by lia; ring).
    exact (mle_station MT S Sc S2 _ _ MLAW HMLE HML2). }
  assert (HAPK3 : apres_kept B W mem0 W2 mem2)
  by (intros a Hi Hno Herr Hpp; exact (HPK2 a Hi Hno Herr (HAPK2 a Hi Hno Herr Hpp))).
  assert (ERR3 : forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem0 (as_errno B + j))
  by (intros j Hj; rewrite (HER2 j Hj); exact (ERR2 j Hj)).
  assert (N2 : getr regs2 2 = getr (ms_regs ms2) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (N3 : getr regs2 3 = getr (ms_regs ms2) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (N4 : getr regs2 4 = getr (ms_regs ms2) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (N8 : getr regs2 8 = getr (ms_regs ms2) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (N9 : getr regs2 9 = getr (ms_regs ms2) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (N18 : getr regs2 18 = getr (ms_regs ms2) 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (N19 : getr regs2 19 = getr (ms_regs ms2) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (N21 : getr regs2 21 = getr (ms_regs ms2) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (N22 : getr regs2 22 = getr (ms_regs ms2) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  assert (N23 : getr regs2 23 = getr (ms_regs ms2) 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (N24 : getr regs2 24 = getr (ms_regs ms2) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
  assert (N25 : getr regs2 25 = getr (ms_regs ms2) 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
  assert (N26 : getr regs2 26 = getr (ms_regs ms2) 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
  assert (N27 : getr regs2 27 = getr (ms_regs ms2) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  assert (HRL2 : lf_regsL regs2 regs0 LA).
  { unfold lf_regsL.
    split; [rewrite N2, Q2, E2; reflexivity|].
    split; [rewrite N3, Q3, E3; reflexivity|].
    split; [rewrite N4, Q4, E4; reflexivity|].
    split; [rewrite N8, Q8, E8; reflexivity|].
    split; [rewrite N9, Q9, D9; reflexivity|].
    split; [rewrite N18, Q18, E18; reflexivity|].
    split; [rewrite N19, Q19, D19; reflexivity|].
    split; [rewrite N21, Q21, E21; reflexivity|].
    split; [rewrite N22, Q22, E22; reflexivity|].
    split; [rewrite N23, Q23, E23; reflexivity|].
    split; [rewrite N24, Q24, E24; reflexivity|].
    split; [rewrite N25, Q25, E25; reflexivity|].
    split; [rewrite N26, Q26, E26; reflexivity|].
    rewrite N27, Q27, E27; reflexivity. }
  assert (Hfr2 : lf_frame W2 mem2 (spZ regs0) regs0).
  { intros i Hi. unfold arm in *. apply (val_mem_kept SEGS (w_H Wc) (w_H W2) (ms_mem ms2) mem2); [|].
    - intros j Hj. apply KH2; [unfold alloc_ceiling in *; lia | lia].
    - pose proof (Hfr i Hi) as Hslot. unfold arm in Hslot.
      apply (val_mem_kept SEGS (w_H Wc) (w_H Wc) memc (ms_mem ms2)); [|exact Hslot].
      intros j Hj. apply K12; lia. }
  destruct (lf_cut_x A_lf_ret W2 ly2 S2 Hp2 mem2 md2 regs2 regs0 LA (hl_v l) (hl_cap l) (Z.of_nat (m - 1))
    HAR2 HRL2 Hsp0 Hfr2 HLA1 HLA2 HZS Mv2 Mn2 Mc2 Hw2 ltac:(rewrite <- Hlcv; exact Hv64)
    ltac:(lia) ltac:(lia)) as [HS2 SHOK2].
  clear HS. rename HS2 into HS. rename SHOK2 into SHOK2'.
  remember (Eimg (Ereg regs2 (lf_xl (hl_v l) (hl_cap l) (Z.of_nat (m - 1)) regs0))) as Eb eqn:HEb in HS.
  rewrite <- HEb in SHOK2'.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (EEb : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Eb n = getr regs2 rr)
  by (intros n rr Hn; subst Eb; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (Eb2 : ew Eb 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEb 2%nat 2%bv eq_refl); exact (proj1 HRL2)).
  assert (Eb8 : ew Eb 8 = Z_to_bv 64 LA) by (rewrite (EEb 8%nat 8%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 HRL2))))).
  assert (Eb34 : ew Eb 34 = Z_to_bv 64 (Z.of_nat (m - 1))) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (Eb3 : ew Eb 3 = getr regs0 3) by (rewrite (EEb 3%nat 3%bv eq_refl); exact (proj1 (proj2 HRL2))).
  assert (Eb4 : ew Eb 4 = getr regs0 4) by (rewrite (EEb 4%nat 4%bv eq_refl); exact (proj1 (proj2 (proj2 HRL2)))).
  assert (Eb18 : ew Eb 18 = Z_to_bv 64 SB) by (rewrite (EEb 18%nat 18%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))).
  assert (Eb21 : ew Eb 21 = getr regs0 21) by (rewrite (EEb 21%nat 21%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))).
  assert (Eb22 : ew Eb 22 = getr regs0 22) by (rewrite (EEb 22%nat 22%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))).
  assert (Eb23 : ew Eb 23 = getr regs0 23) by (rewrite (EEb 23%nat 23%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))))).
  assert (Eb24 : ew Eb 24 = getr regs0 24) by (rewrite (EEb 24%nat 24%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))).
  assert (Eb25 : ew Eb 25 = getr regs0 25) by (rewrite (EEb 25%nat 25%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))))))).
  assert (Eb26 : ew Eb 26 = getr regs0 26) by (rewrite (EEb 26%nat 26%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))))).
  assert (Eb27 : ew Eb 27 = getr regs0 27) by (rewrite (EEb 27%nat 27%bv eq_refl); exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))))).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 (hl_v l)) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (hl_cap l)) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs0 - 48) by (rewrite Eb2; apply unsigned_lit_small; lia).
  assert (U8b : bv_unsigned (ew Eb 8) = LA) by (rewrite Eb8; apply unsigned_lit_small; lia).
  assert (ESVb : forall i, (i < 6)%nat -> ew Eb (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
  by (intros i Hi; subst Eb; exact (lf_ew_saved regs2 regs0 _ _ _ i Hi)).
  clear HEb.
  (* 0x866e0 the shadow byte of l->n, 0x866e8 a0 = l->n, 0x866ec bnez a0 *)
  paj_run_tok_x RUN HS HJ2 SHOK2' lf_Bspan. { lf_awrL Uspb U8b HLG. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hf into HFr3 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hgr into HGr3 end.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) mem2 (ms_mem ms3) HFr3 a Ha).
    intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite U8b in Hr; lia]. }
  psrr_branch_tok RUN BR HS SHOK2' lf_Bspan.
  + (* l->n <> 0: back to the loop head *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
    rewrite trap_br_ne, (U_atom Eb 34 (Z.of_nat (m - 1)) Eb34 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Bool.negb_true_iff, Z.eqb_neq in Hbr.
    assert (Hz : (m - 1 =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hz in HK.
    paj_run_to_tok_x RUNTO HS HJ2 SHOK2' lf_Bspan A_lf_loop.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awrL Uspb U8b HLG. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
    { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [lia | rewrite U8b in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    destruct (lf_den_regs Eb LA Eb8 Eb18 ltac:(lia)) as (D9b & D19b).
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1f. cbn [ms_mem restrict] in RL1f.
    apply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + k1)).
    * unfold lf_inv_x.
      split; [exact HJ2|].
      split.
      { unfold lf_regsL.
        split; [rewrite F2, Eb2; reflexivity|].
        split; [rewrite F3, Eb3; reflexivity|].
        split; [rewrite F4, Eb4; reflexivity|].
        split; [rewrite F8, Eb8; reflexivity|].
        split; [rewrite F9, D9b; reflexivity|].
        split; [rewrite F18, Eb18; reflexivity|].
        split; [rewrite F19, D19b; reflexivity|].
        split; [rewrite F21, Eb21; reflexivity|].
        split; [rewrite F22, Eb22; reflexivity|].
        split; [rewrite F23, Eb23; reflexivity|].
        split; [rewrite F24, Eb24; reflexivity|].
        split; [rewrite F25, Eb25; reflexivity|].
        split; [rewrite F26, Eb26; reflexivity|].
        rewrite F27, Eb27; reflexivity. }
      split.
      { intros i Hi. unfold arm.
        pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
        eapply (slot_of_region Eb _ (spZ regs0 - 48) _ 0 48 0 0 (8 * Z.of_nat i) (SOff (35 + i) 0)).
        - exact RS0.
        - exact Uspb.
        - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
        - cbn [sv_denot]. rewrite (ESVb i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - exact Hr. }
      split.
      { exists lc'. split; [exact Hlc'v|]. split; [exact Hlc'cap|]. split; [exact Hlc'recs|].
        destruct (lf_head_of_region Eb W2 (ms_mem msf) LA (hl_v l) (Z.of_nat (m - 1)) (hl_cap l) RL1f U8b Eb32 Eb34 Eb33
          ltac:(rewrite <- Hlcv; exact Hv64) ltac:(lia) ltac:(lia)) as (FL0 & FL8 & FL12 & FAWR).
        apply (lf_alist_relocate_x ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) LA lc' lines HAR2 HAL2 HLG);
        [ intros a Hh Hno; rewrite (K4 a ltac:(unfold alloc_ceiling in *; lia) Hno);
          exact (K3 a ltac:(unfold alloc_ceiling in *; lia) Hno)
        | rewrite Hlc'v; exact FL0 | rewrite Hlc'n; exact FL8 | rewrite Hlc'cap; exact FL12 | exact FAWR ]. }
      split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
      split.
      { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
        exact (lf_apresent_grows _ _ _ a HGr3 (HAPK3 a Hi Hno Herr Hpp)). }
      split.
      { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
        rewrite (K4 (as_errno B + j) ltac:(lia) Gb). rewrite (K3 (as_errno B + j) ltac:(lia) Gb). exact (ERR3 j Hj). }
      split; [exact HRM2 | exact HCNT2].
    * intros _. rewrite F10, Eb34. reflexivity.
  + (* l->n = 0: out of the loop, to 0x86700 *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
    rewrite trap_br_ne, (U_atom Eb 34 (Z.of_nat (m - 1)) Eb34 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Bool.negb_false_iff, Z.eqb_eq in Hbr.
    assert (Hz : (m - 1 =? 0)%nat = true) by (apply Nat.eqb_eq; lia).
    rewrite Hz in HK.
    paj_run_to_tok_x RUNTO HS HJ2 SHOK2' lf_Bspan A_lf_done.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awrL Uspb U8b HLG. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
    { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [lia | rewrite U8b in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    destruct (lf_den_regs Eb LA Eb8 Eb18 ltac:(lia)) as (D9b & D19b).
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1f. cbn [ms_mem restrict] in RL1f.
    apply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + k1)).
    * unfold lf_inv_x.
      split; [exact HJ2|].
      split.
      { unfold lf_regsL.
        split; [rewrite F2, Eb2; reflexivity|].
        split; [rewrite F3, Eb3; reflexivity|].
        split; [rewrite F4, Eb4; reflexivity|].
        split; [rewrite F8, Eb8; reflexivity|].
        split; [rewrite F9, D9b; reflexivity|].
        split; [rewrite F18, Eb18; reflexivity|].
        split; [rewrite F19, D19b; reflexivity|].
        split; [rewrite F21, Eb21; reflexivity|].
        split; [rewrite F22, Eb22; reflexivity|].
        split; [rewrite F23, Eb23; reflexivity|].
        split; [rewrite F24, Eb24; reflexivity|].
        split; [rewrite F25, Eb25; reflexivity|].
        split; [rewrite F26, Eb26; reflexivity|].
        rewrite F27, Eb27; reflexivity. }
      split.
      { intros i Hi. unfold arm.
        pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
        eapply (slot_of_region Eb _ (spZ regs0 - 48) _ 0 48 0 0 (8 * Z.of_nat i) (SOff (35 + i) 0)).
        - exact RS0.
        - exact Uspb.
        - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
        - cbn [sv_denot]. rewrite (ESVb i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - exact Hr. }
      split.
      { exists lc'. split; [exact Hlc'v|]. split; [exact Hlc'cap|]. split; [exact Hlc'recs|].
        destruct (lf_head_of_region Eb W2 (ms_mem msf) LA (hl_v l) (Z.of_nat (m - 1)) (hl_cap l) RL1f U8b Eb32 Eb34 Eb33
          ltac:(rewrite <- Hlcv; exact Hv64) ltac:(lia) ltac:(lia)) as (FL0 & FL8 & FL12 & FAWR).
        apply (lf_alist_relocate_x ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) LA lc' lines HAR2 HAL2 HLG);
        [ intros a Hh Hno; rewrite (K4 a ltac:(unfold alloc_ceiling in *; lia) Hno);
          exact (K3 a ltac:(unfold alloc_ceiling in *; lia) Hno)
        | rewrite Hlc'v; exact FL0 | rewrite Hlc'n; exact FL8 | rewrite Hlc'cap; exact FL12 | exact FAWR ]. }
      split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
      split.
      { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
        exact (lf_apresent_grows _ _ _ a HGr3 (HAPK3 a Hi Hno Herr Hpp)). }
      split.
      { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
        rewrite (K4 (as_errno B + j) ltac:(lia) Gb). rewrite (K3 (as_errno B + j) ltac:(lia) Gb). exact (ERR3 j Hj). }
      split; [exact HRM2 | exact HCNT2].
    * intros Hne. exfalso. apply Hne. lia.
Qed.

(* ---- after the loop (0x86700): free(l->v) (free(NULL) when the list never had a vector), l->v = 0,
   l->cap = 0, the epilogue and the ret ---- *)
Lemma lf_exit_x : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines ->
lf_inv_x W ly S Hp regs0 mem0 md0 LA l lines 0 kr Wc lyc Sc Hpc regs memc mdc kk ->
SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HINV.
destruct HCTX as (HPRE & HL & HLG & HZS & HLA8 & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra0 & Hra04 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & (lc & Hlcv & Hlccap & Hlcrecs & HLc) & HPERM & HFRS & HMLE & HAPK & HERR & HRM0 & HCNT).
(* the room: the vector's free is the one left *)
assert (HRM : rp_RM RP Sc (1 + kr)) by (apply (lf_rm_cast RP Sc _ _ HRM0); clear - kr; lia).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hlcn : hl_n lc = 0) by (unfold hl_n; rewrite Hlcrecs; reflexivity).
pose proof HLc as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & _).
rewrite Hlcn in Mn. rewrite Hlcv in Mv. rewrite Hlccap in Mc, Hcap.
assert (HVEC : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc)).
{ intros Hcp. destruct Hvc as [[Hc0 _] | (_ & Hin & _)]; [rewrite Hlccap in Hc0; lia|].
  rewrite Hlcv, Hlccap in Hin. exact Hin. }
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hlcv in Hv0; lia|].
  destruct (lf_blk_bounds_x lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as [Hb1 Hb2].
  rewrite Hlcv in Hb1. unfold req_size, AREC in Hb2. rewrite Hlcv, Hlccap in Hb2.
  destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) ((hl_n l - Z.of_nat 0) * mo_free MT) (mo_free MT) MLAW HMO HMLE MF0).
  unfold lf_cost. cbn [Z.of_nat]. assert (Hn0l : 0 <= hl_n l) by (unfold hl_n; lia). nia. }
(* ---- the cut at 0x86700 ---- *)
destruct (lf_cut_x A_lf_done Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) 0
  HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hv64 ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) 0 regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = getr regs0 21) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = getr regs0 22) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regs0 23) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs0 24) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = getr regs0 25) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (ESV : forall i, (i < 6)%nat -> ew E (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
clear HE.
(* 0x86700 .. the jal to free *)
paj_run_tok_x RUN HS HJ SHOK lf_Bspan. { lf_awrL Usp U8 HLG. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => rename Hgr into HGr1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr1 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -48) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (R10s : getr (ms_regs ms) 10 = w64 (hl_v l)) by (rewrite Q10; exact E32).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, E4; exact Htp).
assert (HS0 : s0Z (ms_regs ms) = LA) by (unfold s0Z; rewrite Q8; exact U8).
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
rewrite HBfree.
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0xa0] *)
assert (HCTXX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0xa0); [exact HCTX_lf_exit|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
eapply SRr_bind with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 /\
  ajournal_x SEGS B PST ARx LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) /\
  aregs_preserved (ms_regs ms) regs4 /\
  (forall rest, Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest) -> Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames Sc /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 + -48 - ASTACK <= a < spZ regs0 + -48) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  mo_le MT Sc S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H Wc) (ms_mem ms) (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H W4) mem4 a)).
{ destruct (Z.eq_dec (hl_cap l) 0) as [Hc0 | Hc0].
  - assert (Hv0 : hl_v l = 0)
    by (destruct Hvc as [[_ H] | (Hcp & _)]; [rewrite Hlcv in H; exact H | rewrite Hlccap in Hcp; lia]).
    eapply SRr_mono.
    { exact (AFREEN Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (-48) (getr (ms_regs ms) 1) [] kr HJi ltac:(rewrite R10s, Hv0; reflexivity) Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-48) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXX HRM HCNT HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_eq (hl_cap l) 0) Hc0) in Hpp. cbn [firstn map app] in Hpp.
      exact (Permutation_trans HPm Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | exact Hpp].
  - assert (Hcp : 0 < hl_cap l) by lia.
    pose proof (HVEC Hcp) as Hvin.
    eapply SRr_mono.
    { exact (AFREE Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (hl_v l) (AREC * hl_cap l) (-48) (getr (ms_regs ms) 1) [] kr HJi Hvin R10s Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-48) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXX HRM HCNT
        ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (hl_v l) (AREC * hl_cap l) i);
              [unfold list_blks; rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) Hc0); apply in_or_app; left; left; reflexivity | exact Hi]) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. rewrite Eb2. rewrite Eb1 in Hpp. unfold lf_blks in Hpp.
      rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) Hc0) in Hpp.
      cbn [firstn map app] in Hpp. apply Permutation_sym in Hpp. apply Permutation_cons_app_inv in Hpp. exact (Permutation_sym Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | | exact Hpp].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hvin Hb Hi). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJi4 & HP4 & HPM4 & HFR4 & KS4 & KI4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
pose proof (proj1 HJi4) as HAR4.
assert (HJ4 : ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | apply out_none]. }
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 2 (spZ regs0 - 48)); [exact Usp | | intros a Ha; exfalso; lia].
    intros a Ha. apply KS4; [lia | lia].
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 8 LA); [exact U8 | |].
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He). exact (KI4 a Hi Ho He).
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He).
      apply (lf_writable_img Wc W4 (ms_mem ms) mem4 a Hi). exact (HPR4 a Hi Ho He). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 48)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHL Ea (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, lf_SHL. constructor; [|constructor].
  apply (lf_shent8_x Ea ly4 S4 Hp4 W4 mem4 md4 LA HAR4 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 48) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* 0x86718 .. the ret: l->v = 0, l->cap = 0, the epilogue *)
paj_run_tok_x RUN HS HJ4 SHOK2 lf_Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons_awr0; [awr_any; try exact Uspa|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregL lf_lreg base_val]. rewrite U8a.
  intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hf into HFrf end.
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W4) mem4 (ms_mem msf) HFrf a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22.
prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (HPF : aregs_preserved regs0 (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspa. replace (spZ regs0 - 48 + 48) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDa by lia. exact E3.
  - rewrite F4, OLDa by lia. exact E4.
  - rewrite F8, OLDa by lia. exact (ESV 4%nat ltac:(lia)).
  - rewrite F9, OLDa by lia. exact (ESV 3%nat ltac:(lia)).
  - rewrite F18, OLDa by lia. exact (ESV 2%nat ltac:(lia)).
  - rewrite F19, OLDa by lia. exact (ESV 1%nat ltac:(lia)).
  - rewrite F20, OLDa by lia. exact (ESV 0%nat ltac:(lia)).
  - rewrite F21, OLDa by lia. exact E21.
  - rewrite F22, OLDa by lia. exact E22.
  - rewrite F23, OLDa by lia. exact E23.
  - rewrite F24, OLDa by lia. exact E24.
  - rewrite F25, OLDa by lia. exact E25.
  - rewrite F26, OLDa by lia. exact E26.
  - rewrite F27, OLDa by lia. exact E27. }
assert (ER1 : ew E 40 = getr regs0 1) by exact (ESV 5%nat ltac:(lia)).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall n, (n < 512)%nat -> ew Ef n = ew Ea n) by (intros n Hn; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U8f : bv_unsigned (ew Ef 8) = LA) by (rewrite UF by lia; exact U8a).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
assert (VL0 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 0) (N.to_nat 8) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 8) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDa by lia. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 12) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W4 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL1 as (_ & _ & RLw & _).
  cbn [lf_lregL lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U8f in RLw. exact (RLw i Hi). }
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lf_post_x.
exists ly4, S4, Hp4, (ms_regs msf), (ms_mem msf). eexists. exists (kk + 1).
split; [rewrite F1, OLDa by lia; rewrite ER1, Hra0; reflexivity|].
split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [exact HPF|].
split.
{ unfold alist_at, empty_list, hl_n. cbn [hl_v hl_cap hl_recs hl_junk length Z.of_nat].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|]. split; [left; split; reflexivity|]. split; [constructor|]. split; [intros []|]. constructor. }
split; [intros rest Hpp; exact (HPM4 rest (HPERM rest Hpp))|].
split.
{ intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). apply (HPR4 a Hi Hno Herr).
  apply (lf_apresent_grows _ _ _ a HGr1). exact (HAPK a Hi Hno Herr Hpp). }
split.
{ intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
  rewrite (Kf (as_errno B + j) ltac:(lia) Gb). rewrite (HER4 j Hj).
  rewrite (K1 (as_errno B + j) ltac:(lia) Gb). exact (HERR j Hj). }
split; [rewrite HFR4; exact HFRS|].
split; [|exact HRM4].
replace (lf_cost MT l) with (hl_n l * mo_free MT + mo_free MT) by (unfold lf_cost; ring).
replace (hl_n l * mo_free MT) with ((hl_n l - Z.of_nat 0) * mo_free MT) by (cbn [Z.of_nat]; ring).
exact (mle_station MT S Sc S4 _ _ MLAW HMLE HML4).
Qed.

(* ---- the walk ---- *)
Theorem pb_list_free_x : lf_spec_x B PST ARx MT RP G A_list_freeP.
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HLA8 HL HLG HZS HROM HMO kr HRM0 HCNT0.
assert (HCTX : lf_ctx_x W ly S Hp regs mem md ch LA l lines)
by (unfold lf_ctx_x; split; [exact HPRE|]; split; [exact HL|]; split; [exact HLG|]; split; [exact HZS|];
    split; [exact HLA8|]; split; [exact HROM | exact HMO]).
(* the loop, by induction on the texts left *)
assert (IND : forall m Wc lyc Sc Hpc regsc memc mdc kc, (m <= length (hl_recs l))%nat ->
  lf_inv_x W ly S Hp regs mem md LA l lines m kr Wc lyc Sc Hpc regsc memc mdc kc ->
  (m <> 0%nat -> getr regsc 10 = w64 (Z.of_nat m)) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + if (m =? 0)%nat then A_lf_done else A_lf_loop)) memc (seg_rom SEGS)) mdc)
    (lf_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines kr)).
{ induction m as [|m IH]; intros Wc lyc Sc Hpc regsc memc mdc kc Hml HI H10c; cbn [Nat.eqb].
  - exact (lf_exit_x W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX HI).
  - apply (lf_iter_x (Datatypes.S m) W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX ltac:(lia) HI
      (H10c ltac:(lia))).
    intros Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' HI' H10'.
    replace (Datatypes.S m - 1)%nat with m in * by lia.
    exact (IH Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ltac:(lia) HI' H10'). }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lf_entry_x W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity.
pose proof (lf_errno_facts (spZ regs) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
pose proof (ajournal_gx_init_x SEGS B PST ARx G 0 [] LF_STK (blk_FP (list_blks l)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (lf_extra l))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (EEo 3%nat 3%bv eq_refl); reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (EEo 4%nat 4%bv eq_refl); reflexivity).
assert (E21 : ew E 21 = getr regs 21) by (rewrite (EEo 21%nat 21%bv eq_refl); reflexivity).
assert (E22 : ew E 22 = getr regs 22) by (rewrite (EEo 22%nat 22%bv eq_refl); reflexivity).
assert (E23 : ew E 23 = getr regs 23) by (rewrite (EEo 23%nat 23%bv eq_refl); reflexivity).
assert (E24 : ew E 24 = getr regs 24) by (rewrite (EEo 24%nat 24%bv eq_refl); reflexivity).
assert (E25 : ew E 25 = getr regs 25) by (rewrite (EEo 25%nat 25%bv eq_refl); reflexivity).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (EEo 26%nat 26%bv eq_refl); reflexivity).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EEo 27%nat 27%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ERS : forall i, (i < 6)%nat -> ew E (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_regs regs _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = LA) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (lf_blk_bounds_x ly S Hp W mem md _ _ HAR Hin) as [Hb1 Hb2].
  unfold req_size, AREC in Hb2. destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
destruct (lf_den_regs E LA E10 E35 ltac:(lia)) as (D9 & D19).
clear HE.
unfold cfg_at. change (w64 A_list_freeP) with (Z_to_bv 64 A_list_freeP).
unfold A_list_freeP, A_list_free.
(* the prologue, to the ALIGN8 trap branch *)
paj_run_tok_x RUN HS HJ SHOK lf_Bspan. { lf_awr0 Usp U10 HLG. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms0 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hf into HFr0 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hgr into HGr0 end.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms0) HFr0 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lf0 lf_regions0 In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [stack_region got_regionP bcell_regionP lf_lreg LF_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
(* 0x8669c bnez: the UBSan ALIGN8 trap on LA, never taken *)
psrr_branch_tok RUN BR HS SHOK lf_Bspan.
- exfalso. rewrite (trap_align8 E (SOff 10 0) LA (U_atom E 10 LA E10 ltac:(lia)) HLA8) in Hc. discriminate.
- paj_run_tok_x RUN HS HJ SHOK lf_Bspan. { lf_awr0 Usp U10 HLG. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ => rename Hf into HFr1 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ => rename Hgr into HGr1 end.
  lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr1 end.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  (* 0x866c4 beqz a0: is the list empty? *)
  psrr_branch_tok RUN BR HS SHOK lf_Bspan.
  + (* n = 0: straight to 0x86700 *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
    rewrite trap_br_eq, (U_atom E 33 (hl_n l) E33 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Z.eqb_eq in Hbr.
    assert (Hrn : hl_recs l = []) by (unfold hl_n in Hbr; destruct (hl_recs l); [reflexivity | cbn [length] in Hbr; lia]).
    paj_run_to_tok_x RUNTO HS HJ SHOK lf_Bspan A_lf_done.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awr0 Usp U10 HLG. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
      aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms1) a).
    { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms1) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22.
    prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
    prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3. cbn [ms_mem restrict] in RL3.
    apply (IND 0%nat W ly S Hp (ms_regs msf) (ms_mem msf) _ 0 ltac:(lia)); [|intros Hne; exfalso; apply Hne; reflexivity].
    unfold lf_inv_x.
    split; [exact HJ|].
    split.
    { unfold lf_regsL.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|]. split; [rewrite F9, D9; reflexivity|].
      split; [rewrite F18, E35; reflexivity|]. split; [rewrite F19, D19; reflexivity|].
      split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|].
      split; [rewrite F23, E23; reflexivity|]. split; [rewrite F24, E24; reflexivity|].
      split; [rewrite F25, E25; reflexivity|]. split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split.
    { intros i Hi. unfold arm.
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      replace (spZ regs - 48 + 8 * Z.of_nat i) with (spZ regs + (-48 + 8 * Z.of_nat i)) by ring.
      eapply (slot_of_region E _ (spZ regs) _ (-48) 0 (-48) 0 (-48 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
      - exact RS0.
      - exact Usp.
      - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
      - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - exact Hr. }
    split.
    { exists l. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrn; reflexivity|].
      assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      rewrite Z.add_0_r in VL0.
      assert (HAWR : awr W (ms_mem msf) LA 16).
      { intros i Hi. destruct RL3 as (_ & _ & RLw & _).
        cbn [lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U10 in RLw. exact (RLw i Hi). }
      apply (lf_alist_relocate_x ly S Hp W mem md (ms_mem msf) LA l lines HAR HL HLG);
      [ intros a Hh Hno; rewrite (K2 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        rewrite (K1 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        exact (K0 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno)
      | exact VL0 | exact VL8 | exact VL12 | exact HAWR ]. }
    split; [intros rest Hpp; unfold lf_blks; rewrite Hrn; cbn [firstn map app]; rewrite app_nil_r;
            unfold list_blks in Hpp; rewrite Hrn in Hpp; cbn [map app] in Hpp; rewrite app_nil_r in Hpp; exact Hpp|].
    split; [reflexivity|].
    split; [cbn [Z.of_nat]; unfold hl_n; rewrite Hrn; cbn [length Z.of_nat];
            replace (0 - 0) with 0 by lia; rewrite Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split.
    { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
      apply (lf_apresent_grows _ _ _ a HGr1). exact (lf_apresent_grows _ _ _ a HGr0 Hpp). }
    split.
    { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
      rewrite (K2 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      rewrite (K1 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      exact (K0 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb). }
    (* the room: no text, so only the vector's free (lf_cost MT_rk l = n + 1, n = 0) *)
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk, Hrn. reflexivity.
  + (* n <> 0: into the loop at 0x866d0 *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
    rewrite trap_br_eq, (U_atom E 33 (hl_n l) E33 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Z.eqb_neq in Hbr.
    assert (Hlen0 : (length (hl_recs l) =? 0)%nat = false) by (apply Nat.eqb_neq; unfold hl_n in Hbr; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK lf_Bspan A_lf_loop.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awr0 Usp U10 HLG. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
      aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms1) a).
    { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms1) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3. cbn [ms_mem restrict] in RL3.
    pose proof (IND (length (hl_recs l)) W ly S Hp (ms_regs msf) (ms_mem msf)) as HH.
    rewrite Hlen0 in HH. apply (HH _ 0 (le_n _)); [|intros _; rewrite F10, E33; unfold hl_n; reflexivity].
    unfold lf_inv_x.
    split; [exact HJ|].
    split.
    { unfold lf_regsL.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|]. split; [rewrite F9, D9; reflexivity|].
      split; [rewrite F18, E35; reflexivity|]. split; [rewrite F19, D19; reflexivity|].
      split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|].
      split; [rewrite F23, E23; reflexivity|]. split; [rewrite F24, E24; reflexivity|].
      split; [rewrite F25, E25; reflexivity|]. split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split.
    { intros i Hi. unfold arm.
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      replace (spZ regs - 48 + 8 * Z.of_nat i) with (spZ regs + (-48 + 8 * Z.of_nat i)) by ring.
      eapply (slot_of_region E _ (spZ regs) _ (-48) 0 (-48) 0 (-48 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
      - exact RS0.
      - exact Usp.
      - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
      - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - exact Hr. }
    split.
    { exists l. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite firstn_all; reflexivity|].
      assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      rewrite Z.add_0_r in VL0.
      assert (HAWR : awr W (ms_mem msf) LA 16).
      { intros i Hi. destruct RL3 as (_ & _ & RLw & _).
        cbn [lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U10 in RLw. exact (RLw i Hi). }
      apply (lf_alist_relocate_x ly S Hp W mem md (ms_mem msf) LA l lines HAR HL HLG);
      [ intros a Hh Hno; rewrite (K2 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        rewrite (K1 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        exact (K0 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno)
      | exact VL0 | exact VL8 | exact VL12 | exact HAWR ]. }
    split; [intros rest Hpp; unfold lf_blks; rewrite firstn_all; exact Hpp|].
    split; [reflexivity|].
    split; [unfold hl_n; rewrite Z.sub_diag, Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split.
    { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
      apply (lf_apresent_grows _ _ _ a HGr1). exact (lf_apresent_grows _ _ _ a HGr0 Hpp). }
    split.
    { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
      rewrite (K2 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      rewrite (K1 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      exact (K0 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb). }
    (* the room: one free per text and one for the vector (lf_cost MT_rk l = n + 1) *)
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk. lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk at a world relation R, in the form of image A's twin (lib/A/W_list_free.v
   Section wR: lf_iter_xR, lf_exit_xR, pb_list_free_xR), over image B's own walk above.  Each twin is its strict text with:
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, lf_post_x -> lf_post_xR .. R (W_contract_srlf_xR.v), the
   runs paj_run_x_xG / paj_run_to_x_xG (W_journal_x.v, concluding SRrG SEGS R), the branches paj_branch_xR, composition
   SRrG_bind (R_trans), the return paj_ret_at after SRr_SRrG (WLE_R), and each lemma name L -> LR.  The exit's free /
   free(NULL) (returning to list_free + 0xa0) takes the R forms of the free rules (W_journal_x.v Section hc), which also
   take the call-boundary premise RO on the call memory (part 3c removed their memnorm premise): RO_ARx gives it from
   the inner journal's ARx at the call state.
   Each list_drop call takes list_drop at R as the premise LD_R (W_contract_xR_g3.v ldrop_spec_xR at the callee's own
   globals G' = lf_G1 LA: the shape of image B's pb_list_drop_ro_xR), lifted to this walk's journal by lf_gx_call_xR
   (ajournal_gx_sub_xR with R_trans, ajournal_gx_G_mono_xR).  The strict lemmas above keep their text and proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
(* list_drop at R, at any globals G' it can run at (gx_ok, gx_rt, rom_out): image B's pb_list_drop_ro_xR's statement *)
Hypothesis LD_R : forall G', gx_ok SEGS B G' -> gx_rt B G' -> rom_out SEGS B G' -> ldrop_spec_xR B PST ARx R MT RP G' A_list_dropP.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRG := paj_branch_xR (PI := PI) (R := R).
(* :674 lf_keep_hi_x *)
Lemma lf_keep_hi_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H Wc) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (lf_inG_lo a (Hsub a Hc)). unfold kLowMemEnd in *. lia.
Qed.
(* :688 lf_frames_of_x *)
Lemma lf_frames_of_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 -> frames S2 = frames Sc.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
Qed.
(* :694 lf_gx_call_x *)
Lemma lf_gx_call_xR : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
eapply (SRrG_mono SEGS R).
{ apply Hcallee. exact (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi
    Hsp Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G STK sp0 0 [] FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k
  STK1 (sp0 + o) 0 [] FP1 [] ly2 S2 Hp2 W2 mem2 md2 k1 HJ);
[ exact (ajournal_gx_G_mono_xR SEGS B PST ARx G1 G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 HGsub HJ1)
| lia | lia | lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.
(* :739 lf_inv_x *)
Definition lf_inv_xR (W : world SEGS) ly S (Hp : list Z) regs0 mem0 md0 (LA : Z) (l : hlist) (lines : bool) (m kr : nat)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regs : bvmap 5 word) memc mdc (kk : Z) : Prop :=
ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk /\
lf_regsL regs regs0 LA /\ lf_frame Wc memc (spZ regs0) regs0 /\
(exists lc, hl_v lc = hl_v l /\ hl_cap lc = hl_cap l /\ hl_recs lc = firstn m (hl_recs l) /\
  alist_at B lyc Sc Wc memc LA lc lines) /\
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l m ++ rest)) /\
frames Sc = frames S /\ mo_le MT S Sc ((hl_n l - Z.of_nat m) * mo_free MT) /\ apres_kept B W mem0 Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) /\
rp_RM RP Sc (m + 1 + kr) /\ cnt_ok RP (ablocks B lyc Sc).
(* :774 lf_call_drop_x: each list_drop call through LD_R in place of lf_ldrop_x *)
Lemma lf_call_drop_xR : forall (LA : Z) (lc : hlist) (lines : bool) (i : nat)
(Wc : world SEGS) regsT memT sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k raw (kr : nat),
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 -> rom_view SEGS Wc memT ->
LA mod 8 = 0 -> AREC * (hl_n lc - 1 - Z.of_nat i) < 2 ^ 32 -> lf_sp0 sp0 ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK sp0 FP ly S Hp W0 mem0 md0 [] lyc Sc Hpc Wc memT mdc k ->
alist_at B lyc Sc Wc memT LA lc lines ->
(i < length (hl_recs lc))%nat -> mo_ok MT Sc (mo_free MT) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
getr regsT 10 = w64 LA -> getr regsT 11 = w64 (Z.of_nat i) -> spZ regsT = sp0 + -48 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsT < alloc_ceiling ->
(forall b n, In (b, n) (list_blks lc) -> forall j, 0 <= j < req_size n -> inFP FP (b + j)) ->
SRrG SEGS R Wc (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_drop)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK sp0 FP ly S Hp W0 mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 aregs_preserved regsT regs2 /\
 alist_at B ly2 S2 W2 mem2 LA (ldrop_list lc i) lines /\
 (exists b1 b2, ablocks B lyc Sc = b1 ++ (fst (nth i (hl_recs lc) (0, [])),
   Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
 apres_kept B Wc memT W2 mem2 /\
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H Wc) memT (as_errno B + j)) /\
 frames S2 = frames Sc /\ mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + -48 - LDROP_STK <= a < sp0 + -48) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memT a)).
Proof.
intros LA lc lines i Wc regsT memT sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k raw kr
HGL HZS HROM HLA8 HCAP Hsp0 HJ HL Hi HMO HRM HCNT H10 H11 Hsp Hgp Htp Hra Hraw Hra4 Hs0 HFP.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HGL) as (HLA1 & HLA2 & _).
destruct Hsp0 as (Hal & Hsp1 & Hsp2).
assert (WS : LF_STK = 16496) by reflexivity. assert (WD : LDROP_STK = 16448) by reflexivity.
assert (Hsub : forall a, inG (lf_G1 LA) a -> inG G a)
by (intros a Ha; apply HGL; exact (proj1 (lf_G1_in LA a) Ha)).
assert (HP1 : gx_prog_x B ARx (lf_G1 LA))
by (exact (gx_prog_sub_x B ARx (lf_G1 LA) G Hsub (conj HG (conj HGR (conj HRO (conj GX_ROM (conj GX_W GSHV))))))).
pose proof HP1 as (HG1 & HGR1 & HRO1 & _).
(* the vector lies in the heap, so off this frame; when cap = 0 the range is empty *)
assert (HVEC : forall a, hl_v lc <= a < hl_v lc + AREC * hl_cap lc -> 4096 <= a < alloc_ceiling).
{ intros a Ha. pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
  destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Ha; unfold AREC in Ha; lia|].
  destruct (lf_blk_bounds_x lyc Sc Hpc Wc memT mdc _ _ HARc Hin) as [Hb1 Hb2].
  assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
  by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
  rewrite Rq in Hb2. lia. }
eapply (SRrG_mono SEGS R).
{ eapply (lf_gx_call_xR (lf_G1 LA) Wc regsT memT (BASE + AF_fr_list_drop) LF_STK sp0 FP ly S Hp W0 mem0 md0 lyc Sc Hpc mdc k
    LDROP_STK [(hl_v lc, hl_v lc + AREC * hl_cap lc);
      (fst (nth i (hl_recs lc) (0, [])), fst (nth i (hl_recs lc) (0, [])) + req_size (Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1))]
    (-48) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 k1 =>
       alist_at B ly2 S2 W2 mem2 LA (ldrop_list lc i) lines /\
       (exists b1 b2, ablocks B lyc Sc = b1 ++ (fst (nth i (hl_recs lc) (0, [])),
         Z.of_nat (length (snd (nth i (hl_recs lc) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
       apres_kept B Wc memT W2 mem2 /\
       (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H Wc) memT (as_errno B + j)) /\
       mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr)
    Hsub HJ Hsp ltac:(reflexivity) ltac:(lia) ltac:(unfold LDROP_STK, LDROP_FRAME, ASTACK; lia)
    ltac:(unfold LDROP_STK, LF_STK, LDROP_FRAME, ASTACK; lia) Hgp Htp Hra Hraw Hra4
    ltac:(apply achain_low; exact Hs0)).
  - intros HPRE1. eapply (SRrG_mono SEGS R).
    { exact (LD_R (lf_G1 LA) HG1 HGR1 HRO1 Wc lyc Sc Hpc regsT memT mdc [] LA lc lines i HPRE1 H10 H11 HL Hi
        HLA8 ltac:(lia) HCAP HZS
        ltac:(intros a Ha; split; [apply (proj2 (lf_G1_in LA a)); exact Ha | rewrite Hsp; lia])
        ltac:(intros a Ha; pose proof (HVEC a Ha); rewrite Hsp; lia) HMO kr HRM HCNT HROM). }
    cbv beta. unfold ldrop_post_xR.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPK & HER & HAL & HBS & HML & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, 1.
    split; [rewrite Hra; reflexivity|]. split; [rewrite <- Hsp; exact HJ2|].
    split; [exact HP2|]. split; [exact HAL | split; [exact HBS | split; [exact HPK | split; [exact HER |
      split; [exact HML | exact HRM2]]]]].
  - intros a Ha. left. split.
    + destruct Ha as (r & Hr & Hra2). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra2.
      * pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
        destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Hra2; unfold AREC in Hra2; lia|].
        assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
        by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
        replace a with (hl_v lc + (a - hl_v lc)) by lia.
        apply (HFP (hl_v lc) (AREC * hl_cap lc)); [unfold list_blks; apply in_or_app; left;
          rewrite (proj2 (Z.eqb_neq (hl_cap lc) 0) ltac:(lia)); left; reflexivity | rewrite Rq; lia].
      * set (r := nth i (hl_recs lc) (0, [])) in *.
        replace a with (fst r + (a - fst r)) by lia.
        apply (HFP (fst r) (Z.of_nat (length (snd r)) + 1)); [unfold list_blks; apply in_or_app; right;
          exact (in_map (fun q : Z * list byte => (fst q, Z.of_nat (length (snd q)) + 1)) _ r (nth_In _ _ Hi)) | lia].
    + destruct Ha as (r & Hr & Hra2). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra2.
      * pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & _).
        destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hc0 in Hra2; unfold AREC in Hra2; lia|].
        assert (Rq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
        by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
        exists (hl_v lc), (AREC * hl_cap lc). split; [exact Hin | rewrite Rq; lia].
      * set (r := nth i (hl_recs lc) (0, [])) in *.
        pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & HFA).
        exists (fst r), (Z.of_nat (length (snd r)) + 1).
        split; [exact (proj1 (proj1 (Forall_forall _ _) HFA r (nth_In _ _ Hi))) | lia]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJa & HJb & HP & HAL & HBS & HPK & HER & HML & HRM2).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJa|]. split; [exact HP|]. split; [exact HAL|].
split; [exact HBS|]. split; [exact HPK|]. split; [exact HER|].
split; [exact (lf_frames_of_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb)|]. split; [exact HML|]. split; [exact HRM2|].
intros a Ha Hno. exact (lf_keep_hi_xR (lf_G1 LA) LDROP_STK (sp0 + -48) _ lyc Sc Hpc Wc memT mdc ly2 S2 Hp2 W2 mem2 md2 k1
  Hsub HJb a Ha Hno).
Qed.
(* :912 lf_iter_x *)
Lemma lf_iter_xR : forall (m : nat) W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> (1 <= m <= length (hl_recs l))%nat ->
lf_inv_xR W ly S Hp regs0 mem0 md0 LA l lines m kr Wc lyc Sc Hpc regs memc mdc kk ->
getr regs 10 = w64 (Z.of_nat m) ->
(forall Wc' lyc' Sc' Hpc' regs' memc' mdc' kk',
   lf_inv_xR W ly S Hp regs0 mem0 md0 LA l lines (m - 1) kr Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ->
   ((m - 1)%nat <> 0%nat -> getr regs' 10 = w64 (Z.of_nat (m - 1))) ->
   SRrG SEGS R Wc' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + if (m - 1 =? 0)%nat then A_lf_done else A_lf_loop)) memc' (seg_rom SEGS)) mdc')
     (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr)) ->
SRrG SEGS R Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) memc (seg_rom SEGS)) mdc)
  (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros m W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX Hm HINV H10 HK.
destruct HCTX as (HPRE & HL & HLG & HZS & HLA8 & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra0 & Hra04 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity. assert (WD : LDROP_STK = 16448) by reflexivity.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & (lc & Hlcv & Hlccap & Hlcrecs & HLc) & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hlcn : hl_n lc = Z.of_nat m) by (unfold hl_n; rewrite Hlcrecs, length_firstn; lia).
pose proof HLc as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
rewrite Hlcn in Mn, Hn0.
assert (Hcap0 : 0 < hl_cap lc) by lia.
assert (Hvin : In (hl_v lc, AREC * hl_cap lc) (ablocks B lyc Sc))
by (destruct Hvc as [[Hc0 _] | (_ & Hin & _)]; [lia | exact Hin]).
destruct (lf_blk_bounds_x lyc Sc Hpc Wc memc mdc _ _ HARc Hvin) as [Hvb1 Hvb2].
assert (Rqv : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
by (unfold req_size; destruct (Z.eqb_spec (AREC * hl_cap lc) 0); [unfold AREC in *; lia | reflexivity]).
rewrite Rqv in Hvb2.
assert (Hv64 : 0 <= hl_v lc < 2 ^ 64) by (unfold alloc_ceiling, AREC in *; lia).
(* the records of lc are records of l, so its blocks are in this walk's footprint *)
assert (HSUBB : forall b n, In (b, n) (list_blks lc) -> In (b, n) (list_blks l)).
{ unfold list_blks. rewrite Hlcv, Hlccap, Hlcrecs. intros b n Hin. apply in_app_or in Hin as [H|H].
  - apply in_or_app. left. exact H.
  - apply in_or_app. right. apply in_map_iff in H as (r & <- & Hr).
    apply (in_map (fun q : Z * list byte => (fst q, Z.of_nat (length (snd q)) + 1))).
    rewrite <- (firstn_skipn m (hl_recs l)). apply in_or_app. left. exact Hr. }
assert (HFP : forall b n, In (b, n) (list_blks lc) -> forall j, 0 <= j < req_size n -> inFP (blk_FP (list_blks l)) (b + j))
by (intros b n Hin j Hj; exact (inFP_ablocks_fp (list_blks l) b n j (HSUBB b n Hin) Hj)).
(* the meter: one free fits in what is left of lf_cost *)
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) ((hl_n l - Z.of_nat m) * mo_free MT) (mo_free MT) MLAW HMO HMLE MF0).
  unfold lf_cost. pose proof HL as (_ & _ & _ & _ & (Hn0' & _) & _).
  assert (Hmn : Z.of_nat m <= hl_n l) by (unfold hl_n; lia). nia. }
(* ---- the cut at the loop head ---- *)
destruct (lf_cut_x A_lf_loop Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v lc) (hl_cap lc) (Z.of_nat m)
  HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hv64 ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v lc) (hl_cap lc) (Z.of_nat m) regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat m)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = getr regs0 21) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = getr regs0 22) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regs0 23) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs0 24) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = getr regs0 25) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat m)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (ESV : forall i, (i < 6)%nat -> ew E (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
clear HE.
unfold A_lf_loop.
(* 0x866d0 addiw a1,a0,-1; 0x866d4 bge a1,a0 -> the UBSan int32 trap, never taken *)
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan. { lf_awrL Usp U8 HLG. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) |- _ => rename Hf into HFr1 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) |- _ => rename Hgr into HGr1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms1) HFr1 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
psrr_branch_tok RUNG BRG HS SHOK lf_Bspan.
- exfalso. rewrite (trap_decw E (SOff 10 0) (Z.of_nat m) (lf_S_atom E 10 (Z.of_nat m) E10 ltac:(lia)) ltac:(lia)) in Hc.
  discriminate.
- (* 0x866d8 mv a0,s0; 0x866dc jal list_drop *)
  paj_run_to_tok_xR RUNTOG HS HJ SHOK lf_Bspan AF_fr_list_drop. { lf_awrL Usp U8 HLG. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ => rename Hf into HFr2 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ => rename Hgr into HGr2 end.
  lazymatch type of HFr2 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) (ms_mem ms1) a).
  { intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite U8 in Hr; lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg_raw HS (9%bv : bv 5) Q9. prreg_raw HS (11%bv : bv 5) Q11. prreg_raw HS (19%bv : bv 5) Q19.
  destruct (lf_den_regs E LA E8 E18 ltac:(lia)) as (D9 & D19).
  (* the list's predicate and errno's view at the call site *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
  destruct (lf_head_of_region E Wc (ms_mem ms2) LA (hl_v lc) (Z.of_nat m) (hl_cap lc) RL1 U8 E32 E34 E33
    Hv64 ltac:(lia) ltac:(lia)) as (VL0 & VL8 & VL12 & HAWR).
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha Hno; rewrite (K2 a Ha Hno); exact (K1 a Ha Hno)).
  assert (HLc2 : alist_at B lyc Sc Wc (ms_mem ms2) LA lc lines).
  { apply (lf_alist_relocate_x lyc Sc Hpc Wc memc mdc (ms_mem ms2) LA lc lines HARc HLc HLG);
    [ intros a Hh Hno; exact (K12 a ltac:(unfold alloc_ceiling in *; lia) Hno)
    | exact VL0 | rewrite Hlcn; exact VL8 | exact VL12 | exact HAWR ]. }
  assert (HROM2 : rom_view SEGS Wc (ms_mem ms2))
  by (exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO PSTR HROM)).
  assert (ERR2 : forall j, 0 <= j < 4 -> aview SEGS (w_H Wc) (ms_mem ms2) (as_errno B + j) = aview SEGS (w_H W) mem0 (as_errno B + j)).
  { intros j Hj. destruct (ERF j Hj) as (Fa & Fb & Fc).
    rewrite (K12 (as_errno B + j) ltac:(lia) Fb). exact (HERR j Hj). }
  assert (HAPK2 : apres_kept B W mem0 Wc (ms_mem ms2)).
  { intros a Hi Hno Herr Hpp.
    lazymatch goal with Hg1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)),
                        Hg2 : mem_grows (mrestrict (w_H Wc) (ms_mem ms1)) (mrestrict (w_H Wc) (ms_mem ms2)) |- _ =>
      exact (lf_apresent_grows _ _ _ a Hg2 (lf_apresent_grows _ _ _ a Hg1 (HAPK a Hi Hno Herr Hpp))) end. }
  assert (Hi1 : ((m - 1) < length (hl_recs lc))%nat) by (rewrite Hlcrecs, length_firstn; lia).
  (* the room: list_drop's free is one of the m frees left for the texts *)
  assert (HRMc : rp_RM RP Sc (1 + (m - 1 + 1 + kr))) by (apply (lf_rm_cast RP Sc _ _ HRM); clear - Hm; lia).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (lf_call_drop_xR LA lc lines (m - 1) Wc (ms_regs ms2) (ms_mem ms2) (spZ regs0)
      (blk_FP (list_blks l)) ly S Hp W mem0 md0 lyc Sc Hpc _ _ (getr (ms_regs ms2) 1) (m - 1 + 1 + kr)%nat
      HLG HZS HROM2 HLA8 ltac:(rewrite Hlcn; unfold AREC; lia) Hsp0 HJ HLc2 Hi1 HMOf HRMc HCNT).
    - rewrite Q10, E8. reflexivity.
    - rewrite Q11. rewrite denot_lit_U.
      rewrite (lf_U_decw E (SOff 10 0) (Z.of_nat m) (lf_S_atom E 10 (Z.of_nat m) E10 ltac:(lia)) ltac:(lia)).
      unfold w64. f_equal. lia.
    - unfold spZ at 1. rewrite Q2, Usp. lia.
    - rewrite Q3, E3. exact Hgp.
    - rewrite Q4, E4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1, unsigned_lit_small by lia. lia.
    - unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia.
      clear - HLA1 HLA2 C1. lia.
    - exact HFP. }
  cbv beta. intros W2 c2 Hwle2
    (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HP2 & HAL2 & HBS2 & HPK2 & HER2 & HFR2 & HML2 & HRM2 & KH2).
  rewrite Q1.
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  (* ---- the state at 0x866e0, afresh: the dropped list, one record shorter ---- *)
  set (lc' := ldrop_list lc (m - 1)) in *.
  assert (Hlc'v : hl_v lc' = hl_v l) by (subst lc'; cbn [ldrop_list hl_v]; exact Hlcv).
  assert (Hlc'cap : hl_cap lc' = hl_cap l) by (subst lc'; cbn [ldrop_list hl_cap]; exact Hlccap).
  assert (Hlc'recs : hl_recs lc' = firstn (m - 1) (hl_recs l)).
  { subst lc'. cbn [ldrop_list hl_recs]. rewrite Hlcrecs, firstn_firstn.
    replace (Nat.min (m - 1) m) with (m - 1)%nat by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). rewrite app_nil_r. reflexivity. }
  assert (Hlc'n : hl_n lc' = Z.of_nat (m - 1)) by (unfold hl_n; rewrite Hlc'recs, length_firstn; lia).
  pose proof HAL2 as (Mv2 & Mn2 & Mc2 & Hw2 & (Hn02 & Hcap2) & _).
  rewrite Hlc'n in Mn2, Hn02. rewrite Hlc'v in Mv2. rewrite Hlc'cap in Mc2, Hcap2.
  (* the blocks: the record the call freed is the last of lc *)
  assert (HPERM2 : forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) ->
    Permutation (ablocks B ly2 S2) (lf_blks l (m - 1) ++ rest)).
  { intros rest Hpp. pose proof (HPERM rest Hpp) as Hp1. destruct HBS2 as (b1 & b2 & Ea1 & Ea2).
    rewrite Ea1 in Hp1. rewrite Ea2.
    assert (Hnth : nth (m - 1) (hl_recs lc) (0, []) = nth (m - 1) (hl_recs l) (0, []))
    by (rewrite Hlcrecs; apply lf_nth_firstn; lia).
    rewrite Hnth in Hp1. unfold lf_blks in Hp1 |- *.
    assert (Hfl : firstn m (hl_recs l) = firstn (m - 1) (hl_recs l) ++ [nth (m - 1) (hl_recs l) (0, [])])
    by (replace m with (Datatypes.S (m - 1)) at 1 by lia; apply lf_firstn_last; lia).
    rewrite Hfl in Hp1.
    rewrite map_app in Hp1. cbn [map] in Hp1.
    exact (lf_perm_drop2 b1 b2 _ _ rest _ Hp1). }
  assert (HFRS2 : frames S2 = frames S) by (rewrite HFR2; exact HFRS).
  (* the live counts: the call freed one block *)
  assert (HCNT2 : cnt_ok RP (ablocks B ly2 S2)).
  { destruct HBS2 as (b1 & b2 & Ea1 & Ea2). rewrite Ea2. rewrite Ea1 in HCNT. exact (lf_cnt_del RP b1 _ b2 HCNT). }
  assert (HML2' : mo_le MT S S2 ((hl_n l - Z.of_nat (m - 1)) * mo_free MT)).
  { replace ((hl_n l - Z.of_nat (m - 1)) * mo_free MT) with ((hl_n l - Z.of_nat m) * mo_free MT + mo_free MT)
    by (replace (Z.of_nat (m - 1)) with (Z.of_nat m - 1) by lia; ring).
    exact (mle_station MT S Sc S2 _ _ MLAW HMLE HML2). }
  assert (HAPK3 : apres_kept B W mem0 W2 mem2)
  by (intros a Hi Hno Herr Hpp; exact (HPK2 a Hi Hno Herr (HAPK2 a Hi Hno Herr Hpp))).
  assert (ERR3 : forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem0 (as_errno B + j))
  by (intros j Hj; rewrite (HER2 j Hj); exact (ERR2 j Hj)).
  assert (N2 : getr regs2 2 = getr (ms_regs ms2) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (N3 : getr regs2 3 = getr (ms_regs ms2) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (N4 : getr regs2 4 = getr (ms_regs ms2) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (N8 : getr regs2 8 = getr (ms_regs ms2) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (N9 : getr regs2 9 = getr (ms_regs ms2) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (N18 : getr regs2 18 = getr (ms_regs ms2) 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (N19 : getr regs2 19 = getr (ms_regs ms2) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (N21 : getr regs2 21 = getr (ms_regs ms2) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (N22 : getr regs2 22 = getr (ms_regs ms2) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  assert (N23 : getr regs2 23 = getr (ms_regs ms2) 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (N24 : getr regs2 24 = getr (ms_regs ms2) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
  assert (N25 : getr regs2 25 = getr (ms_regs ms2) 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
  assert (N26 : getr regs2 26 = getr (ms_regs ms2) 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
  assert (N27 : getr regs2 27 = getr (ms_regs ms2) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  assert (HRL2 : lf_regsL regs2 regs0 LA).
  { unfold lf_regsL.
    split; [rewrite N2, Q2, E2; reflexivity|].
    split; [rewrite N3, Q3, E3; reflexivity|].
    split; [rewrite N4, Q4, E4; reflexivity|].
    split; [rewrite N8, Q8, E8; reflexivity|].
    split; [rewrite N9, Q9, D9; reflexivity|].
    split; [rewrite N18, Q18, E18; reflexivity|].
    split; [rewrite N19, Q19, D19; reflexivity|].
    split; [rewrite N21, Q21, E21; reflexivity|].
    split; [rewrite N22, Q22, E22; reflexivity|].
    split; [rewrite N23, Q23, E23; reflexivity|].
    split; [rewrite N24, Q24, E24; reflexivity|].
    split; [rewrite N25, Q25, E25; reflexivity|].
    split; [rewrite N26, Q26, E26; reflexivity|].
    rewrite N27, Q27, E27; reflexivity. }
  assert (Hfr2 : lf_frame W2 mem2 (spZ regs0) regs0).
  { intros i Hi. unfold arm in *. apply (val_mem_kept SEGS (w_H Wc) (w_H W2) (ms_mem ms2) mem2); [|].
    - intros j Hj. apply KH2; [unfold alloc_ceiling in *; lia | lia].
    - pose proof (Hfr i Hi) as Hslot. unfold arm in Hslot.
      apply (val_mem_kept SEGS (w_H Wc) (w_H Wc) memc (ms_mem ms2)); [|exact Hslot].
      intros j Hj. apply K12; lia. }
  destruct (lf_cut_x A_lf_ret W2 ly2 S2 Hp2 mem2 md2 regs2 regs0 LA (hl_v l) (hl_cap l) (Z.of_nat (m - 1))
    HAR2 HRL2 Hsp0 Hfr2 HLA1 HLA2 HZS Mv2 Mn2 Mc2 Hw2 ltac:(rewrite <- Hlcv; exact Hv64)
    ltac:(lia) ltac:(lia)) as [HS2 SHOK2].
  clear HS. rename HS2 into HS. rename SHOK2 into SHOK2'.
  remember (Eimg (Ereg regs2 (lf_xl (hl_v l) (hl_cap l) (Z.of_nat (m - 1)) regs0))) as Eb eqn:HEb in HS.
  rewrite <- HEb in SHOK2'.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (EEb : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Eb n = getr regs2 rr)
  by (intros n rr Hn; subst Eb; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (Eb2 : ew Eb 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEb 2%nat 2%bv eq_refl); exact (proj1 HRL2)).
  assert (Eb8 : ew Eb 8 = Z_to_bv 64 LA) by (rewrite (EEb 8%nat 8%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 HRL2))))).
  assert (Eb34 : ew Eb 34 = Z_to_bv 64 (Z.of_nat (m - 1))) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (Eb3 : ew Eb 3 = getr regs0 3) by (rewrite (EEb 3%nat 3%bv eq_refl); exact (proj1 (proj2 HRL2))).
  assert (Eb4 : ew Eb 4 = getr regs0 4) by (rewrite (EEb 4%nat 4%bv eq_refl); exact (proj1 (proj2 (proj2 HRL2)))).
  assert (Eb18 : ew Eb 18 = Z_to_bv 64 SB) by (rewrite (EEb 18%nat 18%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))).
  assert (Eb21 : ew Eb 21 = getr regs0 21) by (rewrite (EEb 21%nat 21%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))).
  assert (Eb22 : ew Eb 22 = getr regs0 22) by (rewrite (EEb 22%nat 22%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))).
  assert (Eb23 : ew Eb 23 = getr regs0 23) by (rewrite (EEb 23%nat 23%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))))).
  assert (Eb24 : ew Eb 24 = getr regs0 24) by (rewrite (EEb 24%nat 24%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))).
  assert (Eb25 : ew Eb 25 = getr regs0 25) by (rewrite (EEb 25%nat 25%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2))))))))))))).
  assert (Eb26 : ew Eb 26 = getr regs0 26) by (rewrite (EEb 26%nat 26%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))))).
  assert (Eb27 : ew Eb 27 = getr regs0 27) by (rewrite (EEb 27%nat 27%bv eq_refl); exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRL2)))))))))))))).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 (hl_v l)) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (hl_cap l)) by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs0 - 48) by (rewrite Eb2; apply unsigned_lit_small; lia).
  assert (U8b : bv_unsigned (ew Eb 8) = LA) by (rewrite Eb8; apply unsigned_lit_small; lia).
  assert (ESVb : forall i, (i < 6)%nat -> ew Eb (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
  by (intros i Hi; subst Eb; exact (lf_ew_saved regs2 regs0 _ _ _ i Hi)).
  clear HEb.
  (* 0x866e0 the shadow byte of l->n, 0x866e8 a0 = l->n, 0x866ec bnez a0 *)
  paj_run_tok_xR RUNG HS HJ2 SHOK2' lf_Bspan. { lf_awrL Uspb U8b HLG. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hf into HFr3 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hgr into HGr3 end.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) mem2 (ms_mem ms3) HFr3 a Ha).
    intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite U8b in Hr; lia]. }
  psrr_branch_tok RUNG BRG HS SHOK2' lf_Bspan.
  + (* l->n <> 0: back to the loop head *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
    rewrite trap_br_ne, (U_atom Eb 34 (Z.of_nat (m - 1)) Eb34 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Bool.negb_true_iff, Z.eqb_neq in Hbr.
    assert (Hz : (m - 1 =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hz in HK.
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2' lf_Bspan A_lf_loop.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awrL Uspb U8b HLG. }
    lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
    { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [lia | rewrite U8b in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    destruct (lf_den_regs Eb LA Eb8 Eb18 ltac:(lia)) as (D9b & D19b).
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1f. cbn [ms_mem restrict] in RL1f.
    apply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + k1)).
    * unfold lf_inv_xR.
      split; [exact HJ2|].
      split.
      { unfold lf_regsL.
        split; [rewrite F2, Eb2; reflexivity|].
        split; [rewrite F3, Eb3; reflexivity|].
        split; [rewrite F4, Eb4; reflexivity|].
        split; [rewrite F8, Eb8; reflexivity|].
        split; [rewrite F9, D9b; reflexivity|].
        split; [rewrite F18, Eb18; reflexivity|].
        split; [rewrite F19, D19b; reflexivity|].
        split; [rewrite F21, Eb21; reflexivity|].
        split; [rewrite F22, Eb22; reflexivity|].
        split; [rewrite F23, Eb23; reflexivity|].
        split; [rewrite F24, Eb24; reflexivity|].
        split; [rewrite F25, Eb25; reflexivity|].
        split; [rewrite F26, Eb26; reflexivity|].
        rewrite F27, Eb27; reflexivity. }
      split.
      { intros i Hi. unfold arm.
        pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
        eapply (slot_of_region Eb _ (spZ regs0 - 48) _ 0 48 0 0 (8 * Z.of_nat i) (SOff (35 + i) 0)).
        - exact RS0.
        - exact Uspb.
        - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
        - cbn [sv_denot]. rewrite (ESVb i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - exact Hr. }
      split.
      { exists lc'. split; [exact Hlc'v|]. split; [exact Hlc'cap|]. split; [exact Hlc'recs|].
        destruct (lf_head_of_region Eb W2 (ms_mem msf) LA (hl_v l) (Z.of_nat (m - 1)) (hl_cap l) RL1f U8b Eb32 Eb34 Eb33
          ltac:(rewrite <- Hlcv; exact Hv64) ltac:(lia) ltac:(lia)) as (FL0 & FL8 & FL12 & FAWR).
        apply (lf_alist_relocate_x ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) LA lc' lines HAR2 HAL2 HLG);
        [ intros a Hh Hno; rewrite (K4 a ltac:(unfold alloc_ceiling in *; lia) Hno);
          exact (K3 a ltac:(unfold alloc_ceiling in *; lia) Hno)
        | rewrite Hlc'v; exact FL0 | rewrite Hlc'n; exact FL8 | rewrite Hlc'cap; exact FL12 | exact FAWR ]. }
      split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
      split.
      { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
        exact (lf_apresent_grows _ _ _ a HGr3 (HAPK3 a Hi Hno Herr Hpp)). }
      split.
      { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
        rewrite (K4 (as_errno B + j) ltac:(lia) Gb). rewrite (K3 (as_errno B + j) ltac:(lia) Gb). exact (ERR3 j Hj). }
      split; [exact HRM2 | exact HCNT2].
    * intros _. rewrite F10, Eb34. reflexivity.
  + (* l->n = 0: out of the loop, to 0x86700 *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
    rewrite trap_br_ne, (U_atom Eb 34 (Z.of_nat (m - 1)) Eb34 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Bool.negb_false_iff, Z.eqb_eq in Hbr.
    assert (Hz : (m - 1 =? 0)%nat = true) by (apply Nat.eqb_eq; lia).
    rewrite Hz in HK.
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2' lf_Bspan A_lf_done.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awrL Uspb U8b HLG. }
    lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
    { intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [lia | rewrite U8b in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    destruct (lf_den_regs Eb LA Eb8 Eb18 ltac:(lia)) as (D9b & D19b).
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1f. cbn [ms_mem restrict] in RL1f.
    apply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + k1)).
    * unfold lf_inv_xR.
      split; [exact HJ2|].
      split.
      { unfold lf_regsL.
        split; [rewrite F2, Eb2; reflexivity|].
        split; [rewrite F3, Eb3; reflexivity|].
        split; [rewrite F4, Eb4; reflexivity|].
        split; [rewrite F8, Eb8; reflexivity|].
        split; [rewrite F9, D9b; reflexivity|].
        split; [rewrite F18, Eb18; reflexivity|].
        split; [rewrite F19, D19b; reflexivity|].
        split; [rewrite F21, Eb21; reflexivity|].
        split; [rewrite F22, Eb22; reflexivity|].
        split; [rewrite F23, Eb23; reflexivity|].
        split; [rewrite F24, Eb24; reflexivity|].
        split; [rewrite F25, Eb25; reflexivity|].
        split; [rewrite F26, Eb26; reflexivity|].
        rewrite F27, Eb27; reflexivity. }
      split.
      { intros i Hi. unfold arm.
        pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
        eapply (slot_of_region Eb _ (spZ regs0 - 48) _ 0 48 0 0 (8 * Z.of_nat i) (SOff (35 + i) 0)).
        - exact RS0.
        - exact Uspb.
        - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
        - cbn [sv_denot]. rewrite (ESVb i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - exact Hr. }
      split.
      { exists lc'. split; [exact Hlc'v|]. split; [exact Hlc'cap|]. split; [exact Hlc'recs|].
        destruct (lf_head_of_region Eb W2 (ms_mem msf) LA (hl_v l) (Z.of_nat (m - 1)) (hl_cap l) RL1f U8b Eb32 Eb34 Eb33
          ltac:(rewrite <- Hlcv; exact Hv64) ltac:(lia) ltac:(lia)) as (FL0 & FL8 & FL12 & FAWR).
        apply (lf_alist_relocate_x ly2 S2 Hp2 W2 mem2 md2 (ms_mem msf) LA lc' lines HAR2 HAL2 HLG);
        [ intros a Hh Hno; rewrite (K4 a ltac:(unfold alloc_ceiling in *; lia) Hno);
          exact (K3 a ltac:(unfold alloc_ceiling in *; lia) Hno)
        | rewrite Hlc'v; exact FL0 | rewrite Hlc'n; exact FL8 | rewrite Hlc'cap; exact FL12 | exact FAWR ]. }
      split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
      split.
      { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
        exact (lf_apresent_grows _ _ _ a HGr3 (HAPK3 a Hi Hno Herr Hpp)). }
      split.
      { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
        rewrite (K4 (as_errno B + j) ltac:(lia) Gb). rewrite (K3 (as_errno B + j) ltac:(lia) Gb). exact (ERR3 j Hj). }
      split; [exact HRM2 | exact HCNT2].
    * intros Hne. exfalso. apply Hne. lia.
Qed.
(* :1332 lf_exit_x *)
Lemma lf_exit_xR : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines ->
lf_inv_xR W ly S Hp regs0 mem0 md0 LA l lines 0 kr Wc lyc Sc Hpc regs memc mdc kk ->
SRrG SEGS R Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HINV.
destruct HCTX as (HPRE & HL & HLG & HZS & HLA8 & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra0 & Hra04 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & (lc & Hlcv & Hlccap & Hlcrecs & HLc) & HPERM & HFRS & HMLE & HAPK & HERR & HRM0 & HCNT).
(* the room: the vector's free is the one left *)
assert (HRM : rp_RM RP Sc (1 + kr)) by (apply (lf_rm_cast RP Sc _ _ HRM0); clear - kr; lia).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hlcn : hl_n lc = 0) by (unfold hl_n; rewrite Hlcrecs; reflexivity).
pose proof HLc as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & _).
rewrite Hlcn in Mn. rewrite Hlcv in Mv. rewrite Hlccap in Mc, Hcap.
assert (HVEC : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc)).
{ intros Hcp. destruct Hvc as [[Hc0 _] | (_ & Hin & _)]; [rewrite Hlccap in Hc0; lia|].
  rewrite Hlcv, Hlccap in Hin. exact Hin. }
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct Hvc as [[Hc0 Hv0] | (Hcp & Hin & _)]; [rewrite Hlcv in Hv0; lia|].
  destruct (lf_blk_bounds_x lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as [Hb1 Hb2].
  rewrite Hlcv in Hb1. unfold req_size, AREC in Hb2. rewrite Hlcv, Hlccap in Hb2.
  destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) ((hl_n l - Z.of_nat 0) * mo_free MT) (mo_free MT) MLAW HMO HMLE MF0).
  unfold lf_cost. cbn [Z.of_nat]. assert (Hn0l : 0 <= hl_n l) by (unfold hl_n; lia). nia. }
(* ---- the cut at 0x86700 ---- *)
destruct (lf_cut_x A_lf_done Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) 0
  HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hv64 ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) 0 regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 48)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = getr regs0 21) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = getr regs0 22) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = getr regs0 23) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs0 24) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = getr regs0 25) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (ESV : forall i, (i < 6)%nat -> ew E (35 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
clear HE.
(* 0x86700 .. the jal to free *)
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan. { lf_awrL Usp U8 HLG. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => rename Hgr into HGr1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr1 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregL lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
pose proof (RO_ARx _ _ _ _ _ _ HARm) as HROm.
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -48) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (R10s : getr (ms_regs ms) 10 = w64 (hl_v l)) by (rewrite Q10; exact E32).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, E4; exact Htp).
assert (HS0 : s0Z (ms_regs ms) = LA) by (unfold s0Z; rewrite Q8; exact U8).
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
rewrite HBfree.
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0xa0] *)
assert (HCTXX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0xa0); [exact HCTX_lf_exit|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
eapply (SRrG_bind SEGS R R_trans _ _ (fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 /\
  ajournal_xR SEGS B PST ARx R LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) /\
  aregs_preserved (ms_regs ms) regs4 /\
  (forall rest, Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest) -> Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames Sc /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 + -48 - ASTACK <= a < spZ regs0 + -48) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  mo_le MT Sc S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H Wc) (ms_mem ms) (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H W4) mem4 a))).
{ destruct (Z.eq_dec (hl_cap l) 0) as [Hc0 | Hc0].
  - assert (Hv0 : hl_v l = 0)
    by (destruct Hvc as [[_ H] | (Hcp & _)]; [rewrite Hlcv in H; exact H | rewrite Hlccap in Hcp; lia]).
    eapply (SRrG_mono SEGS R).
    { exact (AFREEN_R Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (-48) (getr (ms_regs ms) 1) [] kr HJi ltac:(rewrite R10s, Hv0; reflexivity) Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-48) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HROm HCTXX HRM HCNT HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_eq (hl_cap l) 0) Hc0) in Hpp. cbn [firstn map app] in Hpp.
      exact (Permutation_trans HPm Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | exact Hpp].
  - assert (Hcp : 0 < hl_cap l) by lia.
    pose proof (HVEC Hcp) as Hvin.
    eapply (SRrG_mono SEGS R).
    { exact (AFREE_R Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (hl_v l) (AREC * hl_cap l) (-48) (getr (ms_regs ms) 1) [] kr HJi Hvin R10s Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-48) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HROm HCTXX HRM HCNT
        ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (hl_v l) (AREC * hl_cap l) i);
              [unfold list_blks; rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) Hc0); apply in_or_app; left; left; reflexivity | exact Hi]) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. rewrite Eb2. rewrite Eb1 in Hpp. unfold lf_blks in Hpp.
      rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) Hc0) in Hpp.
      cbn [firstn map app] in Hpp. apply Permutation_sym in Hpp. apply Permutation_cons_app_inv in Hpp. exact (Permutation_sym Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | | exact Hpp].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hvin Hb Hi). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJi4 & HP4 & HPM4 & HFR4 & KS4 & KI4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
pose proof (proj1 HJi4) as HAR4.
assert (HJ4 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | apply out_none]. }
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 2 (spZ regs0 - 48)); [exact Usp | | intros a Ha; exfalso; lia].
    intros a Ha. apply KS4; [lia | lia].
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 8 LA); [exact U8 | |].
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He). exact (KI4 a Hi Ho He).
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He).
      apply (lf_writable_img Wc W4 (ms_mem ms) mem4 a Hi). exact (HPR4 a Hi Ho He). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 48)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHL Ea (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, lf_SHL. constructor; [|constructor].
  apply (lf_shent8_x Ea ly4 S4 Hp4 W4 mem4 md4 LA HAR4 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 48) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* 0x86718 .. the ret: l->v = 0, l->cap = 0, the epilogue *)
paj_run_tok_xR RUNG HS HJ4 SHOK2 lf_Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons_awr0; [awr_any; try exact Uspa|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregL lf_lreg base_val]. rewrite U8a.
  intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hf into HFrf end.
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W4) mem4 (ms_mem msf) HFrf a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22.
prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (HPF : aregs_preserved regs0 (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspa. replace (spZ regs0 - 48 + 48) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDa by lia. exact E3.
  - rewrite F4, OLDa by lia. exact E4.
  - rewrite F8, OLDa by lia. exact (ESV 4%nat ltac:(lia)).
  - rewrite F9, OLDa by lia. exact (ESV 3%nat ltac:(lia)).
  - rewrite F18, OLDa by lia. exact (ESV 2%nat ltac:(lia)).
  - rewrite F19, OLDa by lia. exact (ESV 1%nat ltac:(lia)).
  - rewrite F20, OLDa by lia. exact (ESV 0%nat ltac:(lia)).
  - rewrite F21, OLDa by lia. exact E21.
  - rewrite F22, OLDa by lia. exact E22.
  - rewrite F23, OLDa by lia. exact E23.
  - rewrite F24, OLDa by lia. exact E24.
  - rewrite F25, OLDa by lia. exact E25.
  - rewrite F26, OLDa by lia. exact E26.
  - rewrite F27, OLDa by lia. exact E27. }
assert (ER1 : ew E 40 = getr regs0 1) by exact (ESV 5%nat ltac:(lia)).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall n, (n < 512)%nat -> ew Ef n = ew Ea n) by (intros n Hn; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U8f : bv_unsigned (ew Ef 8) = LA) by (rewrite UF by lia; exact U8a).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
assert (VL0 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 0) (N.to_nat 8) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 8) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDa by lia. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 12) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W4 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL1 as (_ & _ & RLw & _).
  cbn [lf_lregL lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U8f in RLw. exact (RLw i Hi). }
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lf_post_xR.
exists ly4, S4, Hp4, (ms_regs msf), (ms_mem msf). eexists. exists (kk + 1).
split; [rewrite F1, OLDa by lia; rewrite ER1, Hra0; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [exact HPF|].
split.
{ unfold alist_at, empty_list, hl_n. cbn [hl_v hl_cap hl_recs hl_junk length Z.of_nat].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|]. split; [left; split; reflexivity|]. split; [constructor|]. split; [intros []|]. constructor. }
split; [intros rest Hpp; exact (HPM4 rest (HPERM rest Hpp))|].
split.
{ intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). apply (HPR4 a Hi Hno Herr).
  apply (lf_apresent_grows _ _ _ a HGr1). exact (HAPK a Hi Hno Herr Hpp). }
split.
{ intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
  rewrite (Kf (as_errno B + j) ltac:(lia) Gb). rewrite (HER4 j Hj).
  rewrite (K1 (as_errno B + j) ltac:(lia) Gb). exact (HERR j Hj). }
split; [rewrite HFR4; exact HFRS|].
split; [|exact HRM4].
replace (lf_cost MT l) with (hl_n l * mo_free MT + mo_free MT) by (unfold lf_cost; ring).
replace (hl_n l * mo_free MT) with ((hl_n l - Z.of_nat 0) * mo_free MT) by (cbn [Z.of_nat]; ring).
exact (mle_station MT S Sc S4 _ _ MLAW HMLE HML4).
Qed.
(* :1592 pb_list_free_x *)
Theorem pb_list_free_xR : lf_spec_xR B PST ARx R MT RP G A_list_freeP.
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HLA8 HL HLG HZS HROM HMO kr HRM0 HCNT0.
assert (HCTX : lf_ctx_x W ly S Hp regs mem md ch LA l lines)
by (unfold lf_ctx_x; split; [exact HPRE|]; split; [exact HL|]; split; [exact HLG|]; split; [exact HZS|];
    split; [exact HLA8|]; split; [exact HROM | exact HMO]).
(* the loop, by induction on the texts left *)
assert (IND : forall m Wc lyc Sc Hpc regsc memc mdc kc, (m <= length (hl_recs l))%nat ->
  lf_inv_xR W ly S Hp regs mem md LA l lines m kr Wc lyc Sc Hpc regsc memc mdc kc ->
  (m <> 0%nat -> getr regsc 10 = w64 (Z.of_nat m)) ->
  SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + if (m =? 0)%nat then A_lf_done else A_lf_loop)) memc (seg_rom SEGS)) mdc)
    (lf_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines kr)).
{ induction m as [|m IH]; intros Wc lyc Sc Hpc regsc memc mdc kc Hml HI H10c; cbn [Nat.eqb].
  - exact (lf_exit_xR W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX HI).
  - apply (lf_iter_xR (Datatypes.S m) W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX ltac:(lia) HI
      (H10c ltac:(lia))).
    intros Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' HI' H10'.
    replace (Datatypes.S m - 1)%nat with m in * by lia.
    exact (IH Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ltac:(lia) HI' H10'). }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lf_entry_x W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (mo_free_nonneg MT MLAW) as MF0.
assert (WS : LF_STK = 16496) by reflexivity.
pose proof (lf_errno_facts (spZ regs) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LF_STK (blk_FP (list_blks l)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (lf_extra l))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (EEo 3%nat 3%bv eq_refl); reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (EEo 4%nat 4%bv eq_refl); reflexivity).
assert (E21 : ew E 21 = getr regs 21) by (rewrite (EEo 21%nat 21%bv eq_refl); reflexivity).
assert (E22 : ew E 22 = getr regs 22) by (rewrite (EEo 22%nat 22%bv eq_refl); reflexivity).
assert (E23 : ew E 23 = getr regs 23) by (rewrite (EEo 23%nat 23%bv eq_refl); reflexivity).
assert (E24 : ew E 24 = getr regs 24) by (rewrite (EEo 24%nat 24%bv eq_refl); reflexivity).
assert (E25 : ew E 25 = getr regs 25) by (rewrite (EEo 25%nat 25%bv eq_refl); reflexivity).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (EEo 26%nat 26%bv eq_refl); reflexivity).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EEo 27%nat 27%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ERS : forall i, (i < 6)%nat -> ew E (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_regs regs _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = LA) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (lf_blk_bounds_x ly S Hp W mem md _ _ HAR Hin) as [Hb1 Hb2].
  unfold req_size, AREC in Hb2. destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
destruct (lf_den_regs E LA E10 E35 ltac:(lia)) as (D9 & D19).
clear HE.
unfold cfg_at. change (w64 A_list_freeP) with (Z_to_bv 64 A_list_freeP).
unfold A_list_freeP, A_list_free.
(* the prologue, to the ALIGN8 trap branch *)
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan. { lf_awr0 Usp U10 HLG. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms0 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hf into HFr0 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hgr into HGr0 end.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms0) HFr0 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lf0 lf_regions0 In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [stack_region got_regionP bcell_regionP lf_lreg LF_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
(* 0x8669c bnez: the UBSan ALIGN8 trap on LA, never taken *)
psrr_branch_tok RUNG BRG HS SHOK lf_Bspan.
- exfalso. rewrite (trap_align8 E (SOff 10 0) LA (U_atom E 10 LA E10 ltac:(lia)) HLA8) in Hc. discriminate.
- paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan. { lf_awr0 Usp U10 HLG. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ => rename Hf into HFr1 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ => rename Hgr into HGr1 end.
  lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr1 end.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  (* 0x866c4 beqz a0: is the list empty? *)
  psrr_branch_tok RUNG BRG HS SHOK lf_Bspan.
  + (* n = 0: straight to 0x86700 *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
    rewrite trap_br_eq, (U_atom E 33 (hl_n l) E33 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Z.eqb_eq in Hbr.
    assert (Hrn : hl_recs l = []) by (unfold hl_n in Hbr; destruct (hl_recs l); [reflexivity | cbn [length] in Hbr; lia]).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK lf_Bspan A_lf_done.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awr0 Usp U10 HLG. }
    lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
      aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms1) a).
    { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms1) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22.
    prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
    prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3. cbn [ms_mem restrict] in RL3.
    apply (IND 0%nat W ly S Hp (ms_regs msf) (ms_mem msf) _ 0 ltac:(lia)); [|intros Hne; exfalso; apply Hne; reflexivity].
    unfold lf_inv_xR.
    split; [exact HJ|].
    split.
    { unfold lf_regsL.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|]. split; [rewrite F9, D9; reflexivity|].
      split; [rewrite F18, E35; reflexivity|]. split; [rewrite F19, D19; reflexivity|].
      split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|].
      split; [rewrite F23, E23; reflexivity|]. split; [rewrite F24, E24; reflexivity|].
      split; [rewrite F25, E25; reflexivity|]. split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split.
    { intros i Hi. unfold arm.
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      replace (spZ regs - 48 + 8 * Z.of_nat i) with (spZ regs + (-48 + 8 * Z.of_nat i)) by ring.
      eapply (slot_of_region E _ (spZ regs) _ (-48) 0 (-48) 0 (-48 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
      - exact RS0.
      - exact Usp.
      - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
      - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - exact Hr. }
    split.
    { exists l. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrn; reflexivity|].
      assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      rewrite Z.add_0_r in VL0.
      assert (HAWR : awr W (ms_mem msf) LA 16).
      { intros i Hi. destruct RL3 as (_ & _ & RLw & _).
        cbn [lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U10 in RLw. exact (RLw i Hi). }
      apply (lf_alist_relocate_x ly S Hp W mem md (ms_mem msf) LA l lines HAR HL HLG);
      [ intros a Hh Hno; rewrite (K2 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        rewrite (K1 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        exact (K0 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno)
      | exact VL0 | exact VL8 | exact VL12 | exact HAWR ]. }
    split; [intros rest Hpp; unfold lf_blks; rewrite Hrn; cbn [firstn map app]; rewrite app_nil_r;
            unfold list_blks in Hpp; rewrite Hrn in Hpp; cbn [map app] in Hpp; rewrite app_nil_r in Hpp; exact Hpp|].
    split; [reflexivity|].
    split; [cbn [Z.of_nat]; unfold hl_n; rewrite Hrn; cbn [length Z.of_nat];
            replace (0 - 0) with 0 by lia; rewrite Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split.
    { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
      apply (lf_apresent_grows _ _ _ a HGr1). exact (lf_apresent_grows _ _ _ a HGr0 Hpp). }
    split.
    { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
      rewrite (K2 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      rewrite (K1 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      exact (K0 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb). }
    (* the room: no text, so only the vector's free (lf_cost MT_rk l = n + 1, n = 0) *)
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk, Hrn. reflexivity.
  + (* n <> 0: into the loop at 0x866d0 *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
    rewrite trap_br_eq, (U_atom E 33 (hl_n l) E33 ltac:(lia)), U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
    apply Z.eqb_neq in Hbr.
    assert (Hlen0 : (length (hl_recs l) =? 0)%nat = false) by (apply Nat.eqb_neq; unfold hl_n in Hbr; lia).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK lf_Bspan A_lf_loop.
    { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
      lf_awr0 Usp U10 HLG. }
    lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
    lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
    lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
      aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms1) a).
    { intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W) (ms_mem ms1) (ms_mem msf) HFrf a Ha).
      intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite Usp in Hr; try unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
    prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    prreg_raw HS (9%bv : bv 5) F9. prreg_raw HS (19%bv : bv 5) F19.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0. cbn [ms_mem restrict] in RS0.
    pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3. cbn [ms_mem restrict] in RL3.
    pose proof (IND (length (hl_recs l)) W ly S Hp (ms_regs msf) (ms_mem msf)) as HH.
    rewrite Hlen0 in HH. apply (HH _ 0 (le_n _)); [|intros _; rewrite F10, E33; unfold hl_n; reflexivity].
    unfold lf_inv_xR.
    split; [exact HJ|].
    split.
    { unfold lf_regsL.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|]. split; [rewrite F9, D9; reflexivity|].
      split; [rewrite F18, E35; reflexivity|]. split; [rewrite F19, D19; reflexivity|].
      split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|].
      split; [rewrite F23, E23; reflexivity|]. split; [rewrite F24, E24; reflexivity|].
      split; [rewrite F25, E25; reflexivity|]. split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split.
    { intros i Hi. unfold arm.
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      replace (spZ regs - 48 + 8 * Z.of_nat i) with (spZ regs + (-48 + 8 * Z.of_nat i)) by ring.
      eapply (slot_of_region E _ (spZ regs) _ (-48) 0 (-48) 0 (-48 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
      - exact RS0.
      - exact Usp.
      - clear - Hi. do 6 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
      - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - exact Hr. }
    split.
    { exists l. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite firstn_all; reflexivity|].
      assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
      { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
        cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      rewrite Z.add_0_r in VL0.
      assert (HAWR : awr W (ms_mem msf) LA 16).
      { intros i Hi. destruct RL3 as (_ & _ & RLw & _).
        cbn [lf_lreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw. rewrite U10 in RLw. exact (RLw i Hi). }
      apply (lf_alist_relocate_x ly S Hp W mem md (ms_mem msf) LA l lines HAR HL HLG);
      [ intros a Hh Hno; rewrite (K2 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        rewrite (K1 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno);
        exact (K0 a ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Hno)
      | exact VL0 | exact VL8 | exact VL12 | exact HAWR ]. }
    split; [intros rest Hpp; unfold lf_blks; rewrite firstn_all; exact Hpp|].
    split; [reflexivity|].
    split; [unfold hl_n; rewrite Z.sub_diag, Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split.
    { intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf).
      apply (lf_apresent_grows _ _ _ a HGr1). exact (lf_apresent_grows _ _ _ a HGr0 Hpp). }
    split.
    { intros j Hj. destruct (ERF j Hj) as (Ga & Gb & Gc).
      rewrite (K2 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      rewrite (K1 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb).
      exact (K0 (as_errno B + j) ltac:(lia) ltac:(unfold LF_STK, ASTACK in *; lia) Gb). }
    (* the room: one free per text and one for the vector (lf_cost MT_rk l = n + 1) *)
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk. lia.
Qed.
End wR.
(* the strict loop state is the R section's at R := wle *)
Lemma lf_inv_x_wle : lf_inv_x = lf_inv_xR (@wle SEGS).
Proof. reflexivity. Qed.
End c.

(* list_free's G-generic form over ARx (W_contract_x.v lf_spec_g_x): gx_ok, gx_rt, rom_out and the three readability /
   writability / shadow clauses of gx_prog_x are its premise; the laws, HP0, PSTR, the allocator rules with their
   caller-context facts and the memmove contract stay hypotheses (all G-free). *)
Section g.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis MLAW : ameter_laws MT.
Hypothesis TL : PALib B.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* fuzz_reply.asan-ubsan objdump: 0x86714 jal __interceptor_trampoline_free; returns to 0x86718 = list_free 0x86678 + 0xa0 *)
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xa0] CTX.
(* fuzz_reply.asan-ubsan objdump: 0x85be8 jal __interceptor_trampoline_free; returns to 0x85bec = list_drop 0x85b50 + 0x9c *)
Hypothesis HCTX_ld_free : In [BASE + AF_fr_list_drop + 0x9c] CTX.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Theorem pb_list_free_g_x : lf_spec_g_x B PST ARx MT RP (BASE + AF_fr_list_free).
Proof.
intros G (HG & HGR & HRO & GX_ROM & GX_W & GSHV).
change (BASE + AF_fr_list_free) with A_list_freeP.
eapply pb_list_free_x with (CTX := CTX); eassumption.
Qed.
(* ---- route R: the G-generic form at R (W_contract_srlf_xR.v lf_spec_g_xR), from pb_list_free_xR as pb_list_free_g_x is
   from pb_list_free_x, under Section c's route-R hypotheses (list_drop at R the premise LD_R). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis LD_R : forall G', gx_ok SEGS B G' -> gx_rt B G' -> rom_out SEGS B G' -> ldrop_spec_xR B PST ARx R MT RP G' A_list_dropP.
(* :3030 pb_list_free_g_x *)
Theorem pb_list_free_g_xR : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Proof.
intros G (HG & HGR & HRO & GX_ROM & GX_W & GSHV).
change (BASE + AF_fr_list_free) with A_list_freeP.
eapply pb_list_free_xR with (CTX := CTX) (RO := RO); eassumption.
Qed.
End wR.
(* ---- the same with LD_R discharged: list_drop at R from the strict list_drop walk (W_list_drop.v pb_list_drop_ro_x,
   which takes this Section's AFREE, HCTX_ld_free and AMOVE) by the bridge W_contract_xR_g3.v ldrop_spec_xR_of_x
   (WLE_R).  The route-R hypotheses are pb_list_free_g_xR's but LD_R. ---- *)
Section wRs.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Theorem pb_list_free_g_xR_sld : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Proof.
eapply pb_list_free_g_xR with (R := R) (RO := RO);
first [ eassumption
      | intros G' HG' HGR' HRO'; eapply ldrop_spec_xR_of_x;
        first [ exact WLE_R | eapply pb_list_drop_ro_x with (CTX := CTX); eassumption ] ].
Qed.
End wRs.
End g.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3): pb_list_free's and pb_list_free_g's statements are the AR
   walk's, byte-identical, now corollaries of pb_list_free_x / pb_list_free_g_x at ARx := ARi0 (cgif's AR with the
   head set empty), PST := [].  Their Sections are the AR walk's, unchanged (a Theorem Labs lane's ruling 03:30Z: the plain names
   keep their B-old statements); each proof derives LX0 (the laws at ARi0) from LAWS by lib/B/YLX0.v
   lx_AR_laws_x_ARi0_of (a Theorem Labs lane's; W_journal_x.AR_laws_x_ARi0 of YCbqG.AR_laws_x_of_AR ..).  The allocator rules stay in
   their AR form: W_journal.v <rule>_c_weak gives the caller-context ones at the two-entry table lf_ctx0, and
   W_journal_x's <rule>_c_x_of_AR0 the generic ones at ARi0; HP0 at ARi0 is ARi0_hp0; PSTR holds at PST = []; the
   memmove contract's twin is W_sites_x.amemmove_realizes_x_of_AR0; the bridges are W_contract_x lf_spec_x_AR0 /
   lf_spec_g_x_AR0. ---- *)
Definition lf_ctx0 : list (list Z) := [[BASE + AF_fr_list_free + 0xa0]; [BASE + AF_fr_list_drop + 0x9c]].
(* the generic Sections' hypotheses at ARx := ARi0, PST := [], CTX := lf_ctx0, from the AR Section's *)
Local Ltac lf_ari0 B MT AFREE AFREEN AMOVE :=
  assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0;
  assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
    by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin));
  assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H);
  assert (AFREEc : afree_cf_rule_c SEGS B MT lf_ctx0) by (apply afree_cf_rule_c_weak; exact AFREE);
  assert (AFREENc : afree_null_cf_rule_c SEGS B MT lf_ctx0) by (apply afree_null_cf_rule_c_weak; exact AFREEN);
  pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT lf_ctx0 AFREEc) as AFREEx;
  pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT lf_ctx0 AFREENc) as AFREENx;
  pose proof (amemmove_realizes_x_of_AR0 B _ AMOVE) as AMOVEx;
  assert (HCTX_lf_exit0 : In [BASE + AF_fr_list_free + 0xa0] lf_ctx0) by (left; reflexivity);
  assert (HCTX_ld_free0 : In [BASE + AF_fr_list_drop + 0x9c] lf_ctx0) by (right; left; reflexivity).
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis HRO : rom_out SEGS B G.
Hypothesis GX_ROM : forall a, inG G a -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Hypothesis GX_W : forall a, inG G a -> forall m, writable_at SEGS m a.
Hypothesis GSHV : forall ly S W mem md a n, AR SEGS B ly S W mem md -> 0 < n ->
(forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AFREEN : afree_null_cf_rule SEGS B MT.
(* the __asan_memmove intrinsic's contract (W_sites.v), which list_drop's theorem takes *)
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Theorem pb_list_free : lf_spec B MT G A_list_freeP.
Proof.
apply lf_spec_x_AR0. pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0. lf_ari0 B MT AFREE AFREEN AMOVE.
assert (GSHVx : forall ly S Hp W mem md a n, ARi0 SEGS B ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n)
  by (intros ly S Hp W mem md a n H; exact (GSHV ly S W mem md a n (proj1 H))).
eapply pb_list_free_x with (CTX := lf_ctx0); eassumption.
Qed.
End cAR.
Section gAR.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AFREEN : afree_null_cf_rule SEGS B MT.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Theorem pb_list_free_g : lf_spec_g B MT (BASE + AF_fr_list_free).
Proof.
apply lf_spec_g_x_AR0. pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0. lf_ari0 B MT AFREE AFREEN AMOVE.
eapply pb_list_free_g_x with (CTX := lf_ctx0); eassumption.
Qed.
End gAR.
End b.
End a.
