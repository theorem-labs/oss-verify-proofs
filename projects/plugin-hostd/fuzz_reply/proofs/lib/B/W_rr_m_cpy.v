(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: hop CPY of the MATCH segment of the IMAGE-B walk of fuzz_reply's relay_remove
   (lib/B/W_rr_match_cx.v hop_cpy_stmt, fuzz_reply.asan-ubsan): RRC i 0x84360 -> RRU (Some i) 0x843c0.
     0x84360  ld a2,-1288(s4)          a2 = g_src = G0
     0x84364  add a0,a2,s3             a0 = &g_src[i] = G0 + 56 i              (the memcpy's destination)
     0x84368  bltu a0,a2,unimp         TRAP pointer overflow: not taken
     0x8436c  snez / seqz / xor / beqz TRAP null consistency (0x84378): the runner decides it
     0x8437c  lw a1,-1304(s1)          a1 = g_nsrc = N
     0x84380  addiw a4,a1,-1; bge      TRAP int32 decrement (0x84384): the runner decides it
     0x84388  a1 = 56 (N - 1) + G0     &g_src[N - 1]                          (the memcpy's source)
     0x8439c  sw a4,-1304(s1)          g_nsrc = N - 1
     0x843a0  beq a3,a5,unimp          TRAP null consistency: the runner decides it
     0x843a4  sltu / slti / xor / xori / beqz   TRAP signed index (0x843b4): not taken
     0x843bc  li a2,56; jal __asan_memcpy        AMEMCPY (i < N - 1) or AMEMCPYS (i = N - 1), ra 0x843c0

   Proves no function (kind: segment lemma of the B walk).  The image-A twin is lib/A/W_rr_m_cpy.v
   (a working branch): its table lemmas (rmc_firstn_app .. rmc_in_remove), its keeping lemmas (rck / rcz /
   rcz_alist / rcz_asrc / rcz_aentry / rcz_aout, rmc_cell_img, rmc_cell_nnsrc, rmc_kept_trans, rmc_garr8_moved /
   _skipn / _firstn) and the
   memcpy call are image-independent and are copied here (lib.A -> lib.B; its W_rr_scan.rrs_* / ablocks_nodup /
   aout_fp_cases are W_rr_m_kit.v's rm_eb_len / rm_concat_len / rm_ablocks_nodup / rm_aout_fp_cases).  rmc_post builds
   RDONE over image B's RLIVE (no fake frame: the saved registers in their slots instead of the frame clause).

   New for image B:
   - THE SEAT at 0x84360.  B reloads g_src with `ld a2,-1288(s4)` and g_nsrc with `lw a1,-1304(s1)`, plain listing
     words (not PLdHi), and stores g_nsrc with a plain `sw a4,-1304(s1)` (no W_rebase).  The run's memory is seated on
     the two registers' own atoms: region 0 is based on atom 20 (s4 = rg_src + 1288, rregs_held) at offsets -1288 ..
     -1280, read-only, holding g_src's 8 bytes as atom 32 (= G0); region 1 is based on atom 9 (s1 = rg_nsrc + 1304) at
     offsets -1304 .. -1300, writable (g_nsrc is a cell of G_RR), holding g_nsrc's 4 bytes as atom 33 (= N, range
     1 .. 16: recipe R4, so `lw` is not sign-extended, addiw is the 64-bit add and the decrement's trap is decided).
     Atom 34 = G0 + 56 i aliases both sums of atoms 32 and 19 (s3 = 56 i); atom 35 = G0 + 56 (N - 1) aliases the
     linear form the engine builds from the two shifts and the sub (YP0e.v alias_lin_lookup).  Every pointer atom has
     `mkAF 4096 140737479966720 _` (W_traps.v recipe R1 / R2).
   - The trap edges: 0x84368 by W_traps.v trap_ptr_wrap_atom (G0 + 56 i does not wrap: G0 + 896 <= alloc_ceiling);
     0x843b4 by trap_ptr_sovf, the compares' values 0 by trap_U_sltu_ge (G0 <= G0 + 56 (N - 1)) and the runner's
     slti = 0; the runner decides 0x84378, 0x84384 and 0x843a0 from the atoms' ranges. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (lane Rrm, the image-A twin a Theorem Labs lane
   f4cd818e98d lib/A/W_rr_m_cpy.v): hop CPY over ANY allocator relation ARx, in place (Section c is
   W_relay_remove_cx.v's generic block, as in W_rr_m_kit.v): laws al_X -> alx_X (BLKN for a live block's 0 <= n,
   rm_ablocks_nodup over ARx), the journal, frame and block lemmas their _x twins (the heap-block shadow facts under
   HP0), RUN = paj_run_x_x with paj_run_tok_x, the call by aj_gx_entry_at_x with AMEMCPY / AMEMCPYS in their _x forms
   (the site keeps ly S Hp).  The room round: the hop allocates nothing, so RRC's rp_RM RP S1 kr is RDONE's last
   conjunct at the same state (rmc_post's new premise).  Image B against the A twin: the journal is at RR_STK_x
   (W_contract_x.v: 128 bytes above RR_STK; A: RR_STK), RLIVE owns no frame (own = [], no fpos / F / FL), and the
   trap edges stay psrr_branch_tok over the same RUN (A's hop has none). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
(* route R (the Section wR below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx W_rr_match_cx W_rr_m_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the table after the copy (the A twin's) *)
Lemma rmc_firstn_app : forall {X : Type} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros X l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma rmc_skipn_app_exact : forall {X : Type} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros X l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma rmc_skipn_app_S : forall {X : Type} (l1 l2 : list X) (x : X), skipn (S (length l1)) (l1 ++ x :: l2) = l2.
Proof. intros X l1 l2 x. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma rmc_remove_at_last : forall {X : Type} (l : list X) (x : X),
  relay_remove_b_c.remove_at (length l) (l ++ [x]) = l.
Proof.
  intros X l x. unfold relay_remove_b_c.remove_at. rewrite rev_unit. cbv beta iota zeta.
  rewrite rev_involutive, Nat.eqb_refl. reflexivity.
Qed.
Lemma rmc_remove_at_mid : forall {X : Type} (l1 l2 : list X) (x z : X),
  relay_remove_b_c.remove_at (length l1) (l1 ++ x :: l2 ++ [z]) = l1 ++ z :: l2.
Proof.
  intros X l1 l2 x z. unfold relay_remove_b_c.remove_at.
  replace (l1 ++ x :: l2 ++ [z]) with ((l1 ++ x :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  rewrite rev_unit. cbv beta iota zeta. rewrite rev_involutive.
  replace (Nat.eqb (length l1) (length (l1 ++ x :: l2))) with false
    by (symmetry; apply Nat.eqb_neq; rewrite length_app; cbn [length]; lia).
  rewrite rmc_firstn_app, rmc_skipn_app_S. reflexivity.
Qed.
Lemma rmc_split_nth : forall {X : Type} (l : list X) (d : X) (i : nat), (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros X l d. induction l as [|a l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Definition rmc_upd (i : nat) (e : rentry) (es : list rentry) : list rentry := firstn i es ++ e :: skipn (S i) es.
Lemma rmc_nth_last : forall (l : list rentry) d, (0 < length l)%nat -> nth (length l - 1) l d = last l d.
Proof.
  intros l d Hl.
  destruct (exists_last (l := l) ltac:(destruct l; [cbn in Hl; lia | discriminate])) as (l' & a & ->).
  rewrite length_app. cbn [length]. rewrite Nat.add_sub.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite last_last. reflexivity.
Qed.
Lemma rmc_cmap_app : forall (f : rentry -> list byte) a b,
  concat (map f (a ++ b)) = concat (map f a) ++ concat (map f b).
Proof. intros f a b. rewrite map_app, concat_app. reflexivity. Qed.
Lemma rmc_cmap_cons : forall (f : rentry -> list byte) a l, concat (map f (a :: l)) = f a ++ concat (map f l).
Proof. intros. reflexivity. Qed.
Lemma rmc_cmap_single : forall (f : rentry -> list byte) a, concat (map f [a]) = f a.
Proof. intros f a. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma rmc_concat_cpy : forall i (es2 : list rentry), (i < length es2)%nat ->
  concat (map entry_bytes (rmc_upd i (last es2 relay_remove_b_c.no_entry) es2))
    = concat (map entry_bytes (relay_remove_b_c.remove_at i es2)) ++ entry_bytes (last es2 relay_remove_b_c.no_entry).
Proof.
  intros i es2 Hi.
  pose proof (rmc_split_nth es2 relay_remove_b_c.no_entry i Hi) as Ees.
  assert (Hlpre : length (firstn i es2) = i) by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
  remember (firstn i es2) as pre eqn:Hpre.
  remember (skipn (S i) es2) as suf eqn:Hsuf.
  remember (nth i es2 relay_remove_b_c.no_entry) as x eqn:Hx.
  assert (Hru : rmc_upd i (last es2 relay_remove_b_c.no_entry) es2 = pre ++ last es2 relay_remove_b_c.no_entry :: suf)
    by (unfold rmc_upd; rewrite <- Hpre, <- Hsuf; reflexivity).
  rewrite Hru.
  destruct suf as [|y suf'] eqn:Esuf.
  - assert (Hlast : last es2 relay_remove_b_c.no_entry = x) by (rewrite Ees; cbn [app]; rewrite last_last; reflexivity).
    assert (Hrem : relay_remove_b_c.remove_at i es2 = pre)
      by (rewrite Ees, <- Hlpre; cbn [app]; apply rmc_remove_at_last).
    rewrite Hlast, Hrem.
    repeat (rewrite rmc_cmap_app || rewrite rmc_cmap_single || rewrite rmc_cmap_cons). reflexivity.
  - destruct (exists_last (l := y :: suf') ltac:(discriminate)) as (mid & zl & Hmz).
    assert (Hlast : last es2 relay_remove_b_c.no_entry = zl)
      by (rewrite Ees, Hmz, app_comm_cons, app_assoc, last_last; reflexivity).
    assert (Hrem : relay_remove_b_c.remove_at i es2 = pre ++ zl :: mid).
    { rewrite Ees, Hmz, <- Hlpre. rewrite rmc_remove_at_mid. reflexivity. }
    rewrite Hlast, Hrem, Hmz.
    repeat (rewrite rmc_cmap_app || rewrite rmc_cmap_single || rewrite rmc_cmap_cons).
    rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma rmc_concat_len : forall (l : list rentry),
  Forall (fun e => length (entry_bytes e) = 56%nat) l -> length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
  induction l as [|e l IH]; intros HF; [reflexivity|].
  cbn [map concat length]. inversion HF as [|a b He HF' Hab]; subst.
  rewrite length_app, He, (IH HF'). lia.
Qed.
Lemma rmc_entry_len56 : forall (es : list rentry),
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => length (entry_bytes e) = 56%nat) es.
Proof. intros es HF. eapply Forall_impl; [|exact HF]. intros e [P1 P2]. exact (rm_eb_len e P1 P2). Qed.
Lemma rmc_forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l HF. rewrite Forall_forall in *. intros x Hx. apply HF.
  rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hx.
Qed.
Lemma rmc_forall_skipn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l HF. rewrite Forall_forall in *. intros x Hx. apply HF.
  rewrite <- (firstn_skipn n l). apply in_or_app. right. exact Hx.
Qed.
Lemma rmc_nth_skipn : forall {A} (l : list A) m k d, nth k (skipn m l) d = nth (m + k) l d.
Proof.
  intros A l m. revert l. induction m as [|m IH]; intros l k d; [reflexivity|].
  destruct l as [|a l]; cbn [skipn nth]; [destruct k; reflexivity|]. apply IH.
Qed.
Lemma rmc_slot_k : forall (l : list rentry) (tl : list byte) k d, (k < length l)%nat ->
  Forall (fun e => length (entry_bytes e) = 56%nat) l ->
  firstn 56 (skipn (56 * k) (concat (map entry_bytes l) ++ tl)) = entry_bytes (nth k l d).
Proof.
  induction l as [|e l IH]; intros tl k d Hk HF; cbn [length] in Hk; [lia|].
  inversion HF as [|a b He HF' Hab]; subst. cbn [map concat].
  rewrite <- app_assoc.
  destruct k as [|k].
  - cbn [nth]. rewrite Nat.mul_0_r, skipn_O, <- He. apply rmc_firstn_app.
  - cbn [nth]. replace (56 * S k)%nat with (56 + 56 * k)%nat by lia.
    rewrite skipn_app, He. rewrite skipn_all2 by (rewrite He; lia).
    replace (56 + 56 * k - 56)%nat with (56 * k)%nat by lia. cbn [app].
    apply IH; [lia | exact HF'].
Qed.
Definition rmc_Tpre (es : list rentry) (i : nat) : list byte := concat (map entry_bytes (firstn i es)).
Definition rmc_Tpost (es : list rentry) (i : nat) (tail : list byte) : list byte :=
  concat (map entry_bytes (skipn (S i) es)) ++ tail.
(* the 896 bytes after slot N - 1 is copied over slot i: the removal's entries, then the copied slot and the old tail *)
Lemma rmc_block_cpy : forall (es : list rentry) (tail X src Bl : list byte) (i : nat),
  (i < length es)%nat -> length X = 56%nat ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Bl = rmc_Tpre es i ++ X ++ rmc_Tpost es i tail ->
  src = firstn 56 (skipn (56 * (length es - 1)) Bl) ->
  firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl
    = concat (map entry_bytes (relay_remove_b_c.remove_at i es)) ++ src ++ tail.
Proof.
  intros es tail X src Bl i Hi HX HF HB Hsrc.
  pose proof (rmc_entry_len56 es HF) as HE56.
  assert (HLpre : length (rmc_Tpre es i) = (56 * i)%nat).
  { unfold rmc_Tpre. rewrite rmc_concat_len by (apply rmc_forall_firstn; exact HE56).
    rewrite length_firstn, Nat.min_l by lia. reflexivity. }
  assert (Hf1 : firstn (56 * i) Bl = rmc_Tpre es i)
    by (rewrite HB, <- HLpre; apply rmc_firstn_app).
  assert (Hf3 : skipn (56 * i + 56) Bl = rmc_Tpost es i tail).
  { rewrite HB. rewrite (app_assoc (rmc_Tpre es i) X). rewrite <- HLpre.
    replace (length (rmc_Tpre es i) + 56)%nat with (length (rmc_Tpre es i ++ X))
      by (rewrite length_app, HX; reflexivity).
    apply rmc_skipn_app_exact. }
  rewrite Hf1, Hf3. unfold rmc_Tpost.
  rewrite (app_assoc src), (app_assoc (rmc_Tpre es i)).
  rewrite (app_assoc (concat (map entry_bytes (relay_remove_b_c.remove_at i es)))).
  f_equal.
  destruct (Nat.eq_dec i (length es - 1)) as [Hlast | Hne].
  - (* i = N - 1: src = X, remove_at i es = firstn i es, no entry after slot i *)
    assert (Hsk : skipn (S i) es = []) by (apply skipn_all2; lia).
    assert (HsrcX : src = X).
    { rewrite Hsrc, HB, <- Hlast, <- HLpre, rmc_skipn_app_exact, <- HX. apply rmc_firstn_app. }
    assert (Hrem : relay_remove_b_c.remove_at i es = firstn i es).
    { pose proof (rmc_split_nth es relay_remove_b_c.no_entry i Hi) as E.
      rewrite Hsk in E. rewrite E at 1.
      assert (Hl : length (firstn i es) = i) by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
      rewrite <- Hl at 1. apply rmc_remove_at_last. }
    replace (concat (map entry_bytes (skipn (S i) es))) with (@nil byte) by (rewrite Hsk; reflexivity).
    rewrite HsrcX, Hrem, app_nil_r. unfold rmc_Tpre. reflexivity.
  - (* i < N - 1: src = entry_bytes (last es), rmc_concat_cpy closes it *)
    assert (Hilt : (i < length es - 1)%nat) by lia.
    pose proof (rmc_nth_last es relay_remove_b_c.no_entry ltac:(lia)) as Hnl.
    assert (HsrcL : src = entry_bytes (last es relay_remove_b_c.no_entry)).
    { rewrite Hsrc, HB, (app_assoc (rmc_Tpre es i) X).
      replace (56 * (length es - 1))%nat
        with (length (rmc_Tpre es i ++ X) + 56 * (length es - 1 - (i + 1)))%nat
        by (rewrite length_app, HLpre, HX; lia).
      rewrite skipn_app, skipn_all2 by lia.
      replace (length (rmc_Tpre es i ++ X) + 56 * (length es - 1 - (i + 1)) - length (rmc_Tpre es i ++ X))%nat
        with (56 * (length es - 1 - (i + 1)))%nat by lia.
      rewrite app_nil_l. unfold rmc_Tpost.
      rewrite (rmc_slot_k (skipn (S i) es) tail (length es - 1 - (i + 1)) relay_remove_b_c.no_entry).
      - rewrite rmc_nth_skipn, <- Hnl. f_equal. f_equal. lia.
      - rewrite length_skipn. lia.
      - apply rmc_forall_skipn; exact HE56. }
    rewrite HsrcL.
    pose proof (rmc_concat_cpy i es Hi) as Hcc.
    assert (Hup : concat (map entry_bytes (rmc_upd i (last es relay_remove_b_c.no_entry) es))
                  = rmc_Tpre es i ++ entry_bytes (last es relay_remove_b_c.no_entry) ++
                    concat (map entry_bytes (skipn (S i) es))).
    { unfold rmc_upd, rmc_Tpre. rewrite rmc_cmap_app, rmc_cmap_cons. reflexivity. }
    rewrite Hup in Hcc. exact Hcc.
Qed.
(* the fds of the removal are distinct *)
Lemma rmc_nodup_remove : forall (es : list rentry) i, (i < length es)%nat ->
  List.NoDup (map re_fd es) -> List.NoDup (map re_fd (relay_remove_b_c.remove_at i es)).
Proof.
  intros es i Hi HND.
  pose proof (Permutation_map re_fd (rm_remove_perm es i relay_remove_b_c.no_entry Hi)) as HPm.
  apply (Permutation_NoDup HPm) in HND. cbn [map] in HND. apply List.NoDup_cons_iff in HND as [_ HND]. exact HND.
Qed.
(* a 16-aligned base plus 56 k is 8-aligned *)
Lemma rmc_mod8 : forall g k, g mod 16 = 0 -> (g + 56 * k) mod 8 = 0.
Proof.
intros g k H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
replace (q * 16 + 56 * k) with ((2 * q + 7 * k) * 8) by ring. apply Z_mod_mult.
Qed.

(* ------------------------------------------------------------------ the seat at 0x84360 (new) *)
(* registers: atoms 0 .. 31 (s1 = rg_nsrc + 1304: atom 9; s2 = the shadow offset: atom 18; s3 = 56 i: atom 19; s4 =
   rg_src + 1288: atom 20); atom 32 = G0 (g_src's 8 bytes at s4 - 1288), atom 33 = N (g_nsrc's 4 bytes at s1 - 1304),
   atom 34 = G0 + 56 i, atom 35 = G0 + 56 (N - 1). *)
Definition RMC_PHI : Z := 140737479966720.
Definition rmc_src : YP09.region :=
  YP09.mkRegion (Some 20%nat) (-1288) (-1280) 0 0 [YP09.mkChunk (-1288) (CVal 8 (SOff 32 0))].
Definition rmc_nsrc : YP09.region :=
  YP09.mkRegion (Some 9%nat) (-1304) (-1300) (-1304) (-1300) [YP09.mkChunk (-1304) (CVal 4 (SOff 33 0))].
Definition rmc_facts : facts :=
mkFacts [ (9%nat, mkAF 1304 (0x7fff8000 + 1300) 0); (18%nat, mkAF SB SB 0); (19%nat, mkAF 0 840 3);
  (32%nat, mkAF 4096 RMC_PHI 4); (33%nat, mkAF 1 16 0);
  (34%nat, mkAF 4096 RMC_PHI 3); (35%nat, mkAF 4096 RMC_PHI 3) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 19 0), SOff 34 0); (SAlu ALU_ADD (SOff 19 0) (SOff 32 0), SOff 34 0);
    (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 33 (-1)) (SLit 56)), SOff 35 0) ].
Definition ss_rmc : sstate := mkSS A_rr_cpy sr_atoms [rmc_src; rmc_nsrc] None rmc_facts.
Definition rmc_Bx : sv := SOff 18 0.
Definition rmc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rmc_extra (G0 N SA L : Z) : list word := map (Z_to_bv 64) [G0; N; SA; L].
(* the registers the run does not write (it writes ra and a0 .. a5) *)
Definition RMC_KEPT : list (bv 5) := [21; 22; 23; 24; 25; 26; 27; 2; 3; 4; 8; 9; 18; 19; 20]%bv.
Lemma rmc_in_kept : forall r : bv 5, 21 <= bv_unsigned r <= 27 -> In r RMC_KEPT.
Proof.
intros r Hr. unfold RMC_KEPT. cbn [In].
assert (Hc : bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|E]]]]]];
[left | right; left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left | do 6 right; left];
apply bv_eq; rewrite E; reflexivity.
Qed.
(* a run's write windows: region 1's (g_nsrc) only *)
Ltac rmc_awr U9 :=
lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT STK sp0 FP b0 bc ly own) end;
apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; lia|];
apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha; unfold RR_HI_NSRC in Ha;
unfold inG, G_RR; apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia.
(* a byte off g_nsrc is in no run's write window *)
Ltac rmc_nowin U9 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin; destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U9 in Hr; unfold RR_HI_NSRC in Hr; lia].

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
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL); image B's closed singleton row) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
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
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
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
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ---- The kept bytes of this hop: image bytes off g_nsrc, and the bytes of the live blocks OB other than the table
   (the A twin's rck / rcz: this hop writes g_nsrc, slot i of the table and the memcpy's scratch). ---- *)
Definition rck (OB : list (Z * Z)) (a : Z) : Prop :=
  (in_img SEGS a /\ ~ (rg_nsrc RG <= a < rg_nsrc RG + 4)) \/
  (exists p n, In (p, n) OB /\ p <= a < p + req_size n).
Definition rcz (OB : list (Z * Z)) (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> rck OB a.
Lemma rcz_nil : forall OB, rcz OB [].
Proof. intros OB r []. Qed.
Lemma rcz_cons : forall OB r fp, (forall a, fst r <= a < snd r -> rck OB a) -> rcz OB fp -> rcz OB (r :: fp).
Proof. intros OB r fp H1 H2 r' [<- | Hr]; [exact H1 | exact (H2 r' Hr)]. Qed.
Lemma rcz_app : forall OB f1 f2, rcz OB f1 -> rcz OB f2 -> rcz OB (f1 ++ f2).
Proof. intros OB f1 f2 H1 H2 r Hr. apply in_app_or in Hr as [Hr | Hr]; [exact (H1 r Hr) | exact (H2 r Hr)]. Qed.
Lemma rck_blk : forall OB p n len a, In (p, n) OB -> 0 <= n -> len <= n -> p <= a < p + len -> rck OB a.
Proof.
intros OB p n len a Hin Hn Hl Ha. right. exists p, n. split; [exact Hin|].
pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rmc_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rmc_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma rmc_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, rmc_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma rmc_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma rcz_alist : forall OB ly S W mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> rck OB a) ->
  (forall b, In b (alist_blks l) -> In b OB) -> rcz OB (alist_fp LA l).
Proof.
intros OB ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA HOB.
rewrite Forall_forall in H9.
unfold alist_fp. apply rcz_cons; [exact HLA|]. apply rcz_app.
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply rcz_nil|].
  destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
  assert (HB : In (hl_v l, AREC * hl_cap l) OB).
  { apply HOB. unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
  apply rcz_cons; [|apply rcz_nil]. cbn [gfp fst snd]. intros a Ha.
  rewrite rmc_bzs_len, length_app, Nat2Z.inj_add, rmc_recs_len, Hj in Ha. unfold hl_n, AREC in *.
  apply (rck_blk OB (hl_v l) (16 * hl_cap l) (16 * hl_cap l) a HB); lia.
- intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd]. intros a Ha.
  assert (HB : In (fst x, Z.of_nat (length (snd x)) + 1) OB).
  { apply HOB. unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx. }
  rewrite rmc_bzs_len, length_app in Ha. cbn [length] in Ha.
  apply (rck_blk OB (fst x) (Z.of_nat (length (snd x)) + 1) (Z.of_nat (length (snd x)) + 1) a HB); lia.
Qed.
Lemma rcz_asrc : forall OB ly S W mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> rck OB a) ->
  (forall b, In b (asrc_blks h) -> In b OB) -> rcz OB (asrc_fp HA h).
Proof.
intros OB ly S W mem HA h HS HHA HOB.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                  _ & Hexp & Hheld & _).
assert (K16 : forall a, HA + 16 <= a < HA + 16 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K64 : forall a, HA + 64 <= a < HA + 64 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K80 : forall a, HA + 80 <= a < HA + 80 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
pose proof (rcz_alist OB ly S W mem (HA + 16) (hs_pending h) false Hpend K16
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; left; exact Hb)) as A1.
pose proof (rcz_alist OB ly S W mem (HA + 64) (hs_expected h) true Hexp K64
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as E1.
pose proof (rcz_alist OB ly S W mem (HA + 80) (hs_held h) true Hheld K80
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as L1.
unfold asrc_fp. apply rcz_cons; [exact HHA|]. apply rcz_cons.
- cbn [gfp fst snd]. intros a Ha. rewrite rmc_bzs_len, Hpj in Ha.
  apply (rck_blk OB (hs_partial h) APARTIAL APARTIAL a (HOB _ (or_introl eq_refl))); unfold APARTIAL in *; lia.
- apply rcz_app; [exact A1|]. apply rcz_app; [exact E1 | exact L1].
Qed.
Lemma rcz_aentry : forall OB ly S W mem e,
  aentry_ok B ly S W mem e -> (forall b, In b (aentry_blks e) -> In b OB) -> rcz OB (aentry_fp e).
Proof.
intros OB ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) HOB.
rewrite Forall_forall in K15.
unfold aentry_fp. apply rcz_app.
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply rcz_nil|].
  destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  assert (HB : In (re_buf e, re_cap e) OB).
  { apply HOB. unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
  apply rcz_cons; [|apply rcz_nil]. cbn [gfp fst snd]. intros a Ha.
  rewrite rmc_bzs_len, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (rck_blk OB (re_buf e) (re_cap e) (re_cap e) a HB); lia.
- apply rcz_cons.
  + cbn [gfp fst snd]. intros a Ha. rewrite rmc_bzs_len, rmc_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    assert (HB : In (re_hp e, re_kh e) OB).
    { apply HOB. unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity. }
    unfold re_nheld in Hk1.
    apply (rck_blk OB (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a HB); lia.
  + intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd]. intros a Ha.
    assert (HB : In (key_addr k, Z.of_nat (length (key_text k)) + 1) OB).
    { apply HOB. unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk. }
    rewrite rmc_bzs_len, length_app in Ha. cbn [length] in Ha.
    apply (rck_blk OB (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a HB);
      lia.
Qed.
Lemma rcz_aout : forall OB ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> rcz OB (aout_fp B RG 0 0) ->
  (forall b, In b (aout_blks cap out) -> In b OB) -> rcz OB (aout_fp B RG cap out).
Proof.
intros OB ly S W mem c O mx no cap out HO HC HOB.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hblk).
intros r Hr a Ha. destruct (rm_aout_fp_cases B RG cap out r Hr) as [Hr0 | (Hc & ->)]; [exact (HC r Hr0 a Ha)|].
destruct Hblk as [(Hc0 & _) | (Hcp & _ & Hin & _)]; [lia|].
assert (HB : In (out, cap) OB) by (apply HOB; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); left; reflexivity).
cbn [fst snd] in Ha. apply (rck_blk OB out cap cap a HB); lia.
Qed.

(* ---- the global cells the post reads, other than g_nsrc: image bytes apart from g_nsrc (HRGP) ---- *)
Definition rmc_cells (a : Z) : Prop :=
  rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
  rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
  rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
  rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
  rg_wake RG + 4 <= a < rg_wake RG + 8 \/ as_errno B <= a < as_errno B + 4.
Ltac rmc_exists := repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Lemma rmc_cell_img : rg_place B RG -> forall a, rmc_cells a -> in_img SEGS a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rmc_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
first [ exact (proj1 (RGIMG a ltac:(unfold rg_rng; tauto)))
      | exact (proj1 (HRGI a ltac:(tauto)))
      | exact (proj1 (HG a ltac:(unfold inG, G_RR, G_DR, G_SL; rmc_exists))) ].
Qed.
Lemma rmc_cell_nnsrc : forall a, rmc_cells a -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4).
Proof.
intros a Ha. pose proof HRGP as H. cbn [zpairwise_disjoint zall_disjoint] in H. unfold zdisj in H. cbn [fst snd] in H.
destruct H as ((_ & _ & D0 & _) & (_ & D1 & _) & (D2 & _) &
  (D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _) & _).
unfold rmc_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
[revert D0 Ha | revert D1 Ha | revert D2 Ha | revert D4 Ha | revert D5 Ha | revert D6 Ha | revert D7 Ha |
 revert D8 Ha | revert D9 Ha | revert D10 Ha | revert D11 Ha | revert D12 Ha | revert D13 Ha | revert D14 Ha];
clear; intros; lia.
Qed.
Lemma rmc_kept_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof.
intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))].
Qed.
(* byte arrays moved, cut *)
Lemma rmc_garr8_moved : forall (W W' : world SEGS) m m' a b l,
  garr8 SEGS (arm W m) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (a + j)) ->
  garr8 SEGS (arm W' m') b l.
Proof.
intros W W' m m' a b l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
unfold arm in *. apply (val_mem_moved SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (b + Z.of_nat j) 1); [|exact Hv].
intros k Hk'. cbn in Hk'. replace k with 0 by lia. rewrite !Z.add_0_r. apply Hk. lia.
Qed.
Lemma rmc_garr8_skipn : forall m a (l : list Z) k, (k <= length l)%nat -> garr8 SEGS m a l ->
  garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k Hk Hg. rewrite <- (firstn_skipn k l) in Hg. apply garr8_app in Hg as [_ Hg].
rewrite length_firstn, Nat.min_l in Hg by lia. exact Hg.
Qed.
Lemma rmc_garr8_firstn : forall m a (l : list Z) k, garr8 SEGS m a l -> garr8 SEGS m a (firstn k l).
Proof.
intros m a l k Hg. rewrite <- (firstn_skipn k l) in Hg. apply garr8_app in Hg as [Hg _]. exact Hg.
Qed.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_order_x.v and
   lib/B/W_bx_reset_x.v): hop CPY at a world relation R, W_rr_match_cx.v's hop_cpy_stmt_xR (RRC_xR i -> RRU_xR
   (Some i), rPOST_xR), over W_relay_remove_cx.v's RLIVE_xR / RDONE_xR.  Against the strict texts only these change:
   ajournal_gx_x .. ARx -> ajournal_gx_xR .. ARx R, RLIVE / RDONE / hop_cpy_stmt -> their _xR .. R, SRr SEGS -> SRrG
   SEGS R, the runs and the branch -> their SRrG forms (W_journal_x.v paj_run_x_xG with W_kit_x.v paj_run_tok_xR,
   W_kit.v paj_branch_xR), the bind -> SRrG_bind SEGS R R_trans, the call -> W_sites_x.v aj_gx_entry_at_xR (the
   memcpy's contracts AMEMCPY / AMEMCPYS stay strict: the call moves no world, aj_gx_entry_at_xR lifts them by
   SRr_SRrG), and the journal lemmas -> their _xR twins (W_journal_x.v).  No W_rr_m_kit.v helper this hop cites
   carries a journal, so it needs no kit twin.  At R := wle each twin is its strict text: rmc_post and rr_m_cpy after
   the Section are these at wle (moved below the Section; their statements are unchanged).
   Census rows -> twins: :392 AFREE -> AFREE_R, :396 DRAIN -> DRAIN_R, :397 GSE -> GSE_R, :399 AFREEN -> AFREEN_R
   (declared; the hop calls no free and no program function, so they vanish from the lemmas), :592 rmc_post ->
   rmc_post_xR, :784 rr_m_cpy -> rr_m_cpy_xR. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary set RO (the free rules' type names it) *)
Variable RO : (word -> option byte) -> Prop.
(* :392 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :396 DRAIN, :397 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :399 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* the runs and the branch at R (W_journal_x.v paj_run_x_xG, W_kit.v paj_branch_xR) *)
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* :592 rmc_post at R *)
Lemma rmc_post_xR : forall cx i ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 ev LB c2 O2 cap2 out2 X m3 md3,
RBASE B ARx MT RP MMAX RG cx ->
0 <= rxFD cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
RLIVE_xR B PST ARx R RG cx ly1 S1 Hp1 W1 m1 md1 k1 ->
rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
rmtbl B RG cx i ly1 S1 W1 m1 X ->
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) ->
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 ->
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
rmgs RG cx W1 m1 ->
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) ->
rp_RM RP S1 (rxkr cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
val_mem SEGS (arm W1 m3) (rg_nsrc RG) 4 (rN cx - 1) ->
(forall t, 0 <= t < AENT ->
   aview SEGS (w_H W1) m3 (rmSA cx i + t) = aview SEGS (w_H W1) m1 (rxG0 cx + AENT * (rN cx - 1) + t)) ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m3 md3 k1 ->
RDONE_xR B PST ARx R MT RP RG cx i ly1 S1 Hp1 W1 m3 md3 k1.
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 ev LB c2 O2 cap2 out2 X m3 md3
  HB HFD0 Hi Hfd HAR HLV HDR HTB HSL HOUT HPERM HGS HMO HRM KM PM NSM SLM HJ3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & HSRC0 & HPERM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _ & _).
pose proof HLV as (HJ1 & HROM1 & HPK1 & HSV1 & HLK1 & HWK1).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
(* image B's journal is at RR_STK_x (the A twin: RR_STK) *)
assert (WS : RR_STK_x = ltac:(let v := eval vm_compute in RR_STK_x in exact v)) by reflexivity.
assert (WF : RR_FRAME = 48) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
assert (HSP : rsp0 cx <= 2 ^ 47) by lia.
clear Hceil Hslo Hshi H47 Hstk HPRE.
pose proof HTB as (Tsrc & Tsrcw & Tnsrc & Tnsrcw & Tcap & Tcapw & TIn & TX & (tail & Ttl & Ttab) & Tslw & Tok).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _ & _ & ROK & RND & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & _ & _ & _).
change (req_size ATABLE) with 896 in HGceil.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
(* the other blocks: live, apart from the table *)
set (OB := rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx).
assert (OBIN : forall b, In b OB -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (OBNE : forall b, In b OB -> b <> (rxG0 cx, ATABLE)).
{ intros b Hb Eb. assert (ND : List.NoDup (ablocks B ly1 S1)) by (eapply rm_ablocks_nodup; eassumption).
  apply (Permutation_NoDup HPERM) in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. rewrite <- Eb. exact Hb. }
assert (NSIMG : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> in_img SEGS a)
  by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (TBIMG : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ in_img SEGS a)
  by (intros a Ha; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE a HAR TIn
        ltac:(change (req_size ATABLE) with 896; lia))).
(* THE KEEP: a kept byte keeps its view (none of g_nsrc, slot i, the scratch) and its writability *)
assert (KEEP : forall a, rck OB a -> abyte_kept W1 m1 W1 m3 a).
{ intros a Ha. split; [|intros Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 m3 a (PM a) Hw)].
  destruct Ha as [(Himg & Hn) | (p & n & Hin & Hpa)].
  - pose proof (Hsegs a Himg) as Hl. apply KM; [lia | exact Hn | | lia].
    intros Hs. apply (TBIMG a); [unfold rmSA, AENT in *; lia | exact Himg].
  - pose proof (OBIN _ Hin) as Hin'.
    destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as (_ & Hp4096 & Hpceil & _ & _ & _).
    pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as Hn.
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (rxG0 cx) ATABLE HAR Hin' TIn (OBNE _ Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
    apply KM; [lia | | | lia].
    + intros Hs. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n a HAR Hin' Hpa (NSIMG a Hs)).
    + unfold rmSA, AENT in *. lia. }
assert (CKZ : forall a, rmc_cells a -> rck OB a)
  by (intros a Ha; left; split; [exact (rmc_cell_img RGP a Ha) | exact (rmc_cell_nnsrc a Ha)]).
assert (AK : forall fp, rcz OB fp -> akept W1 m1 W1 m3 fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (OUTC : rcz OB (aout_fp B RG 0 0)).
{ intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
  [cbn [fst snd] in Ha; unfold rmc_cells; tauto .. | simpl in Hr; destruct Hr]. }
(* the table outside slot i *)
assert (TB : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hs. apply KM; [lia | intros Hn; exact (TBIMG a Ha (NSIMG a Hn)) | exact Hs | lia]. }
unfold RDONE_xR. split; [|split; [exact Hi|split; [exact Hfd|split; [exact HMO|split; [|split; [|exact HRM]]]]]].
- (* RLIVE *)
  split; [exact HJ3|].
  split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJ3 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [intros a H1 H2 H3 Hp; apply PM; exact (HPK1 a H1 H2 H3 Hp)|].
  split; [|split].
  + (* the six saved registers, above sp *)
    intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m3 _ 8 _); [|exact (HSV1 j Hj)].
    intros t Ht. change (Z.of_nat 8) with 8 in Ht. apply KM; [lia | | | lia].
    * intros Hn. pose proof (Hsegs _ (NSIMG _ Hn)). lia.
    * unfold rmSA, AENT in *. lia.
  + (* g_lock held *)
    eapply alock_at_kept; [exact HLK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. left. exact Ha.
  + eapply awake_at_kept; [exact HWK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. tauto.
- (* g_s as at the entry outside drain's slot j *)
  intros a Ha Hj. apply (rmc_kept_trans _ _ _ _ _ _ a (HGS a Ha Hj)). apply KEEP. apply CKZ. unfold rmc_cells. tauto.
- (* rr_found *)
  unfold rr_found. cbv zeta.
  exists e1, h1, ev, LB, c2, O2, cap2, out2, (rxrest cx).
  split.
  { destruct (re_eof (nth i (rxes cx) relay_remove_b_c.no_entry) =? 0) eqn:Eo.
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. destruct HDR as (HDR1 & HAS).
      split; [exact HDR1|].
      assert (HOBs : forall b, In b (asrc_blks h1) -> In b OB).
      { intros b Hb. unfold OB, rmsrc, rmopen, rnth. rewrite Eo. apply in_or_app. right. apply in_or_app. left. exact Hb. }
      apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 _ h1 HAS).
      + apply AK. apply (rcz_asrc OB ly1 S1 W1 m1 _ h1 HAS); [|exact HOBs].
        intros a Ha. apply CKZ. unfold rmc_cells. right. left. unfold rmHA, ASRC in *.
        pose proof (proj1 (HSRC0 i Hi Hfd (proj1 (Z.eqb_eq _ _) Eo))) as Hj4. lia.
      + intros b Hb. exact (OBIN b (HOBs b Hb)).
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. exact HDR. }
  split; [exact HSL|].
  split.
  { (* the relay's table after the copy: remove_at i es *)
    assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
    { eapply Forall_impl; [|exact ROK]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
    pose proof (rm_remove_length (rxes cx) i Hi) as HRL.
    assert (LTpre : length (rmTpre cx i) = (56 * i)%nat).
    { unfold rmTpre. rewrite rm_concat_len by (apply rmc_forall_firstn; exact HPADS). rewrite length_firstn. lia. }
    assert (LTpost : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
    { unfold rmTpost. rewrite rm_concat_len by (apply rmc_forall_skipn; exact HPADS). rewrite length_skipn. lia. }
    assert (LX : length X = 56%nat) by (unfold AENT in TX; lia).
    set (Bl := rmTpre cx i ++ X ++ rmTpost cx i ++ tail) in Ttab.
    assert (LBl : length Bl = 896%nat).
    { unfold Bl. rewrite !length_app, LTpre, LX, LTpost. unfold rN, ATABLE, AENT in Ttl. lia. }
    set (src := firstn 56 (skipn (56 * (length (rxes cx) - 1)) Bl)).
    assert (Lsrc : length src = 56%nat) by (unfold src; rewrite length_firstn, length_skipn, LBl; lia).
    assert (EQB : firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl =
                  concat (map entry_bytes (relay_remove_b_c.remove_at i (rxes cx))) ++ src ++ tail)
      by (apply (rmc_block_cpy (rxes cx) tail X src Bl i Hi LX HPADS); reflexivity).
    assert (GNL : garr8 SEGS (arm W1 m3) (rxG0 cx) (bzs (firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl))).
    { unfold bzs in Ttab |- *. rewrite !map_app. apply garr8_app. split.
      - apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx) (rxG0 cx)).
        + rewrite <- firstn_map. apply rmc_garr8_firstn. exact Ttab.
        + intros j Hj. rewrite length_map, length_firstn in Hj. apply TB; [lia | unfold rmSA, AENT; lia].
      - rewrite length_map, length_firstn, Nat.min_l by lia. apply garr8_app. split.
        + apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * (length (rxes cx) - 1))) _).
          * unfold src. rewrite <- firstn_map, <- skipn_map. apply rmc_garr8_firstn. apply rmc_garr8_skipn;
            [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, Lsrc in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + j) with (rmSA cx i + j) by (unfold rmSA, AENT; lia).
            rewrite (SLM j ltac:(unfold AENT; lia)). f_equal. unfold rN, AENT. lia.
        + rewrite length_map, Lsrc.
          apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * i + 56)) _).
          * rewrite <- skipn_map. apply rmc_garr8_skipn; [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, length_skipn, LBl in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + Z.of_nat 56 + j) with (rxG0 cx + Z.of_nat (56 * i + 56) + j) by lia.
            apply TB; [lia | unfold rmSA, AENT; lia]. }
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tsrc]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tsrcw]|].
    split.
    { rewrite HRL. replace (Z.of_nat (length (rxes cx) - 1)) with (rN cx - 1) by (unfold rN; lia). exact NSM. }
    split; [intros k Hk; unfold arm; exact (writable_kept (w_H W1) m1 m3 _ (PM _) (Tnsrcw k Hk))|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tcap]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tcapw]|].
    split; [rewrite HRL; lia|].
    split; [exact TIn|].
    split.
    { exists (src ++ tail). split; [|split].
      - rewrite length_app, Nat2Z.inj_add, Lsrc, Ttl, HRL. unfold rN, ATABLE, AENT. lia.
      - rewrite <- EQB, !length_app, length_firstn, Lsrc, length_skipn, LBl. unfold ATABLE. lia.
      - rewrite <- EQB. exact GNL. }
    split.
    { rewrite Forall_forall in Tok |- *. intros e He.
      assert (HOBe : forall b, In b (aentry_blks e) -> In b OB).
      { intros b Hb. unfold OB, rmOB. apply in_or_app. left. apply in_concat. exists (aentry_blks e).
        split; [apply in_map; exact He | exact Hb]. }
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 e (Tok e He)).
      - apply AK. exact (rcz_aentry OB ly1 S1 W1 m1 e (Tok e He) HOBe).
      - intros b Hb. exact (OBIN b (HOBe b Hb)). }
    split.
    { apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply rmc_nodup_remove; [exact Hi|].
      exact (proj1 (stdpp.base.NoDup_ListNoDup _) RND). }
    (* no entry's block is the table (arelay_at's twelfth conjunct, the kit's W_rep): W_rr_match_cx.v's rm_base_notab *)
    exact (rm_base_notab B ARx MT RP MMAX RG cx i HB Hi). }
  split.
  { apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m3 _ _ _ _ _ _ HOUT).
    - apply AK. apply (rcz_aout OB ly1 S1 W1 m1 _ _ _ _ _ _ HOUT OUTC).
      intros b Hb. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    - intros b Hb. apply OBIN. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  split.
  { rewrite (rm_drains cx i (proj1 (stdpp.base.NoDup_ListNoDup _) RND) HFD0 Hi Hfd) in HPERM0. exact HPERM0. }
  exact HPERM.
Qed.

(* :784 rr_m_cpy at R *)
Theorem rr_m_cpy_xR : hop_cpy_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
unfold hop_cpy_stmt_xR. intros cx i W1 c1 HB HC KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
destruct HC as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & X &
  -> & HMH & HLV & HDR & HTB & HSL & HOUT & HPERM & HGS & HMO & HRM).
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _ & _).
destruct HMH as (HRH & H19 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & H3 & H4 & H2127) & H8 & H9 & H18 & H20).
pose proof HLV as (HJ & _).
pose proof HTB as (Tsrc & _ & Tnsrc & Tnsrcw & _ & _ & TIn & _ & _ & _ & _).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
change (req_size ATABLE) with 896 in HGceil, HGapp, HGpres.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
assert (NUM : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= RMC_PHI /\ 1 <= rN cx <= 16 /\ 0 <= Z.of_nat i < rN cx)
  by (unfold RMC_PHI, rN in *; lia).
assert (M19 : (AENT * Z.of_nat i) mod 8 = 0)
  by (unfold AENT; replace (56 * Z.of_nat i) with ((7 * Z.of_nat i) * 8) by ring; apply Z_mod_mult).
assert (M34 : (rxG0 cx + AENT * Z.of_nat i) mod 8 = 0) by (apply rmc_mod8; exact HG16).
assert (M35 : (rxG0 cx + AENT * (rN cx - 1)) mod 8 = 0) by (apply rmc_mod8; exact HG16).
assert (LS : 0 <= rg_src RG /\ rg_src RG + 8 <= kLowMemEnd).
{ pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; lia)))) as A1.
  pose proof (Hsegs _ (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; lia)))) as A2. lia. }
assert (LN : 0 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= kLowMemEnd).
{ pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG) ltac:(unfold rg_rng; lia)))) as A1.
  pose proof (Hsegs _ (proj1 (RGIMG (rg_nsrc RG + 3) ltac:(unfold rg_rng; lia)))) as A2. lia. }
remember (Eimg (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx) (rmSA cx i) (rxG0 cx + AENT * (rN cx - 1))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx) (rmSA cx i) (rxG0 cx + AENT * (rN cx - 1)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rN cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rmSA cx i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rxG0 cx + AENT * (rN cx - 1)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E9 : ew E 9 = Z_to_bv 64 (rg_nsrc RG + RR_HI_NSRC)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (rg_src RG + RR_HI_SRC)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (U9 : bv_unsigned (ew E 9) = rg_nsrc RG + RR_HI_NSRC)
  by (rewrite E9; apply unsigned_lit_small; unfold RR_HI_NSRC, kLowMemEnd in *; lia).
assert (U20 : bv_unsigned (ew E 20) = rg_src RG + RR_HI_SRC)
  by (rewrite E20; apply unsigned_lit_small; unfold RR_HI_SRC, kLowMemEnd in *; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmc (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_cpy)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmc. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, rmc_src, rmc_nsrc;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U20. split; [unfold RR_HI_SRC; lia|]. split; [unfold RR_HI_SRC, kLowMemEnd in *; lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_src RG + RR_HI_SRC) (-1288) 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (rg_src RG + RR_HI_SRC + -1288) with (rg_src RG) by (unfold RR_HI_SRC; lia). exact Tsrc.
  + rewrite U9. split; [unfold RR_HI_NSRC; lia|]. split; [unfold RR_HI_NSRC, kLowMemEnd in *; lia|].
    split; [intros o Ho; replace (rg_nsrc RG + RR_HI_NSRC + o) with (rg_nsrc RG + (o + 1304)) by (unfold RR_HI_NSRC; lia);
            apply Tnsrcw; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nsrc RG + RR_HI_NSRC) (-1304) 4 (SOff 33 0) (rN cx));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (rg_nsrc RG + RR_HI_NSRC + -1304) with (rg_nsrc RG) by (unfold RR_HI_NSRC; lia). exact Tnsrc.
- apply pairwise_disjoint_of_extents. unfold rmc_src, rmc_nsrc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U9.
  pose proof HRGP as HP. cbn [zpairwise_disjoint zall_disjoint] in HP. unfold zdisj in HP. cbn [fst snd] in HP.
  destruct HP as (_ & _ & (D23 & _) & _).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold RR_HI_SRC, RR_HI_NSRC.
  repeat split; try exact I; lia.
- split; [|split; [exact I|]].
  + cbn [rmc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E18, E19, E32, E33, E34, E35.
    rewrite !unsigned_lit_small
      by (clear - NUM LN C5; unfold SHADOW_OFF, rmSA, AENT, RMC_PHI, RR_HI_NSRC, kLowMemEnd in *; lia).
    change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    clear - NUM M19 M34 M35 HG16 LN C5. unfold rmSA.
    repeat match goal with |- _ /\ _ => split end; try assumption;
    unfold SB, SHADOW_OFF, RMC_PHI, AENT, RR_HI_NSRC, kLowMemEnd in *; lia.
  + cbn [rmc_facts f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = U E (SOff 34 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 34 _ E34)
        by (clear - NUM; unfold rmSA, AENT, RMC_PHI in *; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (clear - NUM; unfold AENT, RMC_PHI in *; lia).
      unfold rmSA. reflexivity.
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = U E (SOff 34 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 34 _ E34)
        by (clear - NUM; unfold rmSA, AENT, RMC_PHI in *; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (clear - NUM; unfold AENT, RMC_PHI in *; lia).
      unfold rmSA. lia.
    * apply U_inj.
      rewrite (lin_nf_sound E (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 33 (-1)) (SLit 56)))
        [(32%nat, 1); (33%nat, 56)] (-56) ltac:(vm_compute; reflexivity)).
      cbn [lin_denot]. rewrite (U_atom E 35 _ E35) by (clear - NUM; unfold AENT, RMC_PHI in *; lia).
      rewrite E32, E33, !unsigned_lit_small by (clear - NUM; unfold RMC_PHI in *; lia).
      unfold M64. rewrite Z.mod_small by (clear - NUM; unfold RMC_PHI in *; lia). unfold AENT. lia. }
clear HE.
assert (SHOK : sh_ok SEGS rmc_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rr_cpy)) with (Z_to_bv 64 (BASE + A_rr_cpy)).
(* 0x84360 .. 0x84364: the load of g_src, a0 = &g_src[i]; stop at the first trap edge 0x84368 *)
paj_run_tok_xR RUNG HS HJ SHOK rmc_Bspan. { rmc_awr U9. }
rename HFr into HFr1, HG0 into HGr1. clear HF HEI0.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
(* TRAP EDGE 0x84368 bltu a0,a2 -> unimp: never taken, G0 + 56 i does not wrap below G0 *)
psrr_branch_tok RUNG BRR HS SHOK rmc_Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 34 32 (rxG0 cx) (AENT * Z.of_nat i) E34 E32) in Hc;
  [discriminate | clear - NUM; unfold AENT, RMC_PHI in *; lia ..]. }
clear Hc.
(* 0x84368 .. 0x843b4: the null-consistency xor (decided), the load of g_nsrc, the int32 decrement (decided), a1 =
   &g_src[N - 1], the store g_nsrc = N - 1, the null-consistency beq (decided); stop at the signed-index trap edge *)
paj_run_tok_xR RUNG HS HJ SHOK rmc_Bspan. { rmc_awr U9. }
rename HFr into HFr2, HG0 into HGr2. clear HF HEI0.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
(* TRAP EDGE 0x843b4 (slti / sltu / xor / xori 1 / beqz) -> unimp: never taken, both compares are 0 *)
psrr_branch_tok RUNG BRR HS SHOK rmc_Bspan.
{ exfalso. rewrite (trap_ptr_sovf E (SAlu ALU_SLTU (SOff 35 0) (SOff 32 0)) (SLit 0) 0) in Hc; [discriminate | |].
  - apply (trap_U_sltu_ge E (SOff 32 0) (SOff 35 0) (rxG0 cx) (rxG0 cx + AENT * (rN cx - 1)));
    [apply (U_atom E 32 _ E32) | apply (U_atom E 35 _ E35) | ]; clear - NUM; unfold AENT, RMC_PHI in *; lia.
  - rewrite U_SLit. reflexivity. }
clear Hc.
(* 0x843b8 .. 0x843bc: a2 = 56; the call *)
paj_run_tok_xR RUNG HS HJ SHOK rmc_Bspan. { rmc_awr U9. }
rename HFr into HFr3, HG0 into HGr3. clear HF HEI0.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as HRN. cbn [ms_mem restrict] in HRN.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ RMC_KEPT HS HAE ltac:(vm_compute; reflexivity)) as K2.
cbn [ms_regs restrict] in K2.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* ---- the state at the call: what the three runs changed (g_nsrc), the registers ---- *)
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
(* image B's journal is at RR_STK_x (the A twin: RR_STK) *)
assert (WS : RR_STK_x = ltac:(let v := eval vm_compute in RR_STK_x in exact v)) by reflexivity.
assert (WF : RR_FRAME = 48) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
pose proof HJ as HAR3. eapply ajournal_gx_AR_xR in HAR3.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) ->
  aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha) by (rmc_nowin U9).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha) by (rmc_nowin U9).
  apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha). rmc_nowin U9. }
assert (PR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGr3 (apresent_grows _ _ _ a HGr2 (apresent_grows _ _ _ a HGr1 Ha)))).
assert (NS3 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms3)) (rg_nsrc RG) 4 (rN cx - 1)).
{ replace (rg_nsrc RG) with (rg_nsrc RG + RR_HI_NSRC + -1304) by (unfold RR_HI_NSRC; lia).
  change 4%nat with (N.to_nat 4).
  apply (field_of_region E _ 9%nat _ _ _ _ _ _ (-1304) 4 (SOff 33 (-1)) (rN cx - 1) HRN).
  - exact U9.
  - left. reflexivity.
  - cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia. }
assert (SP3 : spZ (ms_regs ms3) = rsp0 cx - RR_FRAME).
{ unfold spZ. rewrite (K2 2%bv ltac:(cbn; tauto)). exact Hsp1. }
assert (A10 : getr (ms_regs ms3) 10 = w64 (rmSA cx i)) by (rewrite P10, E34; reflexivity).
assert (A11 : getr (ms_regs ms3) 11 = w64 (rxG0 cx + AENT * (rN cx - 1))) by (rewrite P11, E35; reflexivity).
assert (HSLOT : forall a, rmSA cx i <= a < rmSA cx i + AENT -> rxG0 cx <= a < rxG0 cx + 896)
  by (intros a Ha; unfold rmSA, AENT in *; lia).
assert (HLAST : forall a, rxG0 cx + AENT * (rN cx - 1) <= a < rxG0 cx + AENT * (rN cx - 1) + AENT ->
  rxG0 cx <= a < rxG0 cx + 896) by (intros a Ha; unfold AENT in *; lia).
(* ---- __asan_memcpy (&g_src[i], &g_src[N - 1], 56) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RR B RG) 0 [] ESTACK (SIGMA WS_asan_memcpy)
    (fun a => rmSA cx i <= a < rmSA cx i + AENT)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) => forall t, 0 <= t < AENT ->
       aview SEGS (w_H W1) mem' (rmSA cx i + t) = aview SEGS (w_H W1) (ms_mem ms3) (rxG0 cx + AENT * (rN cx - 1) + t))
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-48) _ HG eq_refl
    HJ).
  - rewrite SP3, WF. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite (K2 3%bv ltac:(cbn; tauto)), H3. exact Hgp.
  - rewrite (K2 4%bv ltac:(cbn; tauto)), H4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rmSA cx i)); [right; lia|].
    destruct (Z_lt_ge_dec a (rmSA cx i + AENT)); [left; lia | right; lia].
  - intros a Ha HGa. exfalso. destruct (HG a HGa) as (Himg & _ & _).
    refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE a HAR3 TIn _ Himg).
    change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros a Ha _. split; [|lia].
    right. left. split.
    + unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
      apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE); [left; reflexivity | change (req_size ATABLE) with 896; pose proof (HSLOT a Ha); lia].
    + exists (rxG0 cx), ATABLE. split; [exact TIn|]. change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros HPRE3 _.
    assert (DEST : dest_ok SEGS B ly1 S1 W1 (ms_regs ms3) (ms_mem ms3) (rmSA cx i) AENT).
    { intros a Ha. destruct (HGpres a (HSLOT a Ha)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact (PR a Hp)|]. split; [exact Hno|].
      rewrite SP3. pose proof (HSLOT a Ha). lia. }
    assert (CHK : forall x, rxG0 cx <= x -> x + AENT <= rxG0 cx + 896 -> achecked W1 (ms_mem ms3) x AENT).
    { intros x Hx1 Hx2. split; [|split].
      - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE);
        [exact HAR3 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE);
        [exact HAR3 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE);
        [exact HAR3 | exact TIn | lia | change (req_size ATABLE) with 896; lia | exact Hpos]. }
    assert (SRC : src_ok SEGS W1 (ms_regs ms3) (ms_mem ms3) (rxG0 cx + AENT * (rN cx - 1)) AENT).
    { intros a Ha. split; [apply aview_some_of_apresent; exact (PR a (proj1 (HGpres a (HLAST a Ha))))|].
      rewrite SP3. pose proof (HLAST a Ha). lia. }
    destruct (Nat.lt_ge_cases (S i) (length (rxes cx))) as [Hlt | Hge].
    + (* i < N - 1: the copy of slot N - 1 (disjoint) *)
      destruct (CHK (rmSA cx i) ltac:(unfold rmSA, AENT; lia) ltac:(unfold rmSA, AENT; lia)) as (Cd1 & Cd2 & Cd3).
      destruct (CHK (rxG0 cx + AENT * (rN cx - 1)) ltac:(unfold AENT; lia) ltac:(unfold AENT; lia)) as (Cs1 & Cs2 & Cs3).
      eapply SRr_mono.
      { apply (AMEMCPY ly1 S1 Hp1 W1 (ms_regs ms3) (ms_mem ms3) _ (rmSA cx i) (rxG0 cx + AENT * (rN cx - 1)) AENT HPRE3
          A10 A11 P12); try (unfold rmSA, AENT; lia); [exact DEST | exact Cd1 | | exact Cd2 | exact Cd3 |].
        (* QMm W1 (B engine 9015b6a6f732): the dest is a slot of the heap block ATABLE, off the image, so no kept byte *)
        { intros a Ha HK. apply (kept_x_off_img SEGS B a); [|exact HK]. intros Himg.
          refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE a HAR3 TIn _ Himg).
          change (req_size ATABLE) with 896. exact (HSLOT a Ha). }
        split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [exact SRC|].
        split; [unfold rmSA, rN, AENT in *; lia|]. split; [exact Cs1|]. split; [exact Cs2 | exact Cs3]. }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hcp4 & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [exact Hcp4|]. split; [exact Hfr4 | exact Hpr4].
    + (* i = N - 1: onto itself *)
      assert (EL : rxG0 cx + AENT * (rN cx - 1) = rmSA cx i) by (unfold rmSA, rN, AENT; lia).
      rewrite EL in A11.
      eapply SRr_mono.
      { apply (AMEMCPYS ly1 S1 Hp1 W1 (ms_regs ms3) (ms_mem ms3) _ (rmSA cx i) AENT HPRE3 A10 A11 P12);
          try (unfold rmSA, AENT; lia); [exact DEST | rewrite <- EL; exact SRC | apply CHK; unfold rmSA, AENT; lia | | | ].
        - eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJ | exact HROMO | exact PSTR | exact HROM0].
        - intros _. eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE);
          [exact HAR3 | exact TIn | unfold rmSA, AENT; lia | change (req_size ATABLE) with 896; unfold rmSA, AENT; lia].
        - intros a Ha. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms3) _ (rxG0 cx) ATABLE a HAR3 TIn
            ltac:(change (req_size ATABLE) with 896; exact (HSLOT a Ha))). }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [|split; [intros a Ha _ Hsc; exact (Hfr4 a Ha (fun x => x) Hsc) | exact Hpr4]].
      intros t Ht. rewrite EL. apply Hfr4; [unfold rmSA, AENT in *; lia | intros x; exact x |].
      rewrite SP3. unfold rmSA, AENT in *. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPr3 & Hfr3 & Hpres3).
(* ---- back at 0x843c0: RRU (Some i) ---- *)
assert (K3 : forall r : bv 5, In r RMC_KEPT -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite <- (K2 r Hr). rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP3.
  unfold RMC_KEPT in Hr.
  repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved;
    lazymatch goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in
      change (bv_unsigned b) with v end; lia|]).
  destruct Hr. }
apply KU. exists regs3, ly1, S1, Hp1, mem3, md3, k1.
split; [reflexivity|].
split.
{ split; [unfold spZ; rewrite (K3 2%bv ltac:(cbn; tauto)); exact Hsp1|].
  split; [rewrite (K3 3%bv ltac:(cbn; tauto)); exact H3|].
  split; [rewrite (K3 4%bv ltac:(cbn; tauto)); exact H4|].
  intros r Hr. rewrite (K3 r (rmc_in_kept r Hr)). exact (H2127 r Hr). }
split; [exact HFD0|].
apply (rmc_post_xR cx i ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 ev LB c2 O2 cap2 out2 X mem3 md3 HB HFD0 Hi Hfd HAR HLV
  HDR HTB HSL HOUT HPERM HGS HMO HRM).
- intros a Ha Hn Hs Hsc. rewrite (Hfr3 a Ha Hs ltac:(rewrite WF in Hsc; lia)). exact (KR a Ha Hn).
- intros a Hp. exact (Hpres3 a (PR a Hp)).
- apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms3) mem3 (rg_nsrc RG) 4 (rN cx - 1)); [|exact NS3].
  intros k Hk. apply Hfr3.
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
  + intros Hs. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
      (proj1 (RGIMG (rg_nsrc RG + k) ltac:(unfold rg_rng; cbn in Hk; lia)))).
    change (req_size ATABLE) with 896. exact (HSLOT _ Hs).
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
- intros t Ht. rewrite (HPr3 t Ht). apply KR; [unfold AENT in *; lia|].
  intros Hn. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
    (proj1 (RGIMG (rxG0 cx + AENT * (rN cx - 1) + t) ltac:(unfold rg_rng; lia)))).
  change (req_size ATABLE) with 896. unfold AENT in *. lia.
- exact HJ3.
Qed.
End wR.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): each R premise at wle is
   the strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* ---- RDONE from RRC and what the hop did to the memory: only g_nsrc (N -> N - 1), slot i (the copy of slot N - 1)
   and the memcpy's scratch below sp changed, every present byte stays present, the journal holds.  Image B's RLIVE
   carries the six saved registers above sp (rr_saved) where the A twin carried its fake frame.  The room round: the
   hop allocates nothing, so RRC's rp_RM RP S1 kr is RDONE's last conjunct. ---- *)
Lemma rmc_post : forall cx i ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 ev LB c2 O2 cap2 out2 X m3 md3,
RBASE B ARx MT RP MMAX RG cx ->
0 <= rxFD cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
RLIVE B PST ARx RG cx ly1 S1 Hp1 W1 m1 md1 k1 ->
rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
rmtbl B RG cx i ly1 S1 W1 m1 X ->
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) ->
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 ->
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
rmgs RG cx W1 m1 ->
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) ->
rp_RM RP S1 (rxkr cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
val_mem SEGS (arm W1 m3) (rg_nsrc RG) 4 (rN cx - 1) ->
(forall t, 0 <= t < AENT ->
   aview SEGS (w_H W1) m3 (rmSA cx i + t) = aview SEGS (w_H W1) m1 (rxG0 cx + AENT * (rN cx - 1) + t)) ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m3 md3 k1 ->
RDONE B PST ARx MT RP RG cx i ly1 S1 Hp1 W1 m3 md3 k1.
Proof. eapply (rmc_post_xR (@wle SEGS)); wle_inst. Qed.

Theorem rr_m_cpy : hop_cpy_stmt B PST ARx MT RP MMAX RG.
Proof. eapply (rr_m_cpy_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
