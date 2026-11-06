(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 674 of its 718 lines of code are new or changed and 791 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_connect.v; 713 of its 835 lines of code are new or changed and 596 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rec_area_glob : forall a, rec_area a -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia. Qed.

Lemma rec_rep_O_in : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. exact (rep_at_blocks segs _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma rec_rep_keep : forall segs gr sc L A mem mem' R O,
  rec_rep segs gr sc L A mem R O ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' R O.
Proof.
  intros segs gr sc L A mem mem' R O (Q & HR & HO) KG KW KB. exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & _ & _ & HX & _).
  apply (rep_at_set_word segs (blocks L A) mem mem' gr sc R R Q HR eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. apply KG. unfold REC_SIZE. lia.
  - exact KW.
  - intros [p k] Hpn i Hi. exact (KB p k i (proj2 (HO (p, k)) Hpn) Hi).
  - apply (scalars_keep segs mem mem' gr R HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.

Lemma rec_entry_at : forall segs L A mem R fn As O,
  rec_rep segs G_REC REC_SC L A mem (rec_record R fn As) O ->
  exists P, call_at segs (blocks L A) mem (rec_entry G_REC REC_SC R) (fn, As) P.
Proof.
  intros segs L A mem R fn As O (Q & HR & _).
  pose proof HR as (_ & (C1 & C2 & _ & C4 & C5 & _) & _).
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (rec_record_lt R fn As Hn) in C2, C4.
    cbn [set_calls r_calls] in C2, C4. rewrite length_app in C2. cbn [length] in C2.
    destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP.
    + exists P. apply (C4 (length (r_calls R)) (fn, As) P); [|exact EP].
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + exfalso. apply nth_error_None in EP. lia.
  - assert (E : rec_record R fn As = set_spill R (fn, As)).
    { unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
    rewrite E in C1, C5. cbn [set_spill r_calls r_spill] in C1, C5.
    rewrite (rec_entry_full G_REC REC_SC R ltac:(lia)). exists (l_spill Q). exact C5.
Qed.

Lemma rec_entry_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  REC_SC <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE /\
  rec_entry G_REC REC_SC R mod 8 = 0.
Proof.
  intros R H. unfold rec_entry. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [E|E].
  - unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE.
    split; [lia|]. split; [lia|].
    apply Z.mod_divide; [lia|]. exists (26631 + 7 * Z.of_nat (length (r_calls R))). lia.
  - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia | reflexivity].
Qed.

Lemma rec_slot_entry : forall R, rec_slot R = rec_entry G_REC REC_SC R.
Proof. reflexivity. Qed.

Lemma rec_rep_calls_le : forall segs gr sc L A mem R O, rec_rep segs gr sc L A mem R O ->
  (length (r_calls R) <= 16)%nat.
Proof. intros segs gr sc L A mem R O (Q & (_ & (C1 & _) & _) & _). exact C1. Qed.

Lemma rec_record_calls : forall R fn As, (length (r_calls (rec_record R fn As)) <= 16)%nat ->
  (length (r_calls R) <= 16)%nat.
Proof.
  intros R fn As H. unfold rec_record in H. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | exact H].
Qed.

Lemma rw_out : forall segs W m m' a cs, rw_cells segs m a cs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0 <= a + i < 2 ^ 64 /\ outside W (a + i)) -> rw_cells segs m' a cs.
Proof.
  intros segs W m m' a cs H MU HO. apply (rw_cells_transfer segs m); [exact H|]. intros i Hi.
  destruct (HO i Hi) as [R O]. split; [exact (munch_mbyte segs W m m' _ MU R O)|].
  exact (proj1 (munch_writable segs W m m' _ MU R O)).
Qed.

Lemma f18_out : forall W m m', f18_words rsegs m -> munch W m m' ->
  (forall i, 0 <= i < 8 -> outside W (snprintf_c.GOT_GUARD + i) /\ outside W (snprintf_c.GUARD + i)) ->
  f18_words rsegs m'.
Proof.
  intros W m m' [F1 (g & F2)] MU HO. split; [|exists g].
  - apply (rw_out rsegs W m m' _ _ F1 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GOT_GUARD; lia | apply (HO i ltac:(lia))].
  - apply (rw_out rsegs W m m' _ _ F2 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GUARD; lia | apply (HO i ltac:(lia))].
Qed.

Lemma ro_out : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 20 -> ro_addr rsegs (Z_to_bv 64 a) = true -> outside W a) -> ro_agree rsegs m'.
Proof.
  intros W m m' RA MU HO x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  assert (Lx : bv_unsigned x < 2 ^ 20).
  { destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
    rewrite <- (Z_to_bv_bv_unsigned x), ro_addr_hi in Hx by lia. discriminate. }
  assert (E : m' x = m x).
  { apply MU. apply HO; [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hx. }
  unfold mrd. rewrite E. exact (RA x Hx).
Qed.

Lemma count_disj : forall (l : list (Z * Z)) x, pairwise ranges_disjoint l -> 0 < snd x ->
  (count_occ pair_dec l x <= 1)%nat.
Proof.
  induction l as [|y l IH]; intros x HP Hx; cbn [count_occ]; [lia|].
  destruct HP as [H1 H2]. destruct (pair_dec y x) as [E|E].
  - subst y. assert (C0 : count_occ pair_dec l x = 0%nat).
    { destruct (count_occ pair_dec l x) eqn:C; [reflexivity|]. exfalso.
      assert (Hin : In x l) by (apply (count_occ_In pair_dec); lia).
      pose proof (H1 x Hin) as D. unfold ranges_disjoint in D. lia. }
    lia.
  - exact (IH x H2 Hx).
Qed.

Lemma perm_not_both : forall (bl bl' P : list (Z * Z)) pn, Permutation bl (bl' ++ P) ->
  pairwise ranges_disjoint bl -> 0 < snd pn -> In pn bl' -> In pn P -> False.
Proof.
  intros bl bl' P pn HP HD Hs H1 H2.
  pose proof (count_disj bl pn HD Hs) as C. rewrite (proj1 (Permutation_count_occ pair_dec _ _) HP), count_occ_app in C.
  apply (count_occ_In pair_dec) in H1. apply (count_occ_In pair_dec) in H2. lia.
Qed.

Lemma win_out : forall (W : list (Z * Z)) S K,
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ rec_area a -> outside W a.
Proof.
  intros W S K HW a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction.
Qed.

Lemma user_blocks_in : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Fixpoint rs_rof (l : list (Z * Z * bool)) (a : Z) : bool :=
  match l with
  | [] => false
  | (b, z, w) :: l' => if (b <=? a) && (a + 1 <=? b + z) then negb w else rs_rof l' a
  end.

Lemma rs_ro_addr_rof : forall segs a,
  ro_addr segs a = rs_rof (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs) (bv_unsigned a).
Proof.
  intros segs a. unfold ro_addr. generalize (bv_unsigned a) as z.
  induction segs as [|sg segs IH]; intros z; [reflexivity|].
  cbn [find_segment map rs_rof]. destruct (_ && _); [reflexivity | apply IH].
Qed.

Lemma rs_rsegs_proj : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs =
  [(65536, 12288, false); (77824, 61440, false); (139264, 4096, true); (143360, 204800, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma rs_ro_rsegs : forall a, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true <-> 65536 <= a < 139264.
Proof.
  intros a Ha. rewrite rs_ro_addr_rof, rs_rsegs_proj, unsigned_lit by lia. cbn [rs_rof].
  repeat match goal with |- context [?u <=? ?v] => destruct (Z.leb_spec u v) end; cbn [andb negb];
    split; intros; first [reflexivity | discriminate | lia | exfalso; lia].
Qed.

Lemma rs_bytes_pad : forall segs m a bs (k : nat), bytes_at segs m a bs ->
  a + Z.of_nat (length bs) + Z.of_nat k <= 2 ^ 64 ->
  (forall j, (j < k)%nat -> mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) <> None) ->
  exists sl, length sl = k /\ bytes_at segs m a (bs ++ sl).
Proof.
  intros segs m a bs k H Hk Hr.
  exists (map (fun j => match mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) with
                        | Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  split; [rewrite length_map, length_seq; reflexivity|].
  apply bytes_at_app. split; [exact H|].
  pose proof (bytes_at_bound _ _ _ _ H) as HB.
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
  change (mrd segs m (wa (a + Z.of_nat (length bs) + Z.of_nat i)))
    with (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)).
  destruct (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)) eqn:E; [reflexivity | exfalso; exact (Hr i Hi E)].
Qed.

Lemma stk_norm : forall mem lo hi, 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs mem a) -> stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hlo Hhi HW. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present mem a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma rw_cells_norm_hi : forall m a cs, ro_agree rsegs m -> 2 ^ 20 <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs RA Ha [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m _ _ RA Hb)]|].
  apply (wr_at_norm rsegs m); [exact (mem_rel_normalize rsegs m RA) | exact Hw |].
  intros i Hi. destruct Hw as (H1 & H2 & _). unfold wa. apply ro_addr_hi. lia.
Qed.

Lemma rw_cells_norm_glob : forall m a cs, ro_agree rsegs m -> GLOB_LO <= a ->
  a + Z.of_nat (cells_size cs) <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs RA H1 H2 [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m _ _ RA Hb)]|].
  apply (wr_at_norm rsegs m); [exact (mem_rel_normalize rsegs m RA) | exact Hw |].
  intros i Hi. apply glob_ro_false. lia.
Qed.

Lemma slack_rebuild : forall m s x, bytes_at rsegs m s (x ++ [Z_to_bv 8 0]) -> 0 <= s ->
  s + Z.of_nat (length x) + 1 + 8 <= 2 ^ 64 ->
  (forall a, s + (Z.of_nat (length x) + 1) <= a < 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8) -> present m a) ->
  exists slack, bytes_at rsegs m s (x ++ Z_to_bv 8 0 :: slack) /\
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) <= 7 /\
    Z.of_nat (length slack) = (- (s + Z.of_nat (length x) + 1)) mod 8.
Proof.
  intros m s x H H0 H1 HP.
  destruct (slack_bytes rsegs m s (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) H
              ltac:(rewrite length_app; cbn [length]; lia) H0 ltac:(lia) HP) as (sl & HB & HL).
  exists sl. rewrite <- app_assoc in HB. cbn [app] in HB. split; [exact HB|].
  rewrite HL. split; [|split]; Z.div_mod_to_equations; lia.
Qed.

Lemma rw_cells_same_bytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

Lemma bytes_cell8 : forall m a v, GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le8 v)) (le8 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le8; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le8. reflexivity.
Qed.

Lemma cells_c8 : forall m a v, rw_cells rsegs m a [C8 v] -> bytes_at rsegs m a (le8 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Section Stub.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Definition sinv (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) (Rc : rstate) (Oc : list (Z * Z))
    (bc : sbound) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac).

Lemma sinv_init : forall K L A regs mem md R O b,
  call_pre_k B (aa_MR API) K L A regs mem md -> 0 <= K ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  sinv K (spZ regs) L A mem md O L A mem md R O b.
Proof.
  intros K L A regs mem md R O b PRE HK GR RA F18 RES.
  split; [exact (rjr_init B (aa_MR API) K rec_area (fun pn => In pn O) L A regs mem md PRE HK)|].
  split; [exact GR|]. split; [intros pn H; left; exact H|].
  split; [intros pn H; destruct (in_dec pair_dec pn O) as [H1|H1]; [right; exact H1 | left; split; assumption]|].
  split; [intros pn H1 H2; contradiction|]. split; [exact RA|]. split; [exact F18|].
  rewrite sb_shift_refl. exact RES.
Qed.

Lemma rjr_blk_out : forall K S O L A mem md Lc Ac mc mdc W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> 0 <= q + i < 2 ^ 64 /\ outside W (q + i).
Proof using SEGS AX.
  intros K S O L A mem md Lc Ac mc mdc W RJ HW q k i Hin Hi.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & H4 & H5 & _).
  split; [lia|]. apply (win_out W S K HW); [lia | lia |].
  intros Hr. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
  apply (ax_blocks_img AX Lc Ac mc mdc p k' i HM Hp Hi). apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
Qed.

Lemma rjr_win : forall K S O L A mem md Lc Ac mc mdc m' W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac m' mdc.
Proof using SEGS AX GOWN.
  intros K S O L A mem md Lc Ac mc mdc m' W RJ MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _).
  pose proof (rjr_blk_out K S O L A mem md Lc Ac mc mdc W RJ HW) as BO.
  apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
    [rewrite SEGS; exact WM | | | | |].
  - intros a Ra Hn _. exact (HW a Ra Hn).
  - intros a Ra Hn Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho) as Hlo.
    destruct (HW a Ra Hn) as [H|H]; [lia|].
    exact (GOWN Lc Ac mc mdc a HM (glob_in a (rec_area_glob a H)) Ho).
  - intros a Ha. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a ltac:(lia) H) as [H'|H'];
      [lia | apply rec_area_glob in H'; unfold GLOB_LO, GLOB_N in H'; lia].
  - intros p n i Hin Hg Hi.
    pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hin Hg) as Hc.
    rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL).
    apply (BO (ptr_addr Lc p) n i); [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi].
  - intros p n i Hc Hi. destruct (mr_blocks B _ LAWS Lc Ac mc mdc p n i HM Hc Hi) as (Hp & _).
    destruct (BO (ptr_addr Lc p) n i) as [Rr Oo]; [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi|].
    exact (munch_present W mc m' _ MU Rr Oo Hp).
Qed.

Lemma sinv_munch_core : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc',
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  g_rec_rep rsegs Lc Ac m' Rc' Oc ->
  sinv K S L A mem md O Lc Ac m' mdc Rc' Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc' SI MU WM HW GR'.
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof (win_out W S K HW) as OUT.
  split; [exact (rjr_win K S O L A mem md Lc Ac mc mdc m' W RJ MU WM HW)|].
  split; [exact GR'|]. split; [exact ON|]. split; [exact B1|]. split; [exact B2|].
  split.
  { apply (ro_out W mc m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    intros Hr. rewrite glob_ro_false in Hro by exact (rec_area_glob a Hr). discriminate. }
  split; [|exact RS].
  apply (f18_out W mc m' F18 MU). intros i Hi.
  split; (apply OUT; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma sinv_kept : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc -> munch W mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall p k i, In (p, k) Oc -> 0 <= i < k -> mbyte rsegs m' (p + i) = mbyte rsegs mc (p + i).
Proof using SEGS AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW p k i Hin Hi.
  pose proof SI as (RJ & GR & _).
  destruct (rjr_blk_out K S O L A mem md Lc Ac mc mdc W RJ HW p k i (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) Hi)
    as [Rr Oo].
  exact (munch_mbyte rsegs W mc m' _ MU Rr Oo).
Qed.

Lemma sinv_stack : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S) ->
  sinv K S L A mem md O Lc Ac m' mdc Rc Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU WM HW.
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a)
    by (intros a Ra Hn; left; exact (HW a Ra Hn)).
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  apply (sinv_munch_core K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc SI MU WM HW').
  unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m' Rc Oc GR).
  - intros a Ha. apply (munch_mbyte rsegs W mc m'); [exact MU | unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
    destruct (outside_dec W a) as [H|H]; [exact H|].
    pose proof (HW a ltac:(unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia) H).
    unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha. lia.
  - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
  - exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW').
Qed.

Lemma sinv_state : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W h,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ G_REC + OFF_STATE <= a < G_REC + OFF_STATE + 8) ->
  0 <= h < 2 ^ 64 -> bytes_at rsegs m' (G_REC + OFF_STATE) (le8 (Z_to_bv 64 h)) ->
  sinv K S L A mem md O Lc Ac m' mdc (set_state Rc h) Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W h SI MU WM HW Hh BS.
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a).
  { intros a Ra Hn. destruct (HW a Ra Hn) as [H|H]; [left; exact H|].
    right. unfold rec_area, G_REC, OFF_STATE, REC_SIZE in *. lia. }
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  apply (sinv_munch_core K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W _ SI MU WM HW').
  unfold g_rec_rep in *. apply (rec_rep_set_state rsegs G_REC REC_SC Lc Ac mc m' Rc Oc h GR Hh BS).
  - intros a Ha Hn. apply (munch_mbyte rsegs W mc m'); [exact MU | unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
    destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a ltac:(unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia) H) as [H'|H'];
      [unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia | exact (Hn H')].
  - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
  - exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW').
Qed.

Lemma sinv_record_post : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c fn
    L1 A1 regs1 m1 md1 O1 (D : list (Z * Z)),
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_rec B (aa_MR API) Kc Lc Ac regs_c mc mdc rec_area (fun a => In a (map fst Oc)) L1 A1 regs1 m1 md1 ->
  g_rec_rep rsegs L1 A1 m1 (rec_record Rc fn []) O1 ->
  (forall pn, In pn O1 -> In pn Oc) ->
  (forall pn, In pn D <-> In pn Oc /\ ~ In pn O1) ->
  Permutation (blocks Lc Ac) (blocks L1 A1 ++ D) ->
  others_kept rsegs Lc Ac mc L1 A1 m1 Oc ->
  (forall pn, In pn (blocks L1 A1) -> (In pn (blocks Lc Ac) /\ ~ In pn Oc) \/ In pn O1) ->
  ro_agree rsegs m1 -> f18_words rsegs m1 ->
  (st_init_done Ac = true -> st_init_done A1 = true) ->
  (length (st_regions Ac) <= length (st_regions A1))%nat ->
  (st_init_done Ac = false -> L1 = Lc /\ A1 = Ac /\ (forall lo, spZ regs_c <= lo ->
     auxv_pre B (ly_sec Lc) lo mc -> auxv_pre B (ly_sec L1) lo m1)) ->
  sb_le (sb_shift (sb_shift bc A Ac) Ac A1) (rfree_b (sb_shift bc A Ac) D) ->
  res_ok_slots A1 (sb_shift (sb_shift bc A Ac) Ac A1) ->
  sinv K S L A mem md O L1 A1 m1 md1 (rec_record Rc fn []) O1 bc /\ sb_le (sb_shift bc A A1) (sb_shift bc A Ac).
Proof using SEGS AX ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c fn L1 A1 regs1 m1 md1 O1 D
    SI HLO HHI POST GR1 OSUB DIFF PERM OK1 BL1 RA1 F181 INIT1 RGN1 NI SBLE RES1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAX).
  assert (DO : forall pn, In pn D -> In pn Oc) by (intros pn H; exact (proj1 (proj1 (DIFF pn) H))).
  assert (OB : forall pn, In pn Oc -> In pn (blocks Lc Ac)) by (intros pn H; exact (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR H)).
  assert (RJ1 : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 m1 md1).
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c rec_area
             (fun a => In a (map fst Oc)) L1 A1 regs1 m1 md1 RJ POST HLO HHI).
    - intros a Ha _. split; [exact Ha|]. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
    - intros p n Hp Hg Hn Hx. apply in_map_iff in Hx as ([a k'] & Ea & Hq). cbn [fst] in Ea. subst a.
      pose proof (OB _ Hq) as Hb. pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn [snd] in Hk'.
      pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hp Hg) as Hc.
      pose proof (user_blocks_in Lc Ac p n Hc) as Hbn. rewrite (ptr_addr_stable A L Lc p n HWA Hp HL) in Hbn.
      pose proof (blocks_same_addr B _ LAWS Lc Ac mc mdc (ptr_addr L p) n k' HM Hbn Hb Hn Hk') as <-.
      destruct (ON _ Hq) as [X|X]; [exact (Hg X) | exact (X (user_blocks_in L A p n Hp))].
    - intros p n Hp Hc Hn1.
      pose proof (ptr_addr_stable A L Lc p n HWA Hp HL) as EA.
      destruct (in_dec pair_dec (ptr_addr L p, n) Oc) as [H|H].
      + destruct (ON _ H) as [X|X]; [exact X|]. exfalso. exact (X (user_blocks_in L A p n Hp)).
      + exfalso. apply Hn1. rewrite <- EA in H. exact (proj1 (OK1 p n Hc H)).
    - exact RGN1.
    - intros Hf. destruct (st_init_done Ac) eqn:EI.
      + rewrite (INIT1 eq_refl) in Hf. discriminate.
      + destruct (NI eq_refl) as (_ & _ & HX). exact (HX S HHI (HAX eq_refl)). }
  rewrite sb_shift_trans in SBLE, RES1.
  split.
  - split; [exact RJ1|]. split; [exact GR1|].
    split; [intros pn H; exact (ON pn (OSUB pn H))|].
    split.
    { intros pn H. destruct (BL1 pn H) as [(Hc & Hn)|H']; [|right; exact H'].
      destruct (B1 pn Hc) as [X|X]; [left; exact X | contradiction]. }
    split.
    { intros pn H1 H2. destruct (in_dec pair_dec pn (blocks Lc Ac)) as [Hc|Hc]; [|exact (B2 pn H1 Hc)].
      assert (HD : In pn D).
      { pose proof (Permutation_in _ PERM Hc) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
      destruct (ON pn (DO pn HD)) as [X|X]; [exact X | contradiction]. }
    split; [exact RA1|]. split; [exact F181 | exact RES1].
  - eapply sb_le_trans; [exact SBLE|]. unfold rfree_b. apply rfree_b_le. apply Forall_forall. intros pn Hpn.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR (DO pn Hpn)). lia.
Qed.

Lemma sinv_arg : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k,
  sinv K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc Ec L' A' regs' m' md' ->
  (forall a, Ec a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
     p <= a < p + k) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinv K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k
    SI H6 HLO HHI POST HEc Hp0 FB (b1 & b2 & EB' & EB) UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HN : (length (r_calls Rp) <= 16)%nat)
    by exact (rec_record_calls Rp fn As (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds Rp HN) as (ER1 & ER2 & _).
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (Hk : 0 < k) by lia.
  assert (PIN : In (p, k) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, k)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, k) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, k) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, k) pn Hpn). }
  assert (APT : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> in_img B a) -> iv_apart p k lo n).
  { intros lo n Hn HI. unfold iv_apart. destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (lo + n) p) as [H'|H']; [right; exact H'|]. exfalso.
    apply (FB3 (Z.max p lo - p)); [lia|]. replace (p + (Z.max p lo - p)) with (Z.max p lo) by lia. apply HI. lia. }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c Ec (fun _ => False)
             L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. destruct (HEc a Ha) as [H|[H|H]].
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hi & _)]; [lia|].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (NQ : ~ In p (map fst Oc)).
  { intros Hq. apply in_map_iff in Hq as ([q k'] & Eq & Hq). cbn in Eq. subst q.
    pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn in Hk'.
    pose proof (blocks_same_addr B _ LAWS L' A' m' md' p k k' PM PIN (CUR _ Hb) Hk Hk') as <-.
    exact (NOTC Hb). }
  assert (GR' : g_rec_rep rsegs L' A' m' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L' A' m' Rp fn As Oc x p k GR H6 BN BS).
    - intros a Ha N1 N2.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ Ec a).
      { intros HE. destruct (HEc a HE) as [H|[H|H]]; [contradiction | contradiction |].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
      exact (proj1 (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                       NS NE)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb.
      split; [exact (CUR pn Hb)|]. intros i Hi. destruct pn as [q n]. cbn [fst snd] in *.
      exact (BK q n i Hb (fun H => H) Hi).
    - exact NQ.
    - exact Hp0.
    - exact PIN.
    - exact Hno.
    - exact Hlx.
    - exact Hsz.
    - exact BX.
    - apply APT; [unfold REC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - apply APT; [unfold SC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia. }
  split; [exact RJ'|]. split; [exact GR'|].
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[<-|[]]]; [exact (ON pn H)|].
    destruct (in_dec pair_dec (p, k) O) as [H|H]; [left; exact H | right; intros Hb].
    destruct (in_dec pair_dec (p, k) (blocks Lc Ac)) as [Hc|Hc]; [exact (NOTC Hc) | exact (H (B2 _ Hb Hc))]. }
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X].
    - subst pn. right. apply in_or_app. right. left. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p k EB' EB).
  exact RS'.
Qed.

Lemma sinv_ret : forall K L A regs mem md O L' A' regs' m' md' R' O' b,
  call_pre_k B (aa_MR API) K L A regs mem md ->
  sinv K (spZ regs) L A mem md O L' A' m' md' R' O' b ->
  regs_preserved regs regs' ->
  call_post_rec B (aa_MR API) K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' m' md' /\
  g_rec_rep rsegs L' A' m' R' O' /\ owns_new L A O O' /\
  (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
  others_kept rsegs L A mem L' A' m' O /\ ro_agree rsegs m' /\ f18_words rsegs m' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\ res_ok_slots A' (sb_shift b A A').
Proof using SEGS CTX.
  intros K L A regs mem md O L' A' regs' m' md' R' O' b PRE SI RP.
  pose proof SI as (RJ & GR & ON & B1 & _ & RA & F18 & RS).
  split.
  { apply (rjr_final B (aa_MR API) CTX K rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L' A' regs' m' md' PRE RJ RP).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [exact GR|]. split; [exact ON|]. split; [exact B1|].
  split.
  { pose proof (rjr_others_kept B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' m' md' O
                  RJ (fun pn H => H)) as OK.
    rewrite SEGS in OK. exact OK. }
  split; [exact RA|]. split; [exact F18|].
  split; [pose proof RJ as (_ & _ & _ & _ & _ & HLen & _); exact HLen | exact RS].
Qed.

Hypothesis REC : record_contract B API.

Lemma sinv_record : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c fn (P : config -> Prop),
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - RECORD_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) -> getr regs_c 10 = Z_to_bv 64 fn -> 0 <= fn < REC_FN_COUNT ->
  (forall L1 A1 regs1 m1 md1 O1,
     sinv K S L A mem md O L1 A1 m1 md1 (rec_record Rc fn []) O1 bc ->
     sb_le (sb_shift bc A A1) (sb_shift bc A Ac) ->
     regs_preserved regs_c regs1 -> getr regs1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rc) ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m1 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m1 a)) ->
     SR rsegs (mkCfg (mkst regs1 (getr regs_c 1) m1 (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 RECORD) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX ERRNO_LOW REC.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c fn P SI Hra Hal Hlo Hhi Htp H10 Hfn KONT.
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS).
  pose proof REC as RC. unfold record_contract in RC. rewrite SEGS in RC.
  eapply SR_bind.
  { apply (RC Lc Ac regs_c mc mdc fn Rc Oc (sb_shift bc A Ac)); [ | exact H10 | exact Hfn | exact GR | exact RA | exact F18
      | exact RS].
    apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc RECORD_K regs_c RJ Hra Hal);
      [unfold RECORD_K, ALLOC_STACK; lia | exact Hlo | exact Hhi | exact Htp]. }
  intros c1 (L1 & A1 & regs1 & m1 & md1 & O1 & D & -> & POST & R10 & GR1 & OSUB & DIFF & PERM & OK1 & BL1 & RA1 & F181
    & INIT1 & RGN1 & NI & SBLE & RES1).
  destruct (sinv_record_post K S L A mem md O Lc Ac mc mdc Rc Oc bc RECORD_K regs_c fn L1 A1 regs1 m1 md1 O1 D SI
              Hlo Hhi POST GR1 OSUB DIFF PERM OK1 BL1 RA1 F181 INIT1 RGN1 NI SBLE RES1) as [SI1 BLE1].
  pose proof POST as (PM & _ & _ & _ & _ & PR & _ & PF & _). rewrite SEGS in PF.
  assert (FK : forall a, spZ regs_c <= a < S ->
            mbyte rsegs m1 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m1 a)).
  { intros a Ha. pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof RJ as (HM & _).
    destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
    unfold RECORD_K, ALLOC_STACK in Hlo.
    apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L1 A1 m1 md1 a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
  exact (KONT L1 A1 regs1 m1 md1 O1 SI1 BLE1 PR R10 FK).
Qed.

Hypothesis ARGS : arg_s_contract B API.

Lemma sarg_facts : forall L A sp mem s v, arg_s_src B L A sp mem s v ->
  no0 (sarg v) /\ Z.of_nat (length (sarg v)) <= LMAX.
Proof.
  intros L A sp mem s [x|] SRC; cbn [arg_s_src] in SRC.
  - destruct SRC as (_ & NO & LX & _). split; [exact NO | exact LX].
  - split; [exact null_no0 | vm_compute; congruence].
Qed.

Lemma sinv_arg_sn : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc regs_c s v (P : config -> Prop),
  sinv K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc -> (length As < 6)%nat ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ARG_S_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 11 = Z_to_bv 64 s ->
  arg_s_src B Lc Ac (spZ regs_c) mc s v ->
  room_ag (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
  (forall L2 A2 regs2 m2 md2 p,
     sinv K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn (As ++ [sarg v]))
       (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) bc ->
     sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1) ->
     st_init_done A2 = true -> regs_preserved regs_c regs2 ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)) ->
     SR rsegs (mkCfg (mkst regs2 (getr regs_c 1) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_S) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW ARGS.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc regs_c s v P SI H6 Hra Hal Hlo Hhi Htp H10 H11 SRC ROOM KONT.
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  assert (HN : (length (r_calls Rp) <= 16)%nat)
    by exact (rec_record_calls Rp fn As (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds Rp HN) as (ER1 & ER2 & ER3).
  destruct (rec_entry_at rsegs Lc Ac mc Rp fn As Oc GR) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA0 & _).
  destruct (sarg_facts Lc Ac (spZ regs_c) mc s v SRC) as (NO & LX).
  set (e := rec_entry G_REC REC_SC Rp) in *.
  pose proof ARGS as ASC. unfold arg_s_contract in ASC. rewrite SEGS in ASC.
  eapply SR_bind.
  { apply (ASC Lc Ac regs_c mc mdc e s (Z.of_nat (length As)) v (sb_shift bc A Ac)).
    - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc ARG_S_K regs_c RJ Hra Hal);
        [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | exact Hlo | exact Hhi | exact Htp].
    - exact H10.
    - exact H11.
    - exact ER3.
    - exact ER1.
    - exact ER2.
    - apply glob_wr_at; unfold GLOB_LO, GLOB_N, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *; lia.
    - exact NA0.
    - lia.
    - exact SRC.
    - exact F18.
    - exact RS.
    - exact ROOM.
    - exact RA. }
  intros c2 (L2 & A2 & regs2 & m2 & md2 & -> & BK & UB & RA2 & GK & F182 & RGN &
    [(M6 & _) | (_ & p & POST & Hp0 & PAL & FB & BLK & NA2 & AS2 & BP & INI & RES2)]); [lia|].
  rewrite SEGS in NA2, AS2, BP, RA2, F182.
  pose proof POST as (PM & _ & _ & _ & _ & PR & _ & PF & _). rewrite SEGS in PF.
  assert (FK : forall a, spZ regs_c <= a < S ->
            mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)).
  { intros a Ha. pose proof (aa_laws API) as LAWS. pose proof RJ as (HM & _).
    pose proof FB as (FB1 & FB2 & _).
    unfold ARG_S_K, XMALLOC_K, ALLOC_STACK in Hlo.
    apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - cbv beta. unfold CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *. lia. }
  pose proof BLK as (b1 & b2 & EB' & EB).
  assert (SI2 : sinv K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn (As ++ [sarg v]))
                  (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) bc).
  { apply (sinv_arg K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc ARG_S_K regs_c _ L2 A2 regs2 m2 md2 (sarg v) p
             (Z.of_nat (length (sarg v)) + 1) SI H6 Hlo Hhi POST).
    - intros a Ha. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - exact Hp0.
    - exact FB.
    - exact BLK.
    - exact UB.
    - exact BK.
    - exact RGN.
    - exact NA2.
    - exact AS2.
    - exact BP.
    - exact NO.
    - exact LX.
    - lia.
    - exact INI.
    - exact RES2.
    - exact RA2.
    - exact F182. }
  rewrite SEGS. apply (KONT L2 A2 regs2 m2 md2 p SI2); [| exact INI | exact PR | exact FK].
  rewrite <- (sb_shift_trans bc A Ac A2). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 b1 b2 p _ EB' EB).
  reflexivity.
Qed.

Lemma sinv_arg_s : forall K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c s v (P : config -> Prop),
  sinv K S L A mem md O Lc Ac mc mdc (rec_record Rp fn []) Oc bc ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ARG_S_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 11 = Z_to_bv 64 s ->
  arg_s_src B Lc Ac (spZ regs_c) mc s v ->
  room_ag (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
  (forall L2 A2 regs2 m2 md2 p,
     sinv K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn [sarg v]) (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) bc ->
     sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1) ->
     st_init_done A2 = true -> regs_preserved regs_c regs2 ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)) ->
     SR rsegs (mkCfg (mkst regs2 (getr regs_c 1) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_S) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW ARGS.
  intros K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c s v P SI Hra Hal Hlo Hhi Htp H10 H11 SRC ROOM KONT.
  exact (sinv_arg_sn K S L A mem md O Lc Ac mc mdc Rp fn [] Oc bc regs_c s v P SI ltac:(cbn [length]; lia)
           Hra Hal Hlo Hhi Htp H10 H11 SRC ROOM KONT).
Qed.

Hypothesis SLACK : block_slack_present B API.

Lemma sinv_arg_src : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p v sp',
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem -> S - K <= sp' - ARG_S_K -> sp' <= S ->
  str_arg B L A O S K mem p v ->
  arg_s_src B Lc Ac sp' mc p v.
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p v sp' SI RA HS1 HS2 H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct v as [x|]; cbn [arg_s_src str_arg] in H |- *; [|exact H].
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS |- *.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  str_home B Lc Ac sp' p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | left; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      right. left. exists q, k. split; [exact QC | lia].
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi.
        assert (RO : ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
        { destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
          pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
          apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2 | right; right; split; [exact H1 | split; [exact H2 | exact H3]]]]. }
  destruct CASES as (TX & PADP & HOMEc).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  split; [exact Hp0|]. split; [exact N0|]. split; [exact LX|]. exists sl.
  split; [exact BS'|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; lia|].
  split; [rewrite length_app; cbn [length]; rewrite SL; unfold ARG_S_K, XMALLOC_K, ALLOC_STACK in *;
          destruct DJ as [D|D]; [left; lia | right; lia]|].
  exact HOMEc.
Qed.

End Stub.
