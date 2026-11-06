(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): the data the two
   SET-UP LOOPS of its walk share, for lib/A/Prog/LLVMFuzzerTestOneInputGl.v (the 64-turn g_names loop, +0x32c) and
   lib/A/Prog/LLVMFuzzerTestOneInputOl.v (the 4-turn odd loop, +0x3cc .. +0x47c). The cut interface is
   lib/A/Prog/LLVMFuzzerTestOneInputDefs.v.

   1. The interface table `lf_tab` by index: entry e of the table is the e-th turn of the g_names loop with
      k mod 16 <> 15 (+0x34c `beq a0, a1` skips the append), i.e. k = e + e / 15; entries 60..63 are
      odd[1..4] with the indices 101..104. `lf_tab_at` grows by one entry per appending turn.
   2. snprintf's text at the g_names site (0x82b14, f = .str 0x20fa0 "nl%d", n = 8, the argument k): the
      format family FF_link (lib/A/Rt/LinkSnpDef.v) carries `pf_text` of PfFacts.v, and `pf_dec k` is the
      interface's `lf_dec2 k` for 0 <= k < 100, so the text is `lf_gname_z k` and the bytes the post places
      at g_names + 8 k are `sn_bytes 7 (lf_gname_z k) = lf_gname_z k ++ [0]`.
   3. The shadow of the two image objects the loops read and write, at every allocator state, as
      lib/A/Prog/LinkWalkZsh.v gives g_nl's: g_names (the snprintf destination) and odd (.data.rel.ro).
   4. The denotation lemmas that let the walk PIN a register to a fresh atom: the two table addresses
      g_nl + NK_IF_NAME + 8 n_if (+0x35c) and g_nl + NK_IF_INDEX + 4 n_if (+0x390) are computed from the
      loaded n_if, so they are not of the engine's `SOff atom + constant` form; the walk adds an atom whose
      value is the address and rewrites the register's symbolic value to it (LinkWalkPi.v st_ok_pi_set_reg).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP0l YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. The interface table by index
   ========================================================================== *)

(* the turn of the g_names loop that writes entry e of the table *)
Definition lf_k_of (e : nat) : nat := (e + e / 15)%nat.

Lemma lf_tab_len64 : length lf_tab = 64%nat.
Proof. exact lf_tab_len. Qed.

(* entries 0 .. 59: the name "nl<k>" at g_names + 8 k and the index k + 2, k = e + e / 15 *)
Lemma lf_tab_nth_g : forall e, (e < 60)%nat ->
  nth_error lf_tab e = Some (lf_gname (Z.of_nat (lf_k_of e)), Z.of_nat (lf_k_of e) + 2).
Proof.
  intros e He.
  do 60 (destruct e as [|e]; [vm_compute; reflexivity|]).
  exfalso. cbn in He. lia.
Qed.

(* entries 60 .. 63: odd[1..4] with the indices 101 .. 104 *)
Lemma lf_tab_nth_o : forall e, (60 <= e < 64)%nat ->
  nth_error lf_tab e = Some (nth (e - 59) lf_odd_strs [], 101 + Z.of_nat (e - 60)).
Proof.
  intros e He.
  do 64 (destruct e as [|e]; [first [vm_compute; reflexivity | exfalso; cbn in He; lia]|]).
  exfalso. cbn in He. lia.
Qed.

Lemma lf_tab_at_len : forall n, (n <= 64)%nat -> length (lf_tab_at (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold lf_tab_at. rewrite Nat2Z.id, length_firstn, lf_tab_len64. lia.
Qed.

(* one more entry per appending turn *)
Lemma lf_firstn_S : forall {A : Type} (l : list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [|x l IH]; intros n d Hn; [cbn in Hn; lia|].
  destruct n as [|n]; cbn [firstn nth app]; [reflexivity|].
  cbn [length] in Hn. f_equal. apply IH. lia.
Qed.

Lemma lf_tab_at_succ : forall n d, (n < 64)%nat ->
  lf_tab_at (Z.of_nat n + 1) = lf_tab_at (Z.of_nat n) ++ [nth n lf_tab d].
Proof.
  intros n d Hn. unfold lf_tab_at.
  replace (Z.to_nat (Z.of_nat n + 1)) with (S n) by lia. rewrite Nat2Z.id.
  apply lf_firstn_S. rewrite lf_tab_len64. lia.
Qed.

(* the two counts the invariants use: j - j / 16 after j turns of the g_names loop, 60 + j in the odd loop *)
Lemma lf_cnt_step_keep : forall j, 0 <= j < 64 -> j mod 16 <> 15 ->
  (j + 1) - (j + 1) / 16 = (j - j / 16) + 1.
Proof.
  intros j Hj Hm.
  pose proof (Z.div_mod j 16 ltac:(lia)) as D. pose proof (Z.mod_pos_bound j 16 ltac:(lia)) as M.
  assert (E : (j + 1) / 16 = j / 16).
  { symmetry. apply (Z.div_unique (j + 1) 16 (j / 16) (j mod 16 + 1)); [left; lia | lia]. }
  lia.
Qed.

Lemma lf_cnt_step_skip : forall j, 0 <= j < 64 -> j mod 16 = 15 ->
  (j + 1) - (j + 1) / 16 = j - j / 16.
Proof.
  intros j Hj Hm.
  pose proof (Z.div_mod j 16 ltac:(lia)) as D.
  assert (E : (j + 1) / 16 = j / 16 + 1).
  { symmetry. apply (Z.div_unique (j + 1) 16 (j / 16 + 1) 0); [left; lia | lia]. }
  lia.
Qed.

Lemma lf_cnt_range : forall j, 0 <= j < 64 -> 0 <= j - j / 16 <= 60.
Proof.
  intros j Hj. pose proof (Z.div_mod j 16 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound j 16 ltac:(lia)) as M.
  pose proof (Z.div_pos j 16 ltac:(lia) ltac:(lia)) as P.
  pose proof (Z.div_le_mono j 63 16 ltac:(lia) ltac:(lia)) as Q.
  change (63 / 16) with 3 in Q. lia.
Qed.

Lemma lf_cnt_full : 64 - 64 / 16 = 60. Proof. reflexivity. Qed.

(* the turn that writes entry e is e + e / 15, and the count of that turn is e *)
Lemma lf_k_of_inv : forall e, (e < 60)%nat ->
  Z.of_nat (lf_k_of e) - Z.of_nat (lf_k_of e) / 16 = Z.of_nat e /\
  Z.of_nat (lf_k_of e) mod 16 <> 15 /\ (lf_k_of e < 64)%nat.
Proof.
  intros e He. unfold lf_k_of.
  do 60 (destruct e as [|e]; [vm_compute; repeat split; (lia || discriminate)|]).
  exfalso. cbn in He. lia.
Qed.

(* the inverse: at a turn j with j mod 16 <> 15 the entry the loop appends is entry j - j / 16 *)
Lemma lf_k_of_of : forall j, 0 <= j < 64 -> j mod 16 <> 15 ->
  lf_k_of (Z.to_nat (j - j / 16)) = Z.to_nat j.
Proof.
  intros j Hj Hm.
  assert (Hb : 0 <= j - j / 16 <= 60) by (apply lf_cnt_range; lia).
  remember (Z.to_nat j) as n eqn:Hn.
  assert (Hj' : j = Z.of_nat n) by lia. subst j.
  do 64 (destruct n as [|n]; [vm_compute in Hm |- *; first [reflexivity | exfalso; apply Hm; reflexivity]|]).
  exfalso. lia.
Qed.

(* ==========================================================================
   2. snprintf's text at the g_names site
   ========================================================================== *)

(* "nl%d" at .str 0x20fa0, as the walk reads it out of the read-only window *)
Definition LF_FMT : list Z := [110; 108; 37; 100].

Lemma lf_fmt_parse : pf_parse LF_FMT = Some [PLit 110; PLit 108; Pd].
Proof. vm_compute. reflexivity. Qed.

(* the decimal conversion of the printf core is the interface's lf_dec2 on the loop's range *)
Lemma lf_pf_dec_small : forall k, 0 <= k < 100 -> pf_dec k = lf_dec2 k.
Proof.
  intros k Hk. unfold pf_dec, lf_dec2.
  destruct (Z.ltb_spec k 0) as [Hneg|_]; [lia|].
  destruct (Z.ltb_spec k 10) as [Hlt|Hge].
  - cbn [pf_digits]. rewrite (proj2 (Z.ltb_lt k 10) Hlt). reflexivity.
  - cbn [pf_digits]. rewrite (proj2 (Z.ltb_ge k 10) Hge).
    assert (Hd : k / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
    cbn [pf_digits]. rewrite (proj2 (Z.ltb_lt (k / 10) 10) Hd). reflexivity.
Qed.

(* the text snprintf writes for the turn's argument k *)
Lemma lf_pf_text : forall k, 0 <= k < 100 ->
  pf_text [PLit 110; PLit 108; Pd] [AInt k] = Some (lf_gname_z k).
Proof.
  intros k Hk. cbn [pf_text option_map].
  rewrite app_nil_r, (lf_pf_dec_small k Hk). reflexivity.
Qed.

Lemma lf_gname_z_len : forall k, 0 <= k < 100 -> (length (lf_gname_z k) <= 4)%nat.
Proof.
  intros k Hk. unfold lf_gname_z, lf_dec2. destruct (k <? 10); cbn [length]; lia.
Qed.

Lemma lf_gname_len : forall k, 0 <= k < 100 -> (length (lf_gname k) <= 4)%nat.
Proof. intros k Hk. unfold lf_gname. rewrite length_map. apply lf_gname_z_len. exact Hk. Qed.

(* the bytes the post places at the destination: the text and its NUL (n - 1 = 7 >= |T|) *)
Lemma lf_firstn_all : forall {A : Type} (l : list A) n, (length l <= n)%nat -> firstn n l = l.
Proof.
  intros A l. induction l as [|x l IH]; intros n Hn; [destruct n; reflexivity|].
  destruct n as [|n]; cbn [length] in Hn; [lia|]. cbn [firstn]. f_equal. apply IH. lia.
Qed.

Lemma lf_sn_bytes : forall k, 0 <= k < 100 ->
  sn_bytes 7 (lf_gname_z k) = lf_gname_z k ++ [0] /\
  sn_len 7 (lf_gname_z k) = Z.of_nat (length (lf_gname_z k)) + 1.
Proof.
  intros k Hk. pose proof (lf_gname_z_len k Hk) as Hl.
  assert (E : sn_bytes 7 (lf_gname_z k) = lf_gname_z k ++ [0]).
  { unfold sn_bytes. f_equal. apply lf_firstn_all. change (Z.to_nat 7) with 7%nat. lia. }
  split; [exact E|]. unfold sn_len. rewrite E, length_app. cbn [length]. lia.
Qed.

Lemma lf_sn_len_range : forall k, 0 <= k < 100 -> 1 <= sn_len 7 (lf_gname_z k) <= 5.
Proof.
  intros k Hk. destruct (lf_sn_bytes k Hk) as (_ & E). rewrite E.
  pose proof (lf_gname_z_len k Hk). lia.
Qed.

(* ==========================================================================
   3. The shadow of g_names and of odd, at every allocator state
   ========================================================================== *)

Section z. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma lf_gnames_row : exists r, find_row LA_G_NAMES 512 = Some r /\
  shadow_addr (fst r) <= shadow_addr LA_G_NAMES / 8 * 8 /\
  (forall ly, all_from (const_byte_b ly) (shadow_addr (fst r) + snd r / 8)
     (Z.to_nat (hull_end LA_G_NAMES 512 - (shadow_addr (fst r) + snd r / 8))) = true).
Proof.
  let v := eval vm_compute in (find_row LA_G_NAMES 512) in
  lazymatch v with Some ?r =>
    exists r; split; [vm_compute; reflexivity|]; split; [vm_compute; congruence|];
    intros ly; vm_compute; reflexivity
  end.
Qed.

Lemma lf_odd_row : exists r, find_row LA_ODD 48 = Some r /\
  shadow_addr (fst r) <= shadow_addr LA_ODD / 8 * 8 /\
  (forall ly, all_from (const_byte_b ly) (shadow_addr (fst r) + snd r / 8)
     (Z.to_nat (hull_end LA_ODD 48 - (shadow_addr (fst r) + snd r / 8))) = true).
Proof.
  let v := eval vm_compute in (find_row LA_ODD 48) in
  lazymatch v with Some ?r =>
    exists r; split; [vm_compute; reflexivity|]; split; [vm_compute; congruence|];
    intros ly; vm_compute; reflexivity
  end.
Qed.

Lemma lf_zsh_gnames_rd : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF LA_G_NAMES 512 /\ shadow_hull_vis rd LA_G_NAMES 512.
Proof.
  intros ly S rd HM. destruct lf_gnames_row as (r & Hf & Hs & Hc).
  split; [exact (zsh_range_find B TB ly S rd _ _ r HM Hf)|].
  apply (zsh_hull_find B TB ly S rd _ _ r HM Hf); [lia | exact Hs | exact (Hc ly)].
Qed.

Lemma lf_zsh_odd_rd : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF LA_ODD 48 /\ shadow_hull_vis rd LA_ODD 48.
Proof.
  intros ly S rd HM. destruct lf_odd_row as (r & Hf & Hs & Hc).
  split; [exact (zsh_range_find B TB ly S rd _ _ r HM Hf)|].
  apply (zsh_hull_find B TB ly S rd _ _ r HM Hf); [lia | exact Hs | exact (Hc ly)].
Qed.

(* a sub-range of an addressable range is addressable, and its shadow hull is inside the hull *)
Lemma lf_ra_sub : forall (rd : reader) p n q m,
  range_addressable rd SHADOW_OFF p n -> p <= q -> q + m <= p + n ->
  range_addressable rd SHADOW_OFF q m.
Proof. intros rd p n q m H Hlo Hhi x Hx. apply H. lia. Qed.

Lemma lf_hull_sub : forall (rd : reader) p n q m,
  shadow_hull_vis rd p n -> 0 < m -> 0 < n -> p <= q -> q + m <= p + n ->
  shadow_hull_vis rd q m.
Proof.
  intros rd p n q m H Hm Hn Hlo Hhi s Hs. apply H.
  unfold shadow_addr in *.
  assert (Hq1 : (SHADOW_OFF + p / 8) / 8 * 8 <= (SHADOW_OFF + q / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono p q 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hq2 : (SHADOW_OFF + (q + m - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (p + n - 1) / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono (q + m - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.

End z.

(* The denotation of the two table addresses, as the walk pins them, is added once the symbolic value the
   engine produces at +0x35c and +0x390 is read off a run: `sv_denot E a = Z_to_bv 64 (base + 8 * nif)` with a
   the engine's own expression. See LLVMFuzzerTestOneInputGl.v `lf_gl_pin_name` / `lf_gl_pin_index`. *)

(* ==========================================================================
   5. The machine state at a cut, in the shape the engine's entry lemma takes
   ========================================================================== *)

(* `lf_shape` pins six fields of the cut's machine state; that is exactly `mkst` at the running FP state. *)
Lemma lf_ms_shape : forall (fy : YK11.FPState) (segs : list Segment) pcv (ms : machine_state),
  ms_pc_val ms = pcv -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom segs -> ms_fregs ms = @YK11.fp_regs fy -> ms_fcsr ms = @YK11.fp_csr fy ->
  ms = @YK11.mkst fy (ms_regs ms) pcv (ms_mem ms) (seg_rom segs).
Proof.
  intros fy segs pcv ms H1 H2 H3 H4 H5 H6.
  destruct ms as [rg fr pc svc rsv fc mm rm]; cbn in *; subst. reflexivity.
Qed.
