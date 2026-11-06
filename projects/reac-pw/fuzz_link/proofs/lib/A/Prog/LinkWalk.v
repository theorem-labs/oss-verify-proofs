(* reac-pw/fuzz_link, image A: THE WALK KIT. What every image-A walk of one of link's own functions needs beside
   the contract shapes of lib/A/Prog/link_amem.v and the journal lifts of lib/A/Prog/link_ajkit.v.

   Section g is pcap's lib/A/W_journal.v Section g at LINK's listing: the two run instances `paj_run_x` /
   `paj_run_to_x` of W_journalG.v's SRr_run_pi_tok_AJX / SRr_run_to_pi_tok_AJX over LinkSyms.lsym, LinkList
   (link_listing), LinkPa (PAListing / PAImg) and LinkPaLib (whose GUIDE tactics paj_run_tok, paj_run_to_tok,
   psrr_branch_tok take them unchanged). pcap's own walks get exactly this from its W_journal.v (link-a/form/FORM.md
   (internal record, sha256 13aeff774164) section 6, open question 6: link's program tables are generated separately).

   Section j holds what a walk does with the run's result: the journal's index bump, the two kept clauses of
   link_amem.v (`akept`, `ashadow_kept`) for a run that writes only its own window and a set E of bytes below
   SHADOW_OFF (every image global of link's G is below it: kLowMemEnd = SHADOW_OFF = 0x7fff8000), and the whole
   `apost` of a leaf that reaches no allocator. Section s lifts the strcmp wrapper onto the journal, as
   link_ajkit.v's aj_gx_strncmp_at lifts strncmp.

   Section y is the byte algebra the Posts need: the A views give a function's result as `val_mem` facts at the
   image addresses, and link_spec.v states it over a byte LIST (`rdn bs off n`), so a walk needs to read a byte
   list off the memory (`abytes_of`), to say that reading n bytes of it at off gives a value whose bytes the walk
   knows (`rdn_of_vals`), and that a read outside the bytes the run wrote is the read it was before (`rdn_agree`).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   Section y: the byte algebra (no image, no segments of its own)
   ========================================================================== *)

Lemma lw_nth_error_skipn : forall (l : list byte) o k, nth_error (skipn o l) k = nth_error l (o + k).
Proof.
  intros l o. revert l. induction o as [|o IH]; intros l k; [reflexivity|].
  destruct l as [|b l]; cbn [skipn]; [destruct k; reflexivity|]. apply IH.
Qed.

Lemma lw_nth_error_firstn : forall (l : list byte) n k, (k < n)%nat -> nth_error (firstn n l) k = nth_error l k.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l k Hk; [lia|].
  destruct l as [|b l]; cbn [firstn]; [destruct k; reflexivity|].
  destruct k as [|k]; [reflexivity|]. cbn [nth_error]. apply IH. lia.
Qed.

Lemma lw_nth_error_map_seq : forall (f : nat -> byte) n s i, (i < n)%nat ->
  nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  induction n as [|n IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn [seq map nth_error].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S s) i ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma lw_list_ext : forall (l1 l2 : list byte),
  length l1 = length l2 -> (forall k, (k < length l1)%nat -> nth_error l1 k = nth_error l2 k) -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros l2 Hlen H; destruct l2 as [|b2 l2]; try (cbn in Hlen; lia); [reflexivity|].
  cbn in Hlen. pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as <-.
  f_equal. apply IH; [lia|]. intros k Hk. exact (H (S k) ltac:(cbn; lia)).
Qed.

(* the n bytes of bs from off, by index *)
Lemma lw_slice_nth : forall (bs : list byte) off n k,
  0 <= off -> (k < Z.to_nat n)%nat -> nth_error (slice bs off n) k = nth_error bs (Z.to_nat off + k).
Proof.
  intros bs off n k Hoff Hk. unfold slice.
  rewrite (lw_nth_error_firstn _ _ k Hk). apply lw_nth_error_skipn.
Qed.

Lemma lw_slice_length : forall (bs : list byte) off n,
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> length (slice bs off n) = Z.to_nat n.
Proof.
  intros bs off n Hoff Hn Hlen. unfold slice.
  rewrite length_firstn, length_skipn. lia.
Qed.

(* A read of n bytes is the read it was, when those bytes did not change. *)
Lemma rdn_agree : forall (bs bs' : list byte) off n,
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> off + n <= Z.of_nat (length bs') ->
  (forall k, (k < Z.to_nat n)%nat -> nth_error bs' (Z.to_nat off + k) = nth_error bs (Z.to_nat off + k)) ->
  rdn bs' off n = rdn bs off n.
Proof.
  intros bs bs' off n Hoff Hn Hl Hl' H. unfold rdn. f_equal.
  apply lw_list_ext.
  - rewrite !lw_slice_length by lia. reflexivity.
  - intros k Hk. rewrite lw_slice_length in Hk by lia.
    rewrite !lw_slice_nth by lia. exact (H k Hk).
Qed.

(* A read of n bytes whose bytes the walk knows, as le_byte of a value, is that value. *)
Lemma lw_bytes_of_vals : forall n (l : list byte) v,
  length l = n -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  (forall k, (k < n)%nat -> nth_error l k = Some (Z_to_bv 8 (le_byte v n k))) ->
  bytes_le_to_Z l = v.
Proof.
  induction n as [|n IH]; intros l v Hlen Hv H.
  - destruct l as [|b l]; [|cbn in Hlen; lia]. cbn in Hv. cbn. lia.
  - destruct l as [|b l]; [cbn in Hlen; lia|]. cbn in Hlen.
    assert (Hpow : 2 ^ (8 * Z.of_nat (S n)) = 256 * 2 ^ (8 * Z.of_nat n)).
    { replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
      rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Hpn : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
    pose proof (H 0%nat ltac:(lia)) as H0. cbn [nth_error] in H0. injection H0 as Hb0.
    assert (Hb : bv_unsigned b = v mod 256).
    { rewrite Hb0. unfold le_byte. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
      rewrite Z.mod_mod by lia. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat (S n)))) by lia. reflexivity. }
    rewrite bytes_le_to_Z_cons, Hb.
    rewrite (IH l (v / 256)).
    + pose proof (Z.div_mod v 256 ltac:(lia)). lia.
    + lia.
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    + intros k Hk. replace (nth_error l k) with (nth_error (b :: l) (S k)) by reflexivity.
      rewrite (H (S k) ltac:(lia)). f_equal. f_equal.
      unfold le_byte.
      rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat (S n)))) by lia.
      rewrite (Z.mod_small (v / 256) (2 ^ (8 * Z.of_nat n)))
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite !Z.shiftr_div_pow2 by lia.
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite <- Z.div_div by lia. reflexivity.
Qed.

Lemma rdn_of_vals : forall (bs : list byte) off n v,
  0 <= off -> off + Z.of_nat n <= Z.of_nat (length bs) ->
  0 <= v < 2 ^ (8 * Z.of_nat n) ->
  (forall k, (k < n)%nat -> nth_error bs (Z.to_nat off + k) = Some (Z_to_bv 8 (le_byte v n k))) ->
  rdn bs off (Z.of_nat n) = v.
Proof.
  intros bs off n v Hoff Hlen Hv H. unfold rdn.
  apply (lw_bytes_of_vals n); [rewrite lw_slice_length by lia; lia | exact Hv |].
  intros k Hk. rewrite lw_slice_nth by lia. exact (H k Hk).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument of every statement that depends on it, as in link_amem.v and
   link_ajkit.v (the only global sink_head instance of this closure is the plain build's, Reusable/YI5b.v). *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* ==========================================================================
   Section g: the run instances at LINK's listing (pcap's W_journal.v Section g)
   ========================================================================== *)
Section g.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* A walk writes `Let RUN := paj_run_x B LAWS G HG XO OUT.` and `Let RUNTO := paj_run_to_x B LAWS G HG XO OUT.`;
   LinkPaLib's tactics paj_run_tok / paj_run_to_tok / psrr_branch_tok take them unchanged. *)
Definition paj_run_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_pi_tok_AJX lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition paj_run_to_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_to_pi_tok_AJX lsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
End g.

(* The image instance is LINK's: its value table is LinkAddr.v's and its entries are LinkAddr.v's. A walk takes
   this as one hypothesis and reads off it the one or two atoms its own listing names (the auipc values A_HI j
   and the objects A_OBJ i of lib/A/Prog/LinkAddr.v, whose addresses link_aaddr.v names). The instance that
   lib/A/Prog/LinkPaCheck.v certifies against the image satisfies it by computation. *)
Section vals.
Context {L : ptable lsym} {PI : PAImg L}.
Record LinkVals : Prop := mkLinkVals {
  lv_text : pa_val A_TEXT = link_text;
  lv_obj : forall i, (i < link_nobj)%nat -> pa_val (A_OBJ i) = link_obj i;
  lv_hi : forall j, (j < link_nhi)%nat -> pa_val (A_HI j) = link_hi j;
  lv_sigma : forall s, pa_sigma s = link_sigma s
}.
End vals.

(* ==========================================================================
   Section j: from the end of a run to the contract's Post
   ========================================================================== *)
Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* Materialising the lazy vm backing keeps the descriptor table and the file system. *)
Lemma wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

(* A record is its own field update. *)
Lemma set_fs_self : forall S : astate, set_fs (st_fs S) S = S.
Proof. intros S. destruct S. reflexivity. Qed.

(* The journal's event index only grows. *)
Lemma ajournal_gx_mono_k : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k k',
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> k <= k' ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k k' (H0 & H1 & (memS & HJ & Hag) & Hout) Hk.
  split; [exact H0|]. split; [exact H1|]. split; [|exact Hout].
  exists memS. split; [|exact Hag]. eapply ajournal_mono_k; [exact HJ | lia].
Qed.

(* The journal's window lies above the allocator's ceiling. *)
Lemma aj_stk_ceiling : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  alloc_ceiling <= sp0 - STK.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (H0 & H1 & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & _). lia.
Qed.

(* THE KEPT CLAUSE of a run that writes only its own window [slo, shi) and the bytes of E, where every byte of E
   is below SHADOW_OFF (link's globals are: kLowMemEnd = SHADOW_OFF = 0x7fff8000, and gx_ok puts G in the image). *)
Lemma akept_run : forall lyc Sc W memc mdc W2 mem2 slo shi (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> slo <= shi ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) ->
  (forall a, slo <= a < shi -> apresent (w_H W2) mem2 a) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof.
  intros lyc Sc W memc mdc W2 mem2 slo shi E HAR Hceil Hwin UN Hgrow Hpw.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  split; [intros a Ha Hn HE; exact (UN a ltac:(lia) Hn HE)|].
  split.
  - intros b m i Hin Hi HE.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
    apply UN; [lia | lia | exact HE].
  - split.
    + intros a Hi Hno He HE. pose proof (segs_low a Hi) as Hr.
      apply UN; [unfold kLowMemEnd in Hr; lia | unfold kLowMemEnd in Hr; lia | exact HE].
    + split.
      * intros cid pos a Hin Hr HE.
        destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & _).
        pose proof (fs_frame_bytes_nonneg cid) as Hnn.
        assert (Hfa0 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by lia.
        assert (Hfa1 : frame_addr lyc cid pos <= alloc_ceiling) by lia.
        pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfa0) as Hsb1.
        pose proof (shadow_mono (frame_addr lyc cid pos) alloc_ceiling Hfa1) as Hsle.
        assert (Hsh : shadow_addr alloc_ceiling < alloc_ceiling)
          by (unfold shadow_addr, SHADOW_OFF; lia).
        unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
        apply UN; [destruct Hr; lia | destruct Hr; lia | exact HE].
      * split; [intros a Ha Hn Hp; exact (Hgrow a Hp) | exact Hpw].
Qed.

(* The shadow of every heap block the call keeps: the run writes only its window (above the ceiling) and E (below
   SHADOW_OFF), and the shadow of a heap byte is at least SHADOW_OFF and below the ceiling. *)
Lemma ashadow_kept_run : forall lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall x, E x -> x < SHADOW_OFF) ->
  ashadow_kept segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
  intros lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi E HAR Hceil UN HE b m a Hin _ Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
  assert (Ha0 : 0 <= a < kHighMemEnd) by lia.
  assert (Ha1 : a <= alloc_ceiling) by lia.
  pose proof (shadow_addr_bounds a Ha0) as Hsb.
  pose proof (shadow_mono a alloc_ceiling Ha1) as Hsle.
  assert (Hsh : shadow_addr alloc_ceiling < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (Hlo : SHADOW_OFF <= shadow_addr a) by (unfold shadow_addr; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia).
  apply UN; [unfold kHighShadowEnd in Hsb; lia | lia | intros HEa; pose proof (HE _ HEa); lia].
Qed.

(* THE WHOLE POST of a leaf that reaches no allocator: the caller's journal raised by EV, the callee-saved
   registers, the side stack and the allocator state as at the call, the descriptors and the file system, the two
   kept clauses, and the contract's own Q. The run ended at the `ret`, so the registers and memory are the run's
   and the model is the materialised one. *)
Lemma apost_leaf : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  0 <= EV -> sp0 - STK <= spZ regs - K -> spZ regs - K <= spZ regs ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall x, E x -> x < SHADOW_OFF) ->
  Q lyc Sc W regs2 mem2 md2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2).
Proof.
  intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 Q
    HJ HJ2 HEV Hlo Hwin Hfds Hfs HP UN Hgrow Hpw HE HQ.
  pose proof (aj_stk_ceiling G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as Hceil.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  exists lyc, Sc, regs2, mem2, md2.
  split; [reflexivity|].
  split; [eapply ajournal_gx_mono_k; [exact HJ2 | lia]|].
  split; [exact HP|]. split; [reflexivity|].
  split; [exact Hfds|]. split; [exact Hfs|].
  split; [exact (akept_run lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E HAR ltac:(lia) Hwin UN Hgrow Hpw)|].
  split; [exact (ashadow_kept_run lyc Sc lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E HAR ltac:(lia) UN HE)|].
  exact HQ.
Qed.
End j.

(* ==========================================================================
   Section s: the strcmp wrapper on the journal (link_ajkit.v's aj_gx_strncmp_at for strcmp)
   ========================================================================== *)
Section s.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The step through a runtime entry whose contract is RtDefs.v's art_post: link_ajkit.v's aj_gx_art_at with the
   conjunct `same_but_materialized mdc md2` KEPT. link_ajkit.v drops it (its intro pattern after aregs_preserved),
   and a walk's `apost` needs it: the descriptors and the file system at the return are the call's
   (`m_fds md2 = m_fds mdc`, `m_fs md2 = m_fs mdc`) only through it. Found by the decide walk. *)
Lemma aj_gx_art_sm_at : forall stk (Eb : Z -> Prop) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
    mdc k raw (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= stk -> sp0 - STK <= spZ regsT - stk -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, Eb a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc Eb Qr) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - stk <= a < spZ regsT) -> ~ Eb a ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros stk Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw Qr
  HG HJX Hstk Hlo Hhi Hraw HEb HC.
eapply SRr_mono.
{ apply (aj_gx_call_at SK segs B LAWS segs_low stk Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
    mdc k raw
    (fun regs' mem' md' => AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
       same_but_materialized mdc md' /\ Qr regs' mem' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regsT a -> ~ Eb a ->
          aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a) /\
       (forall a, ascratch_stk stk regsT a -> apresent (w_H W) mem' a))
    HG HJX Hstk Hlo Hhi Hraw HEb).
  - intros regs' mem' md' (HAR' & _ & Hs & _ & Hf & Hp & _).
    split; [exact HAR'|]. split; [exact Hs|]. split; [|exact Hp].
    intros a Ha Hw He. exact (Hf a Ha Hw He).
  - exact HC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & Hsm & HQ & Hfr & Hpres2 & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw He; exact (Hfr a Ha Hw He)|]. split; [exact Hpres2 | exact Hsm].
Qed.

(* wrapper_strcmp over lib/A/Rt/RtString.v astrcmp_realizes (window 2 * ESTACK); proved on link by
   lib/A/Rt/RtStrcmpClosed.v link_strcmp_closed. *)
Lemma aj_gx_strcmp_at : forall pc, RtString.astrcmp_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  astr_at segs W memT x sx -> astr_at segs W memT y sy ->
  aread_ok segs (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
  aread_ok segs (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
  atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
  rt_rom_view segs B W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ (getr regs2 10 = w64 0 <-> sx = sy) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hy Hx0 Hy0 Hsx Hsy Hrx Hry Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre SK segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT
  HJX ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_gx_art_sm_at (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' _ => getr regs' 10 = w64 0 <-> sx = sy)
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - exact (HC lyc Sc W regsT memT mdc x y sx sy HPRE Hx Hy Hx0 Hy0 Hsx Hsy Hrx Hry Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hsm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H))|]. split; [exact Hpres2 | exact Hsm].
Qed.

(* wrapper_strncmp over lib/A/Rt/RtString.v astrncmp_realizes (window 2 * ESTACK): link_ajkit.v's
   aj_gx_strncmp_at with `same_but_materialized mdc md2` kept (see aj_gx_art_sm_at); proved on link by
   lib/A/Rt/RtClosed.v cmd_strncmp_closed. *)
Lemma aj_gx_strncmp_sm_at : forall pc, RtString.astrncmp_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> 0 < y ->
  astr_at segs W memT x sx -> astr_at segs W memT y sy ->
  aread_ok segs (2 * ESTACK) W regsT memT x (Z.min n (astr_len sx + 1)) -> amem_range x (astr_len sx + 8) ->
  aread_ok segs (2 * ESTACK) W regsT memT y (Z.min n (astr_len sy + 1)) -> amem_range y (astr_len sy + 8) ->
  atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
  rt_rom_view segs B W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (getr regs2 10 = w64 0 <->
        LStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hy Hn Hnr Hx0 Hy0 Hsx Hsy Hrx Hmx Hry Hmy Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre SK segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT
  HJX ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_gx_art_sm_at (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' _ => getr regs' 10 = w64 0 <->
       LStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0)
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - exact (HC lyc Sc W regsT memT mdc x y n sx sy HPRE Hx Hy Hn Hnr Hx0 Hy0 Hsx Hsy Hrx Hmx Hry Hmy Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hsm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H))|]. split; [exact Hpres2 | exact Hsm].
Qed.
End s.

(* ==========================================================================
   Section v: the byte list a walk reads off the end memory
   ========================================================================== *)
Section v.
Variable segs : list Segment.

(* the n bytes at a, as a list (used to name the Post's byte list bs') *)
Definition abytes_of (m : word -> option byte) (a : Z) (n : nat) : list byte :=
  map (fun i => match mbyte segs m (a + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n).

Lemma abytes_of_length : forall m a n, length (abytes_of m a n) = n.
Proof. intros m a n. unfold abytes_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma abytes_of_nth : forall m a n i b,
  (i < n)%nat -> mbyte segs m (a + Z.of_nat i) = Some b -> nth_error (abytes_of m a n) i = Some b.
Proof.
  intros m a n i b Hi Hb. unfold abytes_of.
  rewrite (lw_nth_error_map_seq _ n 0%nat i Hi). cbn [Nat.add]. rewrite Hb. reflexivity.
Qed.

Lemma abytes_of_abytes : forall m a n,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mbyte segs m (a + Z.of_nat i) = Some b) ->
  abytes segs m a (abytes_of m a n).
Proof.
  intros m a n Ha Han Hs. split; [exact Ha|].
  rewrite abytes_of_length. split; [exact Han|].
  intros i Hi.
  destruct (Hs i Hi) as (b & Hb). rewrite Hb. symmetry. exact (abytes_of_nth m a n i b Hi Hb).
Qed.

(* THE ENTRY SIDE: the Pre gives a function's structure as one byte list (link_spec.v reads its fields with
   `rdn bs off n`); the symbolic entry state needs each field as a `val_mem` at its address. *)
Lemma val_mem_of_abytes : forall m a bs off (n : nat),
  abytes segs m a bs -> 0 <= off -> (Z.to_nat off + n <= length bs)%nat ->
  val_mem segs m (a + off) n (rdn bs off (Z.of_nat n)).
Proof.
  intros m a bs off n Hab Hoff Hn k Hk.
  destruct Hab as (Ha & Hal & Hb).
  assert (Hll : length (slice bs off (Z.of_nat n)) = n) by (rewrite lw_slice_length by lia; lia).
  assert (Hnth : nth_error (slice bs off (Z.of_nat n)) k = nth_error bs (Z.to_nat off + k))
    by (apply lw_slice_nth; lia).
  destruct (nth_error bs (Z.to_nat off + k)) as [b|] eqn:Eb;
    [|exfalso; apply nth_error_None in Eb; lia].
  replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite (Hb (Z.to_nat off + k)%nat ltac:(lia)), Eb. f_equal.
  pose proof (nth_error_le_byte (slice bs off (Z.of_nat n)) k b Hnth) as Hbv.
  pose proof (bytes_le_to_Z_bound (slice bs off (Z.of_nat n))) as Hbd. rewrite Hll in Hbd.
  pose proof (bytes_le_to_Z_nonneg (slice bs off (Z.of_nat n))) as Hnn.
  unfold rdn. rewrite (le_byte_small (bytes_le_to_Z (slice bs off (Z.of_nat n))) n k ltac:(lia) Hk).
  apply bv_eq. rewrite Hbv, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma val_mem_u32 : forall m a bs off, abytes segs m a bs -> 0 <= off -> (Z.to_nat off + 4 <= length bs)%nat ->
  val_mem segs m (a + off) 4 (rdn bs off 4).
Proof. intros m a bs off H Ho Hn. exact (val_mem_of_abytes m a bs off 4%nat H Ho Hn). Qed.

Lemma val_mem_u64 : forall m a bs off, abytes segs m a bs -> 0 <= off -> (Z.to_nat off + 8 <= length bs)%nat ->
  val_mem segs m (a + off) 8 (rdn bs off 8).
Proof. intros m a bs off H Ho Hn. exact (val_mem_of_abytes m a bs off 8%nat H Ho Hn). Qed.

(* two byte lists of the same length at the same address are the same list *)
Lemma abytes_unique : forall m a bs bs', abytes segs m a bs -> abytes segs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H1) (_ & _ & H2) Hl.
  apply lw_list_ext; [exact Hl|]. intros k Hk.
  rewrite <- (H1 k Hk), (H2 k ltac:(lia)). reflexivity.
Qed.

(* the bytes of a value the walk knows, inside such a list *)
Lemma abytes_of_val : forall m a n off (w : nat) v k,
  (Z.to_nat off + w <= n)%nat -> 0 <= off -> (k < w)%nat ->
  val_mem segs m (a + off) w v ->
  nth_error (abytes_of m a n) (Z.to_nat off + k) = Some (Z_to_bv 8 (le_byte v w k)).
Proof.
  intros m a n off w v k Hn Hoff Hk HV.
  apply abytes_of_nth; [lia|].
  replace (a + Z.of_nat (Z.to_nat off + k)) with (a + off + Z.of_nat k) by lia.
  exact (HV k Hk).
Qed.
End v.
End a.
