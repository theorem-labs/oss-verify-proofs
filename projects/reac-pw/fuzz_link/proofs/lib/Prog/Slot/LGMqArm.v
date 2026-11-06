(* The slot's mark step glue, plain image: lmq_arm (the premises of mark_quietly_contract the arm gives) at a
   call cut of mark_quietly, from the facts both call cuts (LC2Defs c2_15d88, LC45Defs c45_13c70) hold:
   sp, tp, a0 = the marks block or NULL, a1 = the name (a g_names slot or a read-only string, with its
   slack) or NULL, the fake kernel, the policy strings, the interface pointers, errno, the guard words. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs LFr LFrEn LFrLo
  LFrMqDefs LGlue.
Import ListNotations.
Local Open Scope Z_scope.

(* the name argument a (LC2Defs c2_name_ok over any address a and option nm) *)
Definition lgmq_name (m : word -> option byte) (a : Z) (nm : option (list byte)) : Prop :=
  str_arg m a nm /\
  forall t, nm = Some t ->
    (length t <= 11)%nat /\
    ((A_RO_LO <= a /\ a + 16 <= A_RO_END) \/
     (exists k, 0 <= k < 64 /\ a = A_G_NAMES + 8 * k /\ (length t <= 4)%nat)) /\
    (exists slack, bytes_at rsegs m (a + Z.of_nat (length t) + 1) slack /\
       Z.of_nat (length slack) = (- (a + Z.of_nat (length t) + 1)) mod 8).

(* [0x10000, 0x11eb0) is read-only image: one closed check *)
Lemma lgmq_ro_chk :
  forallb (fun i => Mem.ro_addr rsegs (wa (0x10000 + Z.of_nat i))) (seq 0 (Z.to_nat 7856)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lgmq_ro_at : forall x, 0x10000 <= x < 0x11eb0 -> Mem.ro_addr rsegs (wa x) = true.
Proof.
  intros x Hx. pose proof lgmq_ro_chk as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - 0x10000)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (0x10000 + (x - 0x10000)) with x in H by lia. exact H.
Qed.

Lemma lgmq_ro_kept : forall a n, 0x10000 <= a -> a + n <= 0x11eb0 -> kept_str a n.
Proof.
  intros a n H1 H2. unfold kept_str. right. intros i Hi. apply lgmq_ro_at. lia.
Qed.

(* the name's span: a read-only name ends by 0x11eb0, a g_names slot's span is its 8 bytes *)
Lemma lgmq_span : forall a t, (length t <= 11)%nat ->
  ((A_RO_LO <= a /\ a + 16 <= A_RO_END) \/
   (exists k, 0 <= k < 64 /\ a = A_G_NAMES + 8 * k /\ (length t <= 4)%nat)) ->
  kept_str a (name_span a t).
Proof.
  intros a t Hl Ha. unfold name_span.
  remember (Z.of_nat (length t)) as n eqn:En.
  pose proof (Z.div_mod (- (a + n + 1)) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (- (a + n + 1)) 8 ltac:(lia)) as Bd.
  destruct Ha as [[H1 H2]|(k & Hk & -> & H4)].
  - apply lgmq_ro_kept; unfold A_RO_LO, A_RO_END in *; lia.
  - unfold kept_str. left. unfold A_G_NAMES, G_NAMES_SIZE in *. lia.
Qed.

(* where lo_name_b puts a table string: g_names, or the odd strings' .rodata *)
Lemma lgmq_name_b_rng : forall q n, lo_name_b q n = true ->
  (A_G_NAMES <= q /\ q + n <= A_G_NAMES + G_NAMES_SIZE) \/ (0x102a2 <= q /\ q + n <= 0x105a1).
Proof.
  intros q n H. unfold lo_name_b in H.
  repeat match goal with Hh : (_ || _)%bool = true |- _ => apply orb_prop in Hh; destruct Hh as [Hh|Hh] end;
  match goal with Hh : lo_in_b _ _ _ _ = true |- _ =>
    unfold lo_in_b in Hh; apply andb_true_iff in Hh as [H1 H2] end;
  apply Z.leb_le in H1; apply Z.leb_le in H2; unfold A_G_NAMES, G_NAMES_SIZE in *; lia.
Qed.

(* the pointer in if_name[i]: interfaces()'s pointer up to the word's wrap, and where that string lies *)
Lemma lgmq_tab_ptr : forall m i n2 ix p, ifptrs_at m -> nth_error link_tab i = Some (n2, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  exists q k, p = q + 18446744073709551616 * k /\
    ((A_G_NAMES <= q /\ q + (Z.of_nat (length n2) + 1) <= A_G_NAMES + G_NAMES_SIZE) \/
     (0x102a2 <= q /\ q + (Z.of_nat (length n2) + 1) <= 0x105a1)).
Proof.
  intros m i n2 ix p HP Hn Hu.
  assert (Hi : (i < 64)%nat).
  { rewrite <- lo_link_len. apply nth_error_Some. rewrite Hn. discriminate. }
  pose proof (lgmq_name_b_rng _ _ (lo_tab_ok_nth link_tab link_ptrs i n2 ix lo_link_tab_ok Hn)) as Rq.
  pose proof (HP i Hi) as Hq.
  assert (W : wz (p mod 2 ^ 64) = wz p).
  { unfold wz. rewrite <- MState.unsigned_lit_wrap. apply Z_to_bv_bv_unsigned. }
  assert (Hm : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (p mod 2 ^ 64)).
  { unfold u64_at in *. rewrite W. exact Hu. }
  assert (Rq' : 0 <= nth i link_ptrs 0 < 2 ^ 64).
  { destruct Rq as [[R1 R2]|[R1 R2]]; unfold A_G_NAMES, G_NAMES_SIZE in *; lia. }
  pose proof (lo_u64_inj m _ _ _ Hm Hq (Z.mod_pos_bound p (2 ^ 64) ltac:(lia)) Rq') as E.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D.
  exists (nth i link_ptrs 0), (p / 2 ^ 64). split; [lia | exact Rq].
Qed.

(* a region [q, q + n) of the image below errno and apart from g_nl, moved by k words of 2^64: apart
   from mark_quietly's frame, g_nl, errno, the FILE block and the marks block *)
Lemma lgmq_apart : forall R S sink a0 mk q k n,
  spZ R = S - 480 -> 0x960e0 + 65536 <= S -> S <= 2 ^ 47 -> errno_at R = 0x75564 ->
  (sink = 0 \/ (4096 <= sink /\ sink + 1304 <= S - 65536 /\
     (sink + 1304 <= 0x10000 \/ 0x97000 <= sink) /\ (sink + 1304 <= mk \/ mk + 516 <= sink))) ->
  (a0 = 0 \/ a0 = mk) -> 4096 <= mk -> mk + 516 <= S - 65536 -> (mk + 516 <= 0x10000 \/ 0x97000 <= mk) ->
  0 < n -> 0x10000 <= q -> q + n <= 0x75564 -> (q + n <= A_G_NL \/ A_G_NL + NK_SIZE <= q) ->
  apart_frame R MARK_QUIETLY_K (q + 18446744073709551616 * k) n /\
  apart_gnl (q + 18446744073709551616 * k) n /\
  apart (errno_at R) 4 (q + 18446744073709551616 * k) n /\
  apart sink FILE_BLOCK (q + 18446744073709551616 * k) n /\
  (a0 <> 0 -> apart a0 MK_SIZE (q + 18446744073709551616 * k) n).
Proof.
  intros R S sink a0 mk q k n Hsp HS1 HS2 He Hsk Ha0 M1 M2 M3 Hn Hq1 Hq2 Hg.
  unfold apart_frame, apart_gnl, apart. rewrite Hsp, He.
  unfold MARK_QUIETLY_K, FILE_BLOCK, MK_SIZE, A_G_NL, NK_SIZE in *.
  destruct (Z.lt_trichotomy k 0) as [Hk|[Hk|Hk]];
    [| subst k; rewrite Z.mul_0_r, Z.add_0_r |];
    (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); intros Hz; lia.
Qed.

Lemma lgmq_errno : forall m R S sink mk,
  spZ R = S - 480 -> 0x960e0 + 65536 <= S -> errno_at R = A_ERRNO ->
  (sink = 0 \/ (4096 <= sink /\ sink + 1304 <= S - 65536 /\
     (sink + 1304 <= 0x10000 \/ 0x97000 <= sink) /\ (sink + 1304 <= mk \/ mk + 516 <= sink))) ->
  wr_at rsegs m A_ERRNO 4 -> mark_errno_ok m R MARK_QUIETLY_K sink.
Proof.
  intros m R S sink mk Hsp HS He Hsk Hw. unfold mark_errno_ok. rewrite He.
  split; [exact Hw|].
  unfold apart_frame, apart_gnl, apart. rewrite Hsp.
  unfold A_ERRNO, A_TP, ERRNO_TP_OFF, MARK_QUIETLY_K, A_G_NL, NK_SIZE, FILE_BLOCK, A_GOT_GUARD, A_G_SAY,
    A_G_SAID, SAID_SIZE, IMG_LO, IMG_TOP in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma lgmq_block : forall m R S sink a0 mk,
  spZ R = S - 480 -> 0x960e0 + 65536 <= S -> errno_at R = 0x75564 -> arg R 0 = a0 ->
  (sink = 0 \/ (4096 <= sink /\ sink + 1304 <= S - 65536 /\
     (sink + 1304 <= 0x10000 \/ 0x97000 <= sink) /\ (sink + 1304 <= mk \/ mk + 516 <= sink))) ->
  (a0 = 0 \/ a0 = mk) -> 4096 <= mk -> mk + 516 <= S - 65536 -> (mk + 516 <= 0x10000 \/ 0x97000 <= mk) ->
  printf_facts_c.pf_img_free mk MK_SIZE ->
  (a0 <> 0 -> exists gbs, marks_at m mk gbs /\ marks_wf gbs) ->
  mark_block_ok m R MARK_QUIETLY_K sink.
Proof.
  intros m R S sink a0 mk Hsp HS He A0 Hsk Ha0 M1 M2 M3 Mf Hmk. unfold mark_block_ok. rewrite A0. intros Hz.
  clear A0. destruct Ha0 as [Ha0|Ha0]; [contradiction|]. subst a0.
  split; [|split; [|split; [|split; [|split]]]].
  - unfold apart_frame. rewrite Hsp. unfold MARK_QUIETLY_K, MK_SIZE. lia.
  - unfold apart_gnl, A_G_NL, NK_SIZE, MK_SIZE. lia.
  - rewrite He. unfold apart, MK_SIZE. lia.
  - unfold apart, FILE_BLOCK, MK_SIZE. lia.
  - exact Mf.
  - exact (Hmk Hz).
Qed.

Section AR.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lgmq_arm : forall g md mk hb T (R : bvmap 5 word) m sink kbs a0 a1 nm,
  lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T -> lmq_sink B g hb T sink ->
  getr R 2 = wz (e_S (lg_E g md mk) - SLOT_FRAME) -> getr R 4 = wz A_TP ->
  getr R 10 = wz a0 -> (a0 = 0 \/ a0 = mk) -> getr R 11 = wz a1 -> lgmq_name m a1 nm ->
  nlk_at m kbs -> nlk_wf kbs -> nk_open kbs = 0 -> iftab_at m kbs link_tab ->
  nk_opened kbs <= 64 * 47 -> nk_opened kbs = nk_closed kbs ->
  policy_ro m -> ifptrs_at m -> wr_at rsegs m A_ERRNO 4 -> guard_m m -> mem_inv rsegs m ->
  (a0 <> 0 -> exists gbs, marks_at m mk gbs /\ marks_wf gbs) ->
  lmq_arm g hb R m sink link_tab kbs nm.
Proof using FF.
  intros g md mk hb T R m sink kbs a0 a1 nm HOK HI HSK HR2 HR4 HR10 Ha0 HR11 HNM
    HNL HNW HNO HIF HOP HOC HPOL HIP HER HGU HMI HMK.
  destruct HNM as (Hsa & Hnm).
  (* the name's address *)
  assert (A1r : 0 <= a1 < 2 ^ 64).
  { destruct nm as [t|].
    - destruct (Hnm t eq_refl) as (_ & Hloc & _). clear - Hloc.
      destruct Hloc as [[L1 L2]|(k & Hk & -> & _)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia.
    - cbn [str_arg] in Hsa. lia. }
  (* the placement *)
  destruct HOK as (HS1 & HS2 & _ & _ & (Hmk1 & Hmk2 & Hmkf) & _).
  assert (S1 : 0x960e0 + 65536 <= lg_S g) by exact HS1.
  assert (S2 : lg_S g <= 2 ^ 47) by exact HS2.
  assert (M1 : 4096 <= mk) by exact Hmk1.
  assert (M2 : mk + 516 <= lg_S g - 65536) by exact Hmk2.
  assert (Mf : printf_facts_c.pf_img_free mk MK_SIZE) by exact Hmkf.
  assert (M3 : mk + 516 <= 0x10000 \/ 0x97000 <= mk)
    by exact (le_img_free mk MK_SIZE Mf ltac:(unfold MK_SIZE; lia)).
  clear HS1 HS2 Hmk1 Hmk2 Hmkf.
  assert (Hmk_hb : In (mk, MK_SIZE) hb).
  { apply (Permutation_in _ (Permutation_sym HI)). right. left. reflexivity. }
  (* the FILE the call finds *)
  assert (SKf : sink = 0 \/ (4096 <= sink /\ sink + 1304 <= lg_S g - 65536 /\
     (sink + 1304 <= 0x10000 \/ 0x97000 <= sink) /\ (sink + 1304 <= mk \/ mk + 516 <= sink))).
  { destruct HSK as [(_ & Hs)|(_ & Hs1 & Hs2 & Hpl & _ & Hhb & _)]; [left; exact Hs|right].
    assert (Hne : (mk, MK_SIZE) <> (sink, MF_BLOCK)).
    { intros E. injection E as E1 E2. discriminate E2. }
    pose proof (Hhb mk MK_SIZE Hmk_hb Hne) as Hd.
    split; [exact Hs1|]. split; [exact Hs2|]. split; [exact Hpl | exact Hd]. }
  (* the registers *)
  assert (G2 : bv_unsigned (getr R 2) = lg_S g - 480).
  { rewrite HR2. change (e_S (lg_E g md mk)) with (lg_S g). unfold wz, SLOT_FRAME.
    apply MState.unsigned_lit. clear - S1 S2. lia. }
  assert (Hsp : spZ R = lg_S g - 480) by exact G2.
  assert (G4 : bv_unsigned (getr R 4) = 0x75608) by (rewrite HR4; unfold wz, A_TP; apply MState.unsigned_lit; lia).
  assert (He : errno_at R = A_ERRNO).
  { transitivity (bv_unsigned (getr R 4) + ERRNO_TP_OFF); [reflexivity|]. rewrite G4. reflexivity. }
  assert (He' : errno_at R = 0x75564) by (rewrite He; reflexivity).
  assert (A0r : 0 <= a0 < 2 ^ 64) by (destruct Ha0 as [-> | ->]; clear - M1 M2 S2; lia).
  assert (VA0 : bv_unsigned (getr R 10) = a0) by (rewrite HR10; unfold wz; apply MState.unsigned_lit; exact A0r).
  assert (VA1 : bv_unsigned (getr R 11) = a1) by (rewrite HR11; unfold wz; apply MState.unsigned_lit; exact A1r).
  assert (A0 : arg R 0 = a0) by exact VA0.
  assert (A1 : arg R 1 = a1) by exact VA1.
  unfold lmq_arm. rewrite VA0, VA1.
  split; [exact HNL|]. split; [exact HNW|]. split; [exact HNO|]. split; [exact HIF|].
  split; [clear - HOP; lia|]. split; [clear - HOP HOC; lia|].
  split; [exact HPOL|]. split; [exact Hsa|].
  split; [exact (lgmq_errno m R (lg_S g) sink mk Hsp S1 He SKf HER)|].
  split.
  { (* the table strings, apart from what the call writes *)
    unfold mark_table_ok. intros i n2 ix p Hn Hu. cbv zeta. rewrite A0.
    destruct (lgmq_tab_ptr m i n2 ix p HIP Hn Hu) as (q & k & -> & Hq).
    apply (lgmq_apart R (lg_S g) sink a0 mk q k _ Hsp S1 S2 He' SKf Ha0 M1 M2 M3);
      clear - Hq; unfold A_G_NAMES, G_NAMES_SIZE, A_G_NL, NK_SIZE in *; lia. }
  split.
  { (* the marks block is the slot's block mk *)
    intros Hz. destruct Ha0 as [Ha0|Ha0]; [contradiction|].
    exists mk, MK_SIZE. split; [exact Hmk_hb|]. clear - Ha0. lia. }
  split.
  { (* the name is kept *)
    intros s Hs. destruct (Hnm s Hs) as (Hl & Hloc & _). exact (lgmq_span a1 s Hl Hloc). }
  split.
  { (* the table strings are kept *)
    intros i n2 ix p Hn Hu Hp.
    destruct (lgmq_tab_ptr m i n2 ix p HIP Hn Hu) as (q & k & -> & Hq).
    clear - Hp Hq. unfold A_G_NAMES, G_NAMES_SIZE in Hq.
    assert (Hk : k = 0) by lia. subst k. rewrite Z.mul_0_r, Z.add_0_r.
    destruct Hq as [[Q1 Q2]|[Q1 Q2]].
    - unfold kept_str, A_G_NAMES, G_NAMES_SIZE. left. lia.
    - apply lgmq_ro_kept; lia. }
  split.
  { (* the name, apart from what the call writes *)
    unfold mark_name_ok. intros s Hs. rewrite A0, A1.
    destruct (Hnm s Hs) as (Hl & Hloc & Hslack).
    assert (Q : 0x10000 <= a1 /\ a1 + (Z.of_nat (length s) + 8) <= 0x75564 /\
      (a1 + (Z.of_nat (length s) + 8) <= A_G_NL \/ A_G_NL + NK_SIZE <= a1)).
    { clear - Hl Hloc. unfold A_G_NL, NK_SIZE.
      destruct Hloc as [[L1 L2]|(k & Hk & -> & L4)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia. }
    destruct Q as (Q1 & Q2 & Q3).
    pose proof (lgmq_apart R (lg_S g) sink a0 mk a1 0 (Z.of_nat (length s) + 8) Hsp S1 S2 He' SKf Ha0
      M1 M2 M3 ltac:(clear - Hl; lia) Q1 Q2 Q3) as (F1 & F2 & F3 & F4 & F5).
    rewrite Z.mul_0_r, Z.add_0_r in F1, F2, F3, F4, F5.
    split; [clear - Hl; lia|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F3|].
    split; [exact Hslack|].
    intros Hz. specialize (F5 Hz). clear - F5. unfold apart in *. lia. }
  split; [exact (lgmq_block m R (lg_S g) sink a0 mk Hsp S1 He' A0 SKf Ha0 M1 M2 M3 Mf HMK)|].
  exact HGU.
Qed.

End AR.

Print Assumptions lgmq_arm.
