From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame pj_get_c pj_get_str_c EntD_Base.
Import ListNotations.
Open Scope Z_scope.

Definition d1_inv (m0 m : word -> option byte) (S lo : Z) : Prop :=
  munch [(S - 64, S); (S + 64, S + 72)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  stk rsegs m lo S /\ lo <= S - 64 /\ stk rsegs m (S + 64) (S + 72).

Definition d1_blk (lblk : Z -> Z -> Prop) (S : Z) : Prop :=
  forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 64) 136.

Definition d1_key (k : Z) (K : list Z) : Prop :=
  0 <= k /\ k + Z.of_nat (length K) + 1 <= 2 ^ 64 /\
  forallb (fun c => (0 <? c) && (c <? 256)) K = true /\
  ro_bytes_b rsegs k (map (Z_to_bv 8) (K ++ [0])) = true.

Ltac d1_keyok :=
  unfold d1_key; refine (conj _ (conj _ (conj _ _)));
  first [apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].

Ltac d1_lit := first [reflexivity | apply bv_eq; vm_compute; reflexivity].

Lemma d1_inv_mk : forall m0 m S lo,
  munch [(S - 64, S); (S + 64, S + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo S -> lo <= S - 64 -> stk rsegs m (S + 64) (S + 72) -> d1_inv m0 m S lo.
Proof. intros m0 m S lo H1 H2 H3 H4 H5 H6. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). Qed.

Lemma d1_inv_refl : forall m S lo, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 ->
  stk rsegs m (S + 64) (S + 72) -> d1_inv m m S lo.
Proof. intros m S lo H3 H4 H5 H6. exact (d1_inv_mk m m S lo (munch_refl _ m) (wmono_refl rsegs m) H3 H4 H5 H6). Qed.

Lemma d1_munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. exact (H x Hx). Qed.

Lemma d1_munch_call : forall S w m0 m m', 0 <= w <= 64 ->
  munch [(S - 64, S); (S + 64, S + 72)] m0 m -> munch [(S - w, S)] m m' ->
  munch [(S - 64, S); (S + 64, S + 72)] m0 m'.
Proof.
  intros S w m0 m m' Hw H1 H2. apply (munch_trans _ m0 m m' H1).
  apply (munch_weaken [(S - w, S)]); [|exact H2].
  intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A & _ & _).
  split; [intros [C1 C2]; apply A; split; lia | exact I].
Qed.

Lemma d1_slot : forall m S, stk rsegs m (S + 64) (S + 72) -> exists j, rw_cells rsegs m (S + 64) [CB 8 j].
Proof.
  intros m S H. destruct (stk_carve rsegs m (S + 64) (S + 72) 8 H ltac:(lia)) as (_ & j & HJ).
  change (Z.of_nat 8) with 8 in HJ. exists j. replace (S + 64) with (S + 72 - 8) by lia. exact HJ.
Qed.

Lemma d1_slot_back : forall m S v, rw_cells rsegs m (S + 64) [C8 v] -> stk rsegs m (S + 64) (S + 72).
Proof.
  intros m S v H. pose proof (stk_of_rw_cells rsegs m (S + 64) [C8 v] H) as H'.
  change (Z.of_nat (cells_size [C8 v])) with 8 in H'. replace (S + 72) with (S + 64 + 8) by lia. exact H'.
Qed.

Lemma d1_root_out : forall m lblk S t D, d1_blk lblk S -> pj_node rsegs m lblk (S + 8) t D ->
  forall x, pj_foot (S + 8) D x -> outside [(S - 64, S); (S + 64, S + 72)] x.
Proof.
  intros m lblk S t D HB HN x [Hx|((a & n) & Hin & Hx)]; cbn [outside].
  - split; [intros [C1 C2]; lia|]. split; [intros [C1 C2]; lia | exact I].
  - pose proof (pj_node_blocks rsegs t m lblk (S + 8) D HN a n Hin) as HL.
    destruct (HB a n HL) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
    unfold pj_holds in Hx. cbn [fst snd] in Hx.
    split; [intros [C1 C2]; lia|]. split; [intros [C1 C2]; lia | exact I].
Qed.

Lemma d1_sub : forall m0 lblk S t D K z, d1_blk lblk S -> pj_node rsegs m0 lblk (S + 8) t D ->
  pj_get_res m0 lblk (S + 8) t D K z ->
  z = 0 \/ exists v Dv, pj_node rsegs m0 lblk z v Dv /\
    (forall x, pj_foot z Dv x -> outside [(S - 64, S); (S + 64, S + 72)] x).
Proof.
  intros m0 lblk S t D K z HB HN HR.
  destruct (entd_get_sub m0 lblk (S + 8) t D K z HN HR) as [Hz|(v & Dz & Hv & Hf)]; [left; exact Hz|right].
  exists v, Dz. split; [exact Hv|]. intros x Hx. exact (d1_root_out m0 lblk S t D HB HN x (Hf x Hx)).
Qed.

Lemma d1_ro_out : forall m lo hi k bs, mem_inv rsegs m -> stk rsegs m lo hi -> ro_bytes rsegs k bs ->
  forall x, k <= x < k + Z.of_nat (length bs) -> ~ (lo <= x < hi).
Proof.
  intros m lo hi k bs MI (_ & _ & HS) HR x Hx Hin.
  destruct (nth_error bs (Z.to_nat (x - k))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  pose proof (ro_bytes_nth rsegs bs k _ b HR E) as (_ & Hro).
  replace (k + Z.of_nat (Z.to_nat (x - k))) with x in Hro by lia.
  destruct (HS x Hin) as (Hw & _).
  destruct (m (wa x)) as [b'|] eqn:Em.
  - pose proof (MI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa x) Hw Em). congruence.
Qed.

Lemma d1_key_apart : forall m lo S w k K, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - w -> 0 < w -> d1_key k K ->
  k + Z.of_nat (length K) + 1 <= S - w \/ S <= k.
Proof.
  intros m lo S w k K MI ST HL Hw (H0 & H1 & HF & HB).
  pose proof (ro_bytes_b_sound rsegs _ _ HB) as HR.
  assert (HA : forall x, k <= x < k + (Z.of_nat (length K) + 1) -> ~ (S - w <= x < S)).
  { intros x Hx Hin. apply (d1_ro_out m lo S k (map (Z_to_bv 8) (K ++ [0])) MI ST HR x);
      [rewrite length_map, length_app; cbn [length]; lia | lia]. }
  destruct (entd_apart k (Z.of_nat (length K) + 1) (S - w) S ltac:(lia) ltac:(lia) HA) as [E|E]; [left|right]; lia.
Qed.

Lemma d1_key_cb : forall m k K, mem_inv rsegs m -> d1_key k K -> pj_cbytes rsegs m k K.
Proof. intros m k K MI (H0 & H1 & HF & HB). exact (entd_cb m k K MI H0 H1 HF HB). Qed.

Section C.
Hypothesis HGET : pj_get_contract.
Hypothesis HGSTR : pj_get_str_contract.

Lemma d1_get : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (S lo k : Z) (K : list Z)
    (t : jv) (D : list (Z * Z)),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (S + 8) -> a1 = Z_to_bv 64 k ->
  120 <= S -> S mod 16 = 0 -> d1_blk lblk S -> d1_inv m0 m S lo ->
  pj_node rsegs m0 lblk (S + 8) t D -> d1_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte) (z : Z),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      d1_inv m0 m' S lo /\ r = Z_to_bv 64 z /\ pj_get_res m0 lblk (S + 8) t D K z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    S lo k K t D Esp E0 E1 HS H16 HB (MU & WM & MI & ST & HLo & SL) HN HK.
  assert (HS72 : S + 72 <= 2 ^ 64) by (destruct SL as (_ & ? & _); lia).
  assert (HSU : bv_unsigned sp = S) by (subst sp; apply unsigned_lit; lia).
  pose proof (d1_root_out m0 lblk S t D HB HN) as HO.
  pose proof (entd_node_tr _ m0 m lblk (S + 8) t D HN MU HO) as HNm.
  pose proof (d1_key_apart m lo S 48 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  eapply evt_mono.
  { apply (HGET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lblk (S + 8) k K t D lo E0 E1 (or_intror HNm) (d1_key_cb m k K MI HK)); rewrite ?HSU.
    - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
    - exact H16.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU' & WM' & MI' & ST' & _ & Hr).
  rewrite HSU in MU', ST'.
  destruct Hr as [(Ho & _)|(_ & HN' & z & Er & HR)]; [lia|].
  pose proof (d1_munch_call S 48 m0 m m' ltac:(lia) MU MU') as MU2.
  exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', z.
  split; [exact E|]. split.
  - apply (d1_inv_mk m0 m' S lo MU2 (wmono_trans rsegs m0 m m' WM WM') MI' ST' HLo).
    apply (stk_transport_disjoint rsegs [(S - 48, S)] m m' (S + 64) (S + 72) SL MU' WM').
    cbn [disjoint_from]. split; [lia | exact I].
  - split; [exact Er|].
    exact (entd_res_tr _ m' m0 lblk (S + 8) t D K z HN' HR (d1_munch_sym _ m0 m' MU2) HO).
Qed.

Lemma d1_gstr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (S lo o k : Z) (K : list Z),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k ->
  120 <= S -> S mod 16 = 0 -> d1_blk lblk S -> d1_inv m0 m S lo ->
  (o = 0 \/ exists v Dv, pj_node rsegs m0 lblk o v Dv /\
     (forall x, pj_foot o Dv x -> outside [(S - 64, S); (S + 64, S + 72)] x)) ->
  d1_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      d1_inv m0 m' S lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET_STR) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    S lo o k K Esp E0 E1 HS H16 HB (MU & WM & MI & ST & HLo & SL) Ho HK.
  assert (HS72 : S + 72 <= 2 ^ 64) by (destruct SL as (_ & ? & _); lia).
  assert (HSU : bv_unsigned sp = S) by (subst sp; apply unsigned_lit; lia).
  pose proof (d1_key_apart m lo S 64 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  assert (HX : exists v Dv, (o = 0 \/ pj_node rsegs m lblk o v Dv) /\ (S <= o \/ o + 56 <= S - 64)).
  { destruct Ho as [Ho|(v & Dv & HNv & HOv)].
    - exists JNull, []. split; [left; exact Ho | right; lia].
    - exists v, Dv. split; [right; exact (entd_node_tr _ m0 m lblk o v Dv HNv MU HOv)|].
      assert (HA : forall x, o <= x < o + 56 -> ~ (S - 64 <= x < S)).
      { intros x Hx. pose proof (HOv x (or_introl Hx)) as Hq. cbn [outside] in Hq. exact (proj1 Hq). }
      destruct (entd_apart o 56 (S - 64) S ltac:(lia) ltac:(lia) HA) as [E|E]; [right|left]; lia. }
  destruct HX as (v & Dv & HNo & HDo).
  eapply evt_mono.
  { apply (HGSTR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lblk o k K v Dv lo E0 E1 HNo (d1_key_cb m k K MI HK)); rewrite ?HSU.
    - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
    - exact H16.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU' & WM' & MI' & ST' & _ & _).
  rewrite HSU in MU', ST'.
  pose proof (d1_munch_call S 64 m0 m m' ltac:(lia) MU MU') as MU2.
  exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|].
  apply (d1_inv_mk m0 m' S lo MU2 (wmono_trans rsegs m0 m m' WM WM') MI' ST' HLo).
  apply (stk_transport_disjoint rsegs [(S - 64, S)] m m' (S + 64) (S + 72) SL MU' WM').
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

End C.
