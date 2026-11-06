(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Mem Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require APristLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Actr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Definition is_heap (b : ablock) : Prop := exists p, ab_kind b = ABHeap p.
Definition is_fake (b : ablock) : Prop := exists c, ab_kind b = ABFake c.
Lemma kind_cases : forall b, is_heap b \/ is_fake b.
Proof. intros [[p|c] A n]; [left; exists p| right; exists c]; reflexivity. Qed.
Lemma heap_not_fake : forall b, is_heap b -> is_fake b -> False.
Proof. intros [[p|c] A n] [q E] [d E']; cbn in *; congruence. Qed.
Lemma ablock_eq_dec : forall x y : ablock, {x = y} + {x <> y}.
Proof. decide equality; try apply Z.eq_dec. decide equality; [apply N.eq_dec| apply Z.eq_dec]. Defined.

Definition lb_del (b : ablock) (LBa : list ablock) : list ablock := List.filter (fun x => if ablock_eq_dec x b then false else true) LBa.
Lemma lb_del_In : forall b LBa x, In x (lb_del b LBa) <-> In x LBa /\ x <> b.
Proof. intros b LBa x. unfold lb_del. rewrite filter_In. destruct (ablock_eq_dec x b); split; intros [H1 H2]; try discriminate; try contradiction; auto. Qed.

Section FakeIface.
Context {rc : runConstT}.
Variable AI : AMallocIface2.

Definition flag_law (L : alayout) (b : ablock) (flg : Z) : Prop :=
  forall RNG st LBa m, AHEAP AI L RNG st LBa m -> In b LBa ->
    AHEAP AI L RNG st (lb_del b LBa) (write_to_mem m (wa flg) [Z_to_bv 8 0])
    /\ wr_at asegs m flg 1 /\ ((AIMG_HI <= flg /\ flg < KLS) \/ (0x10007fff8000 <= flg /\ flg < ATOP))
    /\ (forall b', In b' LBa -> ~ (ab_addr b' <= flg < ab_addr b' + ab_size b'))

    /\ al_fake L <= flg /\ flg < al_fake L + 11571200.
Record fake_iface : Type := mkFakeIface {
  FLG : alayout -> ablock -> Z;
  FRNG : alayout -> footprint -> Prop;
  fk_facts :> forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b ->
     ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0 /\ ab_size b mod 8 = 0 /\ 64 <= ab_size b
     /\ wr_at asegs m (ab_addr b) (ab_size b) /\ wr_at asegs m (shad (ab_addr b)) (shlen (ab_size b));
  fk_class : forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b ->
     exists c, ab_kind b = ABFake c /\ 0 <= c /\ ab_size b = 64 * 2 ^ c;
  fk_law : forall L b, is_fake b -> flag_law L b (FLG L b);
  fk_rng : forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b -> FRNG L RNG ->
     rng RNG (ab_addr b) (ab_size b) /\ rng RNG (shad (ab_addr b)) (shlen (ab_size b)) /\ rng RNG (FLG L b) 1;
  fk_area : forall L RNG, FRNG L RNG -> rng RNG (al_fake L) 11571200 }.
End FakeIface.

Abbreviation AI_fake_law := fake_iface.

Section ImgxOk.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Definition imgx_ok (IMGX : list iv) : Prop := forall v, In v IMGX -> 0 <= snd v /\
  (   (exists r, In r (aci AI) /\ fst r <= fst v /\ fst v + snd v <= snd r)
   \/ (exists r, In r (aci AI) /\ fst r <= 8 * (fst v - ASHOFF) /\ 8 * (fst v - ASHOFF) + 8 * snd v <= snd r)
   \/ (ATOP <= 8 * (fst v - ASHOFF) /\ 8 * (fst v - ASHOFF) + 8 * snd v <= 2 ^ 47)).
End ImgxOk.

Lemma is_primary_le : forall n, 0 <= n <= 64512 -> is_primary n = true.
Proof.
  intros n Hn. unfold is_primary, needed0, rounded_size, rz_size, rz_log, K_MAX_SIZE, rup.
  apply Z.leb_le.
  repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end;
    rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.
Qed.

Section AsanWorld.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.

Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).

Definition PUBSH : list (Z * Z) := [(0x800b9828, 0x800b9980); (0x800b9998, 0x800bd9e8); (0x800bd9f0, 0x800bdb80); (0x800bdb88, 0x800bdc05); (0x800bdc06, 0x800bdca8)].

Definition STGSH : list (Z * Z) := [(0x800b7820, 0x800b9828)].
Definition SHLIT : list (Z * Z) := ActrA.IMGSH ++ STGSH ++ PUBSH.
Lemma IMGSH_SHLIT : forall v, In v ActrA.IMGSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. left. exact H. Qed.
Lemma STGSH_SHLIT : forall v, In v STGSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma PUBSH_SHLIT : forall v, In v PUBSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
Lemma SHLIT_cases : forall v, In v SHLIT ->
  v = (0x7fffa000, 0x7fffc66c) \/ (In v (STGSH ++ PUBSH) /\ 0x800b7820 <= fst v /\ fst v <= snd v /\ snd v <= 0x800bdca8).
Proof.
  intros v H. unfold SHLIT in H. apply in_app_or in H. destruct H as [H|H].
  - left. unfold ActrA.IMGSH in H. cbn [In] in H. destruct H as [<-|[]]. reflexivity.
  - right. split; [exact H|]. unfold STGSH, PUBSH in H. cbn [In app] in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.
Definition sh_cov (z : Z) : Prop :=
  (exists a', ATOP <= a' < 2^47 /\ z = shad a') \/ (exists v, In v SHLIT /\ fst v <= z < snd v).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.

Variable UNIV : list (list Z).

Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (wa a) = m (wa a)) -> wmono asegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> wmono asegs m m'.

Definition usz (b : ablock) : Z := match ab_kind b with ABFake _ => ab_size b - 8 | ABHeap _ => ab_size b end.
Definition user_iv (b : ablock) : iv := (ab_addr b, usz b).
Lemma usz_le : forall b, ab_size b - 8 <= usz b <= ab_size b.
Proof. intros [[p|c] A n]; unfold usz; cbn; lia. Qed.
Lemma usz_heap : forall b, is_heap b -> usz b = ab_size b.
Proof. intros [[p|c] A n] [q E]; unfold usz; cbn in *; [reflexivity| discriminate]. Qed.
Lemma usz_fake : forall b, is_fake b -> usz b = ab_size b - 8.
Proof. intros [[p|c] A n] [q E]; unfold usz; cbn in *; [discriminate| reflexivity]. Qed.
Ltac usz_facts :=
  repeat match goal with
         | |- context [usz ?b] => lazymatch goal with H' : ab_size b - 8 <= usz b <= ab_size b |- _ => fail | _ => pose proof (usz_le b) end
         | H : context [usz ?b] |- _ => lazymatch goal with H' : ab_size b - 8 <= usz b <= ab_size b |- _ => fail | _ => pose proof (usz_le b) end
         end.
Ltac ulia := usz_facts; lia.
Definition twin_iv (b : ablock) : iv := (shad (ab_addr b), shlen (ab_size b + 7)).
Definition fsh_iv (b : ablock) : iv := (shad (ab_addr b), shlen (ab_size b)).
Definition ZTOTAL : Z := 1024.
Definition FRAME_MAX : Z := 256.

Variable AI_fake : fake_iface AI.

Record wit := mkWit { w_L : alayout; w_RNG : footprint; w_st : astate; w_LBa : list ablock; w_T : list ablock; w_FA : list ablock;
                      w_ms : amem; w_zc : Z }.
Definition vis (W : wit) (b : ablock) : Prop := In b (w_LBa W) /\ ~ In b (w_FA W).
Definition visf (W : wit) (b : ablock) : Prop := vis W b /\ is_fake b.

Definition aw_holds_w (W : wit) (aw : word) (LB : blocks) (m : amem) (mo : Model) : Prop :=
     AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_ms W)
  /\ (forall b, In b (w_T W) -> In b (w_LBa W) /\ is_heap b) /\ List.NoDup (w_T W)
  /\ (forall b, In b (w_FA W) -> In b (w_LBa W) /\ is_fake b) /\ List.NoDup (w_FA W)
  /\ (forall v, In v LB <->    (exists b, vis W b /\ v = user_iv b) \/ (exists b, In b (w_T W) /\ v = twin_iv b)
                            \/ (exists b, visf W b /\ v = fsh_iv b))
  /\ (forall a, 0 <= a < two64 -> ~ in_ivs (map twin_iv (w_T W)) a -> w_ms W (wa a) = m (wa a))
  /\ (forall a, in_ivs (map twin_iv (w_T W)) a -> m (wa a) <> None)
  /\ 0 <= w_zc W /\ Z.of_nat (length (w_FA W)) + w_zc W <= ZTOTAL
  /\ ACCT aw (w_L W) (w_RNG W) (w_st W) (w_LBa W) mo
  /\ incl UNIV (al_U (w_L W))
  /\ (forall b, In b (w_LBa W) -> is_fake b -> ab_size b <= FRAME_MAX)
  /\ (forall b, visf W b ->
        exists flg, bytes_at asegs (w_ms W) (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg)
  /\ (forall b, vis W b -> is_heap b -> ~ In b (w_T W) -> forall g, 0 <= g -> 8 * g < ab_size b ->
        m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
Definition aw_holds_asan (aw : word) (LB : blocks) (m : amem) (mo : Model) : Prop := exists W, aw_holds_w W aw LB m mo.

Definition aw_ceiling_asan (_ : Model) : Z := ATOP + 4096.
Definition aw_dep_asan (LB : blocks) (_ : amem) (_ : Model) (a : Z) : Prop :=
  0 <= a < ATOP + 4096 /\ ~ in_user LB a /\ ~ in_ivs IMGX a.

Fixpoint in_ivs_b (l : list iv) (a : Z) : bool :=
  match l with
  | [] => false
  | v :: l' => ((fst v <=? a) && (a <? fst v + snd v)) || in_ivs_b l' a
  end.
Lemma in_ivs_b_spec : forall l a, in_ivs_b l a = true <-> in_ivs l a.
Proof.
  induction l as [|v l IH]; intros a; cbn [in_ivs_b].
  - split; [discriminate| intros H; inversion H].
  - rewrite in_ivs_cons, <- IH. unfold in_iv. rewrite orb_true_iff, andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Definition to_ivl (v : iv) : ivl := (fst v, fst v + snd v).
Lemma outside_map : forall l x, outside (map to_ivl l) x <-> ~ in_ivs l x.
Proof.
  induction l as [|v l IH]; intros x; cbn [map outside].
  - split; [intros _ H; inversion H| intros _; exact I].
  - unfold to_ivl at 1. cbn [fst snd]. rewrite IH, in_ivs_cons. unfold in_iv. tauto.
Qed.
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto| rewrite IH; tauto]. Qed.

Lemma wview_ext1 : forall (m1 m2 : amem) x, m1 x = m2 x -> wview asegs m1 x = wview asegs m2 x.
Proof. intros m1 m2 x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma heap_block_facts : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b ->
  1 <= ab_size b <= AREQMAX /\ ablock_range (ab_addr b) (ab_size b) /\ wr_at asegs ms (ab_addr b) (ab_size b).
Proof.
  intros L RNG st LBa ms [k A n] AH Hb [p Hp]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (N & BR & _ & _ & _ & WR & _). auto.
Qed.

Lemma blk_facts : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa ->
  0 < ab_size b /\ ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0
  /\ wr_at asegs ms (ab_addr b) (ab_size b).
Proof.
  intros L RNG st LBa ms b AH Hb. destruct (kind_cases b) as [HH|HF].
  - destruct (heap_block_facts L RNG st LBa ms b AH Hb HH) as (N & (BK & N0 & HI & AL) & WR).
    split; [ulia|]. split; [exact BK|]. split; [exact HI|]. split; [clear -AL; Z.div_mod_to_equations; ulia| exact WR].
  - destruct (AI_fake L RNG st LBa ms b AH Hb HF) as (BK & HI & A8 & N8 & NP & WR & _). split; [ulia|]. split; [exact BK|]. split; [exact HI|]. split; [exact A8| exact WR].
Qed.

Lemma twin_band : forall A n, ablock_range A n -> 1 <= n <= AREQMAX ->
  0x7fff8000 <= shad A /\ shad A + shlen (n + 7) <= 0x10007fff8000 /\ 1 <= shlen (n + 7) /\ shad A + shlen (n + 7) = shad (A + n + 7).
Proof.
  intros A n (BK & N0 & HI & AL) N. pose proof atop_range as AR. unfold ablk, AIMG_HI, KLS, AREQMAX in *.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8.
  repeat split; Z.div_mod_to_equations; ulia.
Qed.
Lemma fsh_band : forall A n, ablk A (A + n) -> A + n <= ATOP -> A mod 8 = 0 -> n mod 8 = 0 -> 0 < n ->
  0x7fff8000 <= shad A /\ shad A + shlen n <= 0x10007fff8000 /\ 1 <= shlen n /\ 8 * (shad A - ASHOFF) = A /\ 8 * shlen n = n.
Proof.
  intros A n BK HI A8 N8 NP. pose proof atop_range as AR. unfold ablk, AIMG_HI, KLS in *.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8.
  repeat split; Z.div_mod_to_equations; ulia.
Qed.
Lemma user_app_band : forall A n, ablk A (A + n) -> 0 < n -> (A + n <= 0x7fff8000 \/ 0x10007fff8000 <= A) /\ 6483968 <= A.
Proof. intros A n BK NP. unfold ablk, AIMG_HI, KLS in BK. ulia. Qed.

Lemma LB_cases : forall W aw LB m mo v, aw_holds_w W aw LB m mo -> In v LB ->
     (exists b, vis W b /\ v = user_iv b) \/ (exists b, In b (w_T W) /\ v = twin_iv b)
  \/ (exists b, visf W b /\ v = fsh_iv b).
Proof. intros W aw LB m mo v (_ & _ & _ & _ & _ & HLB & _) Hv. apply HLB. exact Hv. Qed.

Lemma usz_pos : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa -> 0 < usz b.
Proof.
  intros L RNG st LBa ms b AH Hb. destruct (kind_cases b) as [HH|HF].
  - rewrite (usz_heap b HH). destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & _). exact NP.
  - rewrite (usz_fake b HF). destruct (AI_fake L RNG st LBa ms b AH Hb HF) as (_ & _ & _ & _ & N64 & _). lia.
Qed.
Lemma LB_user_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> vis W b ->
  0 < usz b /\ (ab_addr b + ab_size b <= 0x7fff8000 \/ 0x10007fff8000 <= ab_addr b) /\ 6483968 <= ab_addr b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros W aw LB m mo b (AH & _) [Hb _]. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _).
  destruct (user_app_band _ _ BK NP) as [B1 B2]. split; [exact (usz_pos _ _ _ _ _ b AH Hb)|]. auto.
Qed.
Lemma LB_twin_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> In b (w_T W) ->
  0x7fff8000 <= shad (ab_addr b) /\ shad (ab_addr b) + shlen (ab_size b + 7) <= 0x10007fff8000 /\ 1 <= shlen (ab_size b + 7).
Proof.
  intros W aw LB m mo b (AH & HT & _) Hb. destruct (HT b Hb) as [HbL HbH].
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (N & BR & _). destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _). auto.
Qed.
Lemma LB_fsh_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> visf W b ->
  0x7fff8000 <= shad (ab_addr b) /\ shad (ab_addr b) + shlen (ab_size b) <= 0x10007fff8000 /\ 1 <= shlen (ab_size b)
  /\ 8 * (shad (ab_addr b) - ASHOFF) = ab_addr b /\ 8 * shlen (ab_size b) = ab_size b.
Proof.
  intros W aw LB m mo b (AH & _) [[Hb _] HF]. destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
  exact (fsh_band _ _ BK HI A8 N8 ltac:(ulia)).
Qed.

Definition fakeb (b : ablock) : bool := match ab_kind b with ABFake _ => true | ABHeap _ => false end.
Lemma fakeb_spec : forall b, fakeb b = true <-> is_fake b.
Proof. intros [[p|c] A n]; unfold fakeb, is_fake; cbn; split; intros H; try discriminate; try (exists c; reflexivity); try reflexivity. destruct H as [d H]. discriminate. Qed.
Definition set_ms (W : wit) (ms : amem) : wit := mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (w_FA W) ms (w_zc W).

Lemma bytes_at_agreeN : forall (m m' : amem) a bs,
  bytes_at asegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [ulia|]. split; [ulia|]. intros i Hi.
  unfold mrd in *. rewrite E by ulia. apply H. exact Hi.
Qed.

Lemma IMGX_class : forall a, in_ivs IMGX a -> a < AIMG_HI \/ (0x7fff8000 <= a < 0x800bde00) \/ (shad ATOP <= a < shad (2 ^ 47)).
Proof.
  intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). destruct (IMGX_aci w Hw) as (N0 & [(r & Hr & R1 & R2)|[(r & Hr & R1 & R2)|(S1 & S2)]]);
    unfold in_iv in Hin.
  - left. pose proof (AI_aci_img AI r Hr). lia.
  - right. left. pose proof (AI_aci_img AI r Hr) as HI. pose proof (AI_aci_lo AI r Hr) as LO. unfold AIMG_HI, ASHOFF in *. lia.
  - right. right. pose proof atop_range as AR. unfold shad, ASHOFF in *. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_tight : forall A n, ablk A (A + n) -> A + n <= ATOP -> 0 < n -> 0x800bde00 <= shad A /\ shad A + shlen (n + 7) <= shad ATOP.
Proof.
  intros A n BK HI NP. pose proof atop_range as AR. pose proof ATOP_al16 as A16. unfold ablk, AIMG_HI, KLS in BK.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia.
Qed.

Lemma sh_cov_band : forall a, sh_cov a -> (0x7fffa000 <= a < 0x800bdca8) \/ (shad ATOP <= a < 0x10007fff8000).
Proof.
  intros a [(a' & R & ->)|(v & Hv & R)].
  - right. pose proof atop_range as AR. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
  - left. destruct (SHLIT_cases v Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in R|]; lia.
Qed.
Lemma blk_not_IMGX : forall L RNG st LBa ms b a, AHEAP AI L RNG st LBa ms -> In b LBa ->
  (ab_addr b <= a < ab_addr b + ab_size b \/ shad (ab_addr b) <= a < shad (ab_addr b) + shlen (ab_size b + 7)) -> ~ in_ivs IMGX a.
Proof.
  intros L RNG st LBa ms b a AH Hb Ha II. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _).
  destruct (shadow_tight _ _ BK HI NP) as [T1 T2]. destruct (user_app_band _ _ BK NP) as [B1 B2]. pose proof atop_range as AR.
  assert (SHT : shad (2 ^ 47) = 0x10007fff8000) by reflexivity.
  assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (IMGX_class a II) as [C|[C|C]]; unfold AIMG_HI in *; destruct Ha as [Ha|Ha]; lia.
Qed.

Lemma blk_byte_private : forall W aw LB m mo b x, aw_holds_w W aw LB m mo -> In b (w_LBa W) -> ab_addr b <= x < ab_addr b + ab_size b ->
  forall v, In v LB -> in_iv v x -> v = user_iv b /\ vis W b.
Proof.
  intros W aw LB m mo b x HW Hb Hx v Hv Hin. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & _).
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _). destruct (user_app_band _ _ BK NP) as [B1 B2].
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b' & Vb' & ->)|[(b' & Hb' & ->)|(b' & Vb' & ->)]]; unfold in_iv in Hin; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
  - destruct (ablock_eq_dec b' b) as [->|NE]; [split; [reflexivity| exact Vb']| exfalso].
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b' b AH (proj1 Vb') Hb NE) as D. ulia.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). ulia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & _). ulia.
Qed.

Lemma flagw_facts : forall W aw LB m mo b x, aw_holds_w W aw LB m mo -> visf W b -> ab_addr b + ab_size b - 8 <= x < ab_addr b + ab_size b ->
  0 <= x < two64 /\ ~ in_ivs (map twin_iv (w_T W)) x /\ ~ in_user LB x /\ ~ in_ivs IMGX x /\ x < ATOP + 4096
  /\ ab_addr b <= x < ab_addr b + ab_size b.
Proof.
  intros W aw LB m mo b x HW [[HbL NFA] HF] Hx. pose proof HW as (AH & _). pose proof atop_range as AR.
  destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
  destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
  split; [unfold two64; lia|]. split.
  { intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
    destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. lia. }
  split.
  { intros IU. unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin).
    destruct (blk_byte_private W aw LB m mo b x HW HbL ltac:(lia) v Hv Hin) as [-> _].
    unfold in_iv, user_iv in Hin. cbn [fst snd] in Hin. rewrite (usz_fake b HF) in Hin. lia. }
  assert (INB : ab_addr b <= x < ab_addr b + ab_size b) by lia.
  split; [intros II; exact (blk_not_IMGX _ _ _ _ _ b x AH HbL (or_introl INB) II)|]. split; lia.
Qed.
Lemma vfl_agree : forall W aw LB m mo (ms' : amem), aw_holds_w W aw LB m mo ->
  (forall b x, visf W b -> ab_addr b + ab_size b - 8 <= x < ab_addr b + ab_size b -> ms' (wa x) = w_ms W (wa x)) ->
  forall b, visf W b -> exists flg, bytes_at asegs ms' (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg.
Proof.
  intros W aw LB m mo ms' HW AG b Vb. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VFL & _).
  destruct (VFL b Vb) as (flg & BA & FL). exists flg. split; [| exact FL].
  eapply bytes_at_agreeN; [exact BA|]. intros x Hx. rewrite length_le8 in Hx. apply (AG b x Vb). lia.
Qed.

Lemma gran_disj : forall A n B k a, 0 <= A -> 0 <= B -> 0 <= n -> 0 <= k -> (A + n <= B \/ B + k <= A) -> A mod 8 = 0 -> B mod 8 = 0 ->
  shad A <= a < shad A + shlen (n + 7) -> shad B <= a < shad B + shlen (k + 7) -> False.
Proof.
  intros A n B k a A0 B0 N0 K0 D A8 B8 H1 H2. unfold shad, shlen, ASHOFF in *. rewrite !Z.shiftr_div_pow2 in * by ulia. change (2^3) with 8 in *.
  destruct D; Z.div_mod_to_equations; ulia.
Qed.
Lemma shlen_le7 : forall n, 0 <= n -> shlen n <= shlen (n + 7).
Proof. intros n N. unfold shlen. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. Z.div_mod_to_equations. ulia. Qed.

Lemma LB_shadow_hull : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> (In b (w_T W) \/ visf W b) ->
  In b (w_LBa W) /\ 0 <= ab_addr b /\ 0 < ab_size b /\ ab_addr b mod 8 = 0.
Proof.
  intros W aw LB m mo b HW HB. pose proof HW as (AH & HT & _).
  assert (Hb : In b (w_LBa W)) by (destruct HB as [HbT|[[Hb _] _]]; [exact (proj1 (HT b HbT))| exact Hb]).
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & A8 & _). destruct (user_app_band _ _ BK NP) as [_ B2].
  split; [exact Hb|]. split; [ulia|]. split; [exact NP| exact A8].
Qed.

Lemma in_twin_clear : forall W aw LB m mo b a, aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) -> in_iv (twin_iv b) a ->
  0 <= a < ATOP + 4096 /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof.
  intros W aw LB m mo b a HW Vb HH NT Ha. pose proof HW as (AH & HT & _). pose proof atop_range as AR. destruct Vb as [Hb NFA].
  destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & BR & _). pose proof BR as (BK & N0 & HI & AL).
  destruct (shadow_tight _ _ BK HI ltac:(ulia)) as [ST1 ST2]. destruct (twin_band _ _ BR N) as (TB1 & TB2 & TB3 & _). unfold in_iv, twin_iv in Ha. cbn [fst snd] in Ha.
  assert (SA : shad ATOP < ATOP + 4096) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by ulia; change (2^3) with 8; Z.div_mod_to_equations; ulia).
  split; [ulia|]. split.
  - intros U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Hva.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b' & Vb' & ->)|[(b' & Hb' & ->)|(b' & Vb' & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b' HW Vb') as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b' HW (or_introl Hb')) as (H1 & H2 & H3 & H4).
      assert (NE : b <> b') by (intros ->; exact (NT Hb')).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb H1 NE) as D.
      exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a ltac:(unfold ablk, AIMG_HI in BK; ulia) H2 ltac:(ulia) ltac:(ulia) D ltac:(clear -AL; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + destruct (LB_shadow_hull W aw LB m mo b' HW (or_intror Vb')) as (H1 & H2 & H3 & H4).
      assert (NE : b <> b') by (intros ->; exact (heap_not_fake _ HH (proj2 Vb'))).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb H1 NE) as D.
      pose proof (shlen_le7 (ab_size b') ltac:(ulia)) as LE.
      exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a ltac:(unfold ablk, AIMG_HI in BK; ulia) H2 ltac:(ulia) ltac:(ulia) D ltac:(clear -AL; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
  - intros X. destruct (IMGX_class a X) as [X1|[X1|X1]]; unfold AIMG_HI in *; ulia.
Qed.

Lemma aw_frame_w_v : forall W A LB m m' mo, aw_holds_w W A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono asegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  exists ms2, aw_holds_w (set_ms W ms2) A LB m' mo.
Proof.
  intros W A LB m m' mo HW AG WM DM. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as AR.
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (st := w_st W) in *. set (LBa := w_LBa W) in *. set (T := w_T W) in *. set (ms := w_ms W) in *.
  set (tw := map twin_iv T) in *. set (FK := List.filter fakeb LBa).

  set (ms2 := fun x : word => if in_ivs_b tw (bv_unsigned x) then ms x else m' x).
  set (ms1 := fun x : word => if bv_unsigned x <? 2^47 then ms2 x else ms x).
  assert (R64 : forall x : word, 0 <= bv_unsigned x < two64).
  { intros x. pose proof (bv_unsigned_in_range 64 x) as R. exact R. }
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).

  assert (KEEP : forall x : word, ~ in_ivs tw (bv_unsigned x) -> bv_unsigned x < ATOP + 4096 -> ~ in_user LB (bv_unsigned x) -> ~ in_ivs IMGX (bv_unsigned x) ->
            ms2 x = ms x).
  { intros x NTW LT NU NI. unfold ms2. replace (in_ivs_b tw (bv_unsigned x)) with false
      by (symmetry; destruct (in_ivs_b tw (bv_unsigned x)) eqn:E; [exfalso; apply NTW; apply in_ivs_b_spec; exact E| reflexivity]).
    pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1. rewrite E1. symmetry. rewrite <- (WAX x). apply AG; [apply R64|].
    split; [pose proof (R64 x); ulia|]. split; assumption. }

  assert (DIFF : forall x : word, ms2 x <> ms x ->
            ATOP + 4096 <= bv_unsigned x \/ in_ivs (map user_iv LBa) (bv_unsigned x) \/ in_ivs (map fsh_iv FK) (bv_unsigned x) \/ in_ivs IMGX (bv_unsigned x)).
  { intros x NE.
    destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW; [exfalso; apply NE; unfold ms2; rewrite TW; reflexivity|].
    assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
    destruct (Z_lt_le_dec (bv_unsigned x) (ATOP + 4096)) as [LT|GE]; [| left; exact GE]. right.
    destruct (in_ivs_b (map user_iv LBa) (bv_unsigned x)) eqn:UB; [left; apply in_ivs_b_spec; exact UB|].
    destruct (in_ivs_b (map fsh_iv FK) (bv_unsigned x)) eqn:FB; [right; left; apply in_ivs_b_spec; exact FB|].
    destruct (in_ivs_b IMGX (bv_unsigned x)) eqn:IB; [right; right; apply in_ivs_b_spec; exact IB|]. exfalso. apply NE.
    apply KEEP; [exact NTW| exact LT| | intros II; apply in_ivs_b_spec in II; congruence].
    intros IU. unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin).
    destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    - assert (X : in_ivs (map user_iv LBa) (bv_unsigned x)) by (apply in_ivs_In; exists (user_iv b); split; [apply in_map; exact (proj1 Vb)| exact Hin]).
      apply in_ivs_b_spec in X. congruence.
    - apply NTW. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact Hb| exact Hin].
    - assert (X : in_ivs (map fsh_iv FK) (bv_unsigned x)).
      { apply in_ivs_In. exists (fsh_iv b). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact (proj1 (proj1 Vb))| apply fakeb_spec; exact (proj2 Vb)]. }
      apply in_ivs_b_spec in X. congruence. }

  assert (AH1 : AHEAP AI L RNG st LBa ms1).
  { eapply (AI_frame AI L RNG st LBa ms ms1 (map to_ivl (map user_iv LBa) ++ map to_ivl (map fsh_iv FK) ++ map to_ivl IMGX ++ [(ATOP + 4096, 2^47)])); [exact AH | | |].
    - intros x OUT. unfold ms1. destruct (bv_unsigned x <? 2^47) eqn:LT; [|reflexivity]. apply Z.ltb_lt in LT.
      destruct (decide (ms2 x = ms x)) as [E|NE]; [exact E| exfalso].
      apply outside_app in OUT as [O1 O234]. apply outside_app in O234 as [O2 O34]. apply outside_app in O34 as [O3 O4]. cbn [outside] in O4.
      rewrite outside_map in O1, O2, O3. destruct (DIFF x NE) as [G|[U|[F|I']]]; [ulia| exact (O1 U)| exact (O2 F)| exact (O3 I')].
    - intros x Hx. destruct (bv_unsigned x <? 2^47) eqn:LT;
        [| rewrite (wview_ext1 ms1 ms x) by (unfold ms1; rewrite LT; reflexivity); exact Hx].
      destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW;
        [rewrite (wview_ext1 ms1 ms x) by (unfold ms1, ms2; rewrite LT, TW; reflexivity); exact Hx|].
      assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
      pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1.
      rewrite (wview_ext1 ms1 m' x) by (unfold ms1, ms2; rewrite LT, TW; reflexivity).
      apply (WM x). rewrite <- (wview_ext1 ms m x E1). exact Hx.
    - apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv). apply in_map_iff in Hv as (b & <- & Hb).
        unfold to_ivl, user_iv. cbn [fst snd]. right. left. exists b. split; [exact Hb|]. ulia.
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv). apply in_map_iff in Hv as (b & <- & Hb).
        apply filter_In in Hb as [Hb FB]. apply fakeb_spec in FB.
        destruct (AI_fake L RNG st LBa ms b AH Hb FB) as (BK & HI & A8 & N8 & NP & _).
        destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (_ & _ & _ & E1 & E2).
        unfold to_ivl, fsh_iv. cbn [fst snd]. right. right.
        replace (shad (ab_addr b) + shlen (ab_size b) - shad (ab_addr b)) with (shlen (ab_size b)) by ulia. rewrite E1, E2.
        right. right. destruct b as [[p|c] F k]; [destruct FB as [d FB]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size]. split; [exact Hb| ulia].
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv).
        destruct (IMGX_aci v Hv) as (R3 & [(r & Hr & R1 & R2)|[(r & Hr & R1 & R2)|(S1 & S2)]]); unfold to_ivl; cbn [fst snd].
        * left. right. left. exists r. split; [exact Hr|]. ulia.
        * right. right. right. left. exists r. split; [exact Hr|]. ulia.
        * right. right. left. ulia.
      + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. left. ulia. }

  assert (AH2 : AHEAP AI L RNG st LBa ms2).
  { eapply (AI_frame_top L RNG st LBa ms1 ms2); [exact AH1 | |].
    - intros a Ha. unfold ms1. unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus; ulia). replace (a <? 2^47) with true by (symmetry; apply Z.ltb_lt; ulia). reflexivity.
    - intros x Hx. destruct (bv_unsigned x <? 2^47) eqn:LT;
        [rewrite <- (wview_ext1 ms1 ms2 x) by (unfold ms1; rewrite LT; reflexivity); exact Hx|].
      rewrite (wview_ext1 ms1 ms x) in Hx by (unfold ms1; rewrite LT; reflexivity).
      destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW;
        [rewrite (wview_ext1 ms2 ms x) by (unfold ms2; rewrite TW; reflexivity); exact Hx|].
      assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
      pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1.
      rewrite (wview_ext1 ms2 m' x) by (unfold ms2; rewrite TW; reflexivity).
      apply (WM x). rewrite <- (wview_ext1 ms m x E1). exact Hx. }
  exists ms2. unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH2|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split.
  { intros a Ha NTW. unfold ms2. unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus, two64 in *; ulia).
    replace (in_ivs_b tw a) with false; [reflexivity|]. symmetry. destruct (in_ivs_b tw a) eqn:E; [| reflexivity]. exfalso. apply NTW. apply in_ivs_b_spec. exact E. }
  split.
  { intros a Ha. pose proof (MAP a Ha) as M0.
    assert (R : 0 <= a < two64 \/ ~ (0 <= a < two64)) by ulia. destruct R as [R|R].
    + unfold wa in *. apply (DM a); [| exact M0]. split; [| exact (proj2 R)].
      apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
      destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI. ulia.
    +   exfalso.
      apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
      destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold two64 in *. ulia. }
  split; [exact ZC0| split; [exact ZCB| split; [exact AC| split; [exact HU| split; [exact CLS| split]]]]].
  -
    apply (vfl_agree W A LB m mo ms2 HW). intros b x Vb Hx.
    destruct (flagw_facts W A LB m mo b x HW Vb Hx) as (XR & NTW & NU & NI & LT & _).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply Z_to_bv_small; unfold bv_modulus, two64 in *; lia).
    apply KEEP; rewrite UX; assumption.
  -
    intros b Vb HH NT g G0 G1. rewrite <- (INC b Vb HH NT g G0 G1). symmetry.
    destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (Nb & BRb & _).
    destruct (in_twin_clear W A LB m mo b (shad (ab_addr b) + g) HW Vb HH NT) as (R1 & NU & NI).
    { unfold in_iv, twin_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. ulia. }
    pose proof atop_range as ATR. apply AG; [unfold two64; ulia|]. split; [exact R1|]. split; [exact NU| exact NI].
Qed.

Lemma aw_frame_w : forall W A LB m m' mo, aw_holds_w W A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  exists ms2, aw_holds_w (set_ms W ms2) A LB m' mo.
Proof.
  intros W A LB m m' mo HW AG DM. apply (aw_frame_w_v W A LB m m' mo HW AG (wmono_of m m' DM)).
  intros a Ha. apply DM. unfold AIMG_HI in Ha. lia.
Qed.

Lemma aw_frame_asan : forall A LB m m' mo, aw_holds_asan A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holds_asan A LB m' mo /\ (forall a, aw_dep_asan LB m' mo a <-> aw_dep_asan LB m mo a).
Proof.
  intros A LB m m' mo [W HW] AG DM. split; [| intros a; reflexivity].
  destruct (aw_frame_w W A LB m m' mo HW AG DM) as [ms2 H2]. exists (set_ms W ms2). exact H2.
Qed.

Lemma aw_dep_ok_asan : forall A LB m mo a, aw_holds_asan A LB m mo -> aw_dep_asan LB m mo a ->
  0 <= a < aw_ceiling_asan mo /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof. intros A LB m mo a _ H. exact H. Qed.

Lemma aw_blocks_ok_asan : forall A LB m mo b, aw_holds_asan A LB m mo -> In b LB ->
  0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= aw_ceiling_asan mo /\ aw_ceiling_asan mo < two64 /\
  (forall a, in_iv b a -> ~ in_ivs IMGX a).
Proof.
  intros A LB m mo v [W HW] Hv. pose proof atop_range as AR. unfold aw_ceiling_asan, two64.
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv].
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 Vb)). left. unfold in_iv, user_iv in Ha. cbn [fst snd] in Ha. ulia.
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & T3). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & HT & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 (HT b Hb))). right. exact Ha.
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & T3 & _). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 (proj1 Vb))). right.
    assert (LE7 : shlen (ab_size b) <= shlen (ab_size b + 7)).
    { destruct (blk_facts _ _ _ _ _ b AH (proj1 (proj1 Vb))) as (NP & _). unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    unfold in_iv, fsh_iv in Ha. cbn [fst snd] in Ha. lia.
Qed.

Lemma wr_at_mapped : forall (ms : amem) A n a, wr_at asegs ms A n -> A <= a < A + n -> 6483968 <= a -> a < two64 -> find_segment asegs a 1 = None ->
  ms (Z_to_bv 64 a) <> None.
Proof.
  intros ms A n a (_ & _ & WR) Ha LO HI SEG. pose proof (WR (a - A) ltac:(ulia)) as W. replace (A + (a - A)) with a in W by ulia.
  unfold wview, wa in W. destruct (ms (Z_to_bv 64 a)); [discriminate|].
  rewrite Z_to_bv_small in W by (unfold bv_modulus, two64 in *; ulia). rewrite SEG in W. congruence.
Qed.

Lemma aw_user_ok_asan : forall A LB m mo b a, aw_holds_asan A LB m mo -> In b LB -> in_iv b a ->
  m (Z_to_bv 64 a) <> None /\ find_segment asegs a 1 = None.
Proof.
  intros A LB m mo v a [W HW] Hv Ha. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & _).
  pose proof atop_range as AR.
  assert (NTWB : 6483968 <= a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> ~ in_ivs (map twin_iv (w_T W)) a).
  { intros _ BA X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
    destruct (LB_twin_facts W A LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. ulia. }
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; unfold in_iv in Ha; cbn [fst snd user_iv twin_iv fsh_iv] in Ha.
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI).
    destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (_ & _ & _ & _ & WR).
    assert (SEG : find_segment asegs a 1 = None) by (apply ref_find_segment_none; ulia).
    split; [| exact SEG].
    assert (R : 0 <= a < two64) by (unfold two64; ulia).
    change (Z_to_bv 64 a) with (wa a). rewrite <- (EQ a R (NTWB ltac:(ulia) ltac:(ulia))). unfold wa.
    apply (wr_at_mapped (w_ms W) (ab_addr b) (ab_size b) a WR ltac:(ulia) ltac:(ulia) ltac:(unfold two64; ulia) SEG).
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _).
    split; [| apply ref_find_segment_none; ulia].
    apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact Hb| exact Ha].
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & T3 & _).
    destruct Vb as [[HbL NFA] HF]. destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (_ & _ & _ & _ & _ & _ & WRS).
    assert (SEG : find_segment asegs a 1 = None) by (apply ref_find_segment_none; ulia).
    split; [| exact SEG].
    assert (R : 0 <= a < two64) by (unfold two64; ulia).

    assert (NTW : ~ in_ivs (map twin_iv (w_T W)) a).
    { intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
      destruct (HT b' Hb') as [Hb'L Hb'H].
      assert (NE : b' <> b) by (intros ->; exact (heap_not_fake b Hb'H HF)).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b' b AH Hb'L HbL NE) as D.
      destruct (heap_block_facts _ _ _ _ _ b' AH Hb'L Hb'H) as (N' & (BK' & N0' & HI' & AL') & _).
      destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      unfold shad, shlen, ASHOFF, ablk, AIMG_HI, KLS, AREQMAX in *. rewrite !Z.shiftr_div_pow2 in * by ulia. change (2^3) with 8 in *.
      destruct D; Z.div_mod_to_equations; ulia. }
    change (Z_to_bv 64 a) with (wa a). rewrite <- (EQ a R NTW). unfold wa.
    apply (wr_at_mapped (w_ms W) _ _ a WRS Ha ltac:(ulia) ltac:(unfold two64; ulia) SEG).
Qed.

Lemma aw_blocks_disj_asan : forall A LB m mo b b' a, aw_holds_asan A LB m mo -> In b LB -> In b' LB -> fst b <> fst b' ->
  in_iv b a -> ~ in_iv b' a.
Proof.
  intros A LB m mo v v' a [W HW] Hv Hv' NE Ha Ha'. pose proof HW as (AH & HT & ND & HFA & NDF & _).

  assert (CL : forall w, In w LB -> in_iv w a ->
            (exists b, vis W b /\ w = user_iv b /\ ab_addr b <= a < ab_addr b + ab_size b /\ (a < 0x7fff8000 \/ 0x10007fff8000 <= a))
         \/ (exists b, In b (w_LBa W) /\ fst w = shad (ab_addr b) /\ shad (ab_addr b) <= a < shad (ab_addr b) + shlen (ab_size b + 7)
                       /\ 0x7fff8000 <= a < 0x10007fff8000 /\ 0 <= ab_addr b /\ 0 < ab_size b /\ ab_addr b mod 8 = 0)).
  { intros w Hw Hin. unfold in_iv in Hin.
    destruct (LB_cases W A LB m mo w HW Hw) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
    - left. exists b. destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI). split; [exact Vb|]. split; [reflexivity|]. split; [ulia| ulia].
    - right. exists b. destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). destruct (LB_shadow_hull W A LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      split; [exact H1|]. split; [reflexivity|]. split; [exact Hin|]. split; [ulia|]. auto.
    - right. exists b. destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & _). destruct (LB_shadow_hull W A LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE. split; [exact H1|]. split; [reflexivity|]. split; [ulia|]. split; [ulia|]. auto. }
  destruct (CL v Hv Ha) as [(b & Vb & -> & R & BA)|(b & Hb & E & R & BA & B0 & BP & B8)];
  destruct (CL v' Hv' Ha') as [(b' & Vb' & -> & R' & BA')|(b' & Hb' & E' & R' & BA' & B0' & BP' & B8')]; try ulia.
  -
    assert (NB : b <> b') by (intros ->; apply NE; reflexivity).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH (proj1 Vb) (proj1 Vb') NB) as D. ulia.
  -
    assert (NB : b <> b') by (intros ->; apply NE; rewrite E, E'; reflexivity).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NB) as D.
    exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a B0 B0' ltac:(ulia) ltac:(ulia) D B8 B8' R R').
Qed.

Lemma aw_ceiling_small_asan : forall mo, aw_ceiling_asan mo <= OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.two62Z.
Proof. intros mo. pose proof atop_range as AR. unfold aw_ceiling_asan. change OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.two62Z with (2^62). ulia. Qed.

Lemma aw_blocks_lo_asan : forall A LB m mo b, aw_holds_asan A LB m mo -> In b LB -> 4096 <= fst b.
Proof.
  intros A LB m mo v [W HW] Hv.
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst user_iv twin_iv fsh_iv].
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (_ & _ & B2 & _). ulia.
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & _). ulia.
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & _). ulia.
Qed.

Definition user_band (A : Z) : Prop := A < 0x7fff8000 \/ 0x10007fff8000 <= A.

Definition set_T (W : wit) (T : list ablock) : wit := mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) T (w_FA W) (w_ms W) (w_zc W).

Lemma twin_mapped_ms : forall L RNG st LBa ms b g, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b ->
  0 <= g -> 8 * g < ab_size b ->
  ms (wa (shad (ab_addr b) + g)) <> None.
Proof.
  intros L RNG st LBa ms [k A n] g AH Hb [p Hp] G0 G1. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (N & BR & _ & _ & (bs & CELL & _) & _).
  destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _).
  destruct CELL as [[[LEN _] (B0 & B1 & BRD)] _]. cbn [ALib.Cells.cells_bytes ALib.Cells.cbytes] in B1, BRD. rewrite app_nil_r in B1, BRD. cbn in LEN.
  assert (GZ : g < shlen (n + 7)) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -G0 G1; Z.div_mod_to_equations; lia).
  assert (GL : (Z.to_nat g < length bs)%nat) by (rewrite LEN; lia).
  specialize (BRD (Z.to_nat g) GL). rewrite Z2Nat.id in BRD by lia.
  rewrite (Shadow.mrd_no_image asegs ms 0x62f000 (2^64) (shad A + g) (RtCells.no_image_asan 0x62f000 (2^64) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) in BRD.
  rewrite BRD. intros E. apply nth_error_None in E. lia.
Qed.
Lemma twin_bytes_sec : forall L RNG st LBa ms b g, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b -> is_primary (ab_size b) = false ->
  0 <= g -> 8 * g < ab_size b ->
  ms (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof.
  intros L RNG st LBa ms [k A n] g AH Hb [p Hp] NP G0 G1. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (_ & _ & _ & _ & (bs & _ & SH) & _). exact (SH NP g G0 G1).
Qed.

Lemma shadow_iv_inj : forall L RNG st LBa ms b b', AHEAP AI L RNG st LBa ms -> In b LBa -> In b' LBa ->
  shad (ab_addr b) = shad (ab_addr b') -> b = b'.
Proof.
  intros L RNG st LBa ms b b' AH Hb Hb' E. destruct (ablock_eq_dec b b') as [EQ|NE]; [exact EQ| exfalso].
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & A8 & _). destruct (blk_facts _ _ _ _ _ b' AH Hb') as (NP' & BK' & HI' & A8' & _).
  destruct (user_app_band _ _ BK NP) as [_ B2]. destruct (user_app_band _ _ BK' NP') as [_ B2'].
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NE) as D.
  unfold shad, ASHOFF in E. rewrite !Z.shiftr_div_pow2 in E by ulia. change (2^3) with 8 in E. destruct D; Z.div_mod_to_equations; ulia.
Qed.

Lemma twin_out_w : forall W aw LB m mo b,
  aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  aw_holds_w (set_T W (b :: w_T W)) aw (twin_iv b :: LB) m mo
  /\ ~ In (twin_iv b) LB
  /\ (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
Proof.
  intros W aw LB m mo b HW Vb HH NT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as AR. destruct Vb as [Hb NFA].
  destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & BR & _). destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _).

  assert (MEQ : forall a, in_iv (twin_iv b) a -> w_ms W (wa a) = m (wa a)).
  { intros a Ha. apply EQ; [unfold in_iv, twin_iv in Ha; cbn [fst snd] in Ha; unfold two64; ulia|].
    intros X. apply in_ivs_In in X as (w & Hw & Hwa). apply in_map_iff in Hw as (b' & <- & Hb'T).
    destruct (HT b' Hb'T) as [Hb'L Hb'H].
    assert (NE : b <> b') by (intros ->; exact (NT Hb'T)).
    destruct (heap_block_facts _ _ _ _ _ b' AH Hb'L Hb'H) as (N' & BR' & _).
    destruct BR as (BK & N0 & HI & AL). destruct BR' as (BK' & N0' & HI' & AL').
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb'L NE) as D.
    unfold in_iv, twin_iv in Ha, Hwa. cbn [fst snd] in Ha, Hwa.
    refine (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a _ _ _ _ D _ _ Ha Hwa); unfold ablk, AIMG_HI, KLS in *; try ulia; Z.div_mod_to_equations; ulia. }
  assert (PAT : forall g, 0 <= g -> 8 * g < ab_size b ->
            m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
  { intros g G0 G1. exact (INC b (conj Hb NFA) HH NT g G0 G1). }
  assert (NIN : ~ In (twin_iv b) LB).
  { intros X. destruct (LB_cases W aw LB m mo _ HW X) as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
    - destruct (LB_user_facts W aw LB m mo b' HW Vb') as (_ & B1 & _). unfold twin_iv, user_iv in E. injection E as E1 E2. ulia.
    - apply NT. replace b with b'; [exact Hb'|]. symmetry. apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb (proj1 (HT b' Hb'))).
      unfold twin_iv in E. injection E as E1 _. exact E1.
    - destruct Vb' as [[Hb'L _] HF']. assert (b = b') as <-; [| exact (heap_not_fake b HH HF')].
      apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb Hb'L). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1. }
  split; [| split; [exact NIN| exact PAT]].
  unfold aw_holds_w, set_T. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split. { intros b0 [<-|Hb0]; [split; [exact Hb| exact HH]| exact (HT b0 Hb0)]. }
  split; [constructor; assumption|]. split; [exact HFA|]. split; [exact NDF|]. split.
  { intros v. cbn [In]. rewrite (HLB v). split.
    - intros [<-|[H|[(b0 & H0 & ->)|H]]]; [right; left; exists b; split; [left; reflexivity| reflexivity]| left; exact H| right; left; exists b0; split; [right; exact H0| reflexivity]| right; right; exact H].
    - intros [H|[(b0 & [<-|H0] & ->)|H]]; [right; left; exact H| left; reflexivity| right; right; left; exists b0; split; [exact H0| reflexivity]| right; right; right; exact H]. }
  split.
  { intros a Ha NTW. apply EQ; [exact Ha|]. intros X. apply NTW. cbn [map]. apply in_ivs_cons. right. exact X. }
  split; [| split; [exact ZC0| split; [exact ZCB| split; [exact AC| split; [exact HU| split; [exact CLS| split; [exact VFL|]]]]]]].
  2:{ intros b0 Vb0 HH0 NT0. apply (INC b0 Vb0 HH0). intros X. apply NT0. right. exact X. }
  intros a Ha. cbn [map] in Ha. apply in_ivs_cons in Ha as [Ha|Ha]; [| exact (MAP a Ha)].
  pose proof Ha as Ha'. unfold in_iv, twin_iv in Ha'. cbn [fst snd] in Ha'.
  assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
  { unfold shlen in Ha'. rewrite Z.shiftr_div_pow2 in Ha' by ulia. change (2^3) with 8 in Ha'. Z.div_mod_to_equations. ulia. }
  pose proof (PAT (a - shad (ab_addr b)) (proj1 G) (proj2 G)) as P. replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia.
  intros X. rewrite X in P. discriminate.
Qed.

Definition aw_realW (aw : word) (LB : blocks) (m : amem) (mo : Model) (W : wit) : Prop := aw_holds_w W aw LB m mo /\ w_ms W = m.

Lemma aw_real_holds : forall aw LB m mo W, aw_realW aw LB m mo W -> aw_holds_asan aw LB m mo.
Proof. intros aw LB m mo W [H _]. exists W. exact H. Qed.

Definition wit_of (W : wit) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) : Prop :=
  w_L W = L /\ w_RNG W = RNG /\ w_st W = st /\ w_LBa W = LBa.
Definition aw_real (aw : word) (LB : blocks) (m : amem) (mo : Model) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) : Prop :=
  exists W, wit_of W L RNG st LBa /\ aw_realW aw LB m mo W.
Lemma wit_of_refl : forall W, wit_of W (w_L W) (w_RNG W) (w_st W) (w_LBa W).
Proof. intros W. repeat split. Qed.
Lemma aw_real_of : forall aw LB m mo W, aw_realW aw LB m mo W -> aw_real aw LB m mo (w_L W) (w_RNG W) (w_st W) (w_LBa W).
Proof. intros aw LB m mo W H. exists W. split; [apply wit_of_refl| exact H]. Qed.
Lemma aw_realW_AHEAP : forall aw LB m mo W, aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m /\ ACCT aw (w_L W) (w_RNG W) (w_st W) (w_LBa W) mo /\ incl UNIV (al_U (w_L W)).
Proof. intros aw LB m mo W [(AH & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & HU & _) EM]. rewrite <- EM. auto. Qed.
Lemma aw_real_AHEAP : forall aw LB m mo L RNG st LBa, aw_real aw LB m mo L RNG st LBa ->
  AHEAP AI L RNG st LBa m /\ ACCT aw L RNG st LBa mo /\ incl UNIV (al_U L).
Proof. intros aw LB m mo L RNG st LBa (W & (<- & <- & <- & <-) & H). exact (aw_realW_AHEAP _ _ _ _ _ H). Qed.

Lemma LB_band : forall W aw LB m mo a, aw_holds_w W aw LB m mo -> in_user LB a ->
  (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP) \/ (0x800bde00 <= a < 0x10007fff8000).
Proof.
  intros W aw LB m mo a HW IU. pose proof HW as (AH & HT & _). pose proof atop_range as AR.
  unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin). unfold in_iv in Hin.
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
  - destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (N0 & BK & TOP & _). unfold ablk, AIMG_HI, KLS in *. ulia.
  - destruct (HT b Hb) as [HbL HH]. destruct (heap_block_facts _ _ _ _ _ b AH HbL HH) as (N & (BK & N0 & HI & AL) & _).
    destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3).
    right; right. split; [| ulia]. unfold ablk, AIMG_HI, KLS in BK. revert Hin. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. intros Hin. Z.div_mod_to_equations. ulia.
  - destruct (blk_facts _ _ _ _ _ b AH (proj1 (proj1 Vb))) as (N0 & BK & TOP & _).
    destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & T3 & T4 & T5).
    right; right. split; [| ulia]. unfold ablk, AIMG_HI, KLS in BK. unfold ASHOFF in T4. ulia.
Qed.

Lemma aw_real_user_band : forall aw LB m mo L RNG st LBa a, aw_real aw LB m mo L RNG st LBa -> in_user LB a ->
  (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP) \/ (0x800bde00 <= a < 0x10007fff8000).
Proof. intros aw LB m mo L RNG st LBa a (W & _ & [HW _]) IU. exact (LB_band W aw LB m mo a HW IU). Qed.

Lemma blk_band : forall L RNG st LBa (m : amem) b x, AHEAP AI L RNG st LBa m -> In b LBa -> ab_addr b <= x < ab_addr b + ab_size b ->
  (AIMG_HI <= x < KLS) \/ (0x10007fff8000 <= x < ATOP).
Proof.
  intros L RNG st LBa m b x AH Hb Hx. destruct (blk_facts _ _ _ _ _ b AH Hb) as (N0 & BK & TOP & _). unfold ablk in BK. ulia.
Qed.

Lemma AHEAP_ext : forall L RNG st LBa (m1 m2 : amem), AHEAP AI L RNG st LBa m1 -> (forall x : word, m2 x = m1 x) -> AHEAP AI L RNG st LBa m2.
Proof.
  intros L RNG st LBa m1 m2 AH E. eapply (AI_frame AI _ _ _ _ m1 m2 []); [exact AH | intros x _; apply E | | apply Forall_nil].
  intros x Hx. rewrite (wview_ext1 m2 m1 x (E x)). exact Hx.
Qed.

Lemma aw_holds_real_w : forall W aw LB m mo,
  aw_holds_w W aw LB m mo ->
  (forall b, In b (w_T W) -> is_primary (ab_size b) = false -> forall g, 0 <= g -> 8 * g < ab_size b ->
     St.rb asegs m (shad (ab_addr b) + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  aw_realW aw LB m mo (set_ms W m).
Proof.
  intros W aw LB m mo HW PAT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as ATR.
  set (patch := fun (l : list ablock) (x : word) => if in_ivs_b (map twin_iv l) (bv_unsigned x) then m x else w_ms W x).
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).

  assert (MAPb : forall b g, In b (w_T W) -> 0 <= g < shlen (ab_size b + 7) -> m (wa (shad (ab_addr b) + g)) <> None).
  { intros b g HbT Hg. apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT| unfold in_iv, twin_iv; cbn [fst snd]; lia]. }
  assert (CH : forall l, (forall b, In b l -> In b (w_T W)) -> AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (patch l)).
  { induction l as [|b l IH]; intros SUB.
    - eapply AHEAP_ext; [exact AH|]. intros x. unfold patch. cbn [map in_ivs_b]. reflexivity.
    - specialize (IH ltac:(intros x Hx; apply SUB; right; exact Hx)).
      assert (HbT : In b (w_T W)) by (apply SUB; left; reflexivity). destruct (HT b HbT) as [HbL HbH].
      destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (Nb & BRb & _).
      assert (OUTS : forall x : word, ~ in_iv (twin_iv b) (bv_unsigned x) -> patch (b :: l) x = patch l x).
      { intros x NIN. unfold patch. cbn [map in_ivs_b]. unfold in_iv in NIN.
        replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct (Z.leb_spec (fst (twin_iv b)) (bv_unsigned x)); [right; apply Z.ltb_ge; lia| left; reflexivity]. }
      assert (INS : forall x : word, in_iv (twin_iv b) (bv_unsigned x) -> patch (b :: l) x = m x).
      { intros x HIN. unfold patch. cbn [map in_ivs_b]. unfold in_iv in HIN.
        replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with true; [reflexivity|].
        symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      destruct (is_primary (ab_size b)) eqn:PRIM.
      +
        destruct b as [[p|c] A n]; [| destruct HbH as [q Hq]; discriminate]. cbn [ab_addr ab_size twin_iv fst snd] in *.
        eapply (AI_frame_twin AI _ _ _ _ (patch l) (patch (HB p A n :: l)) p A n IH HbL PRIM).
        * intros x OUT. cbn [ALib.Frame.outside] in OUT. apply OUTS. unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. lia.
        * intros x Hx. destruct (in_ivs_b [twin_iv (HB p A n)] (bv_unsigned x)) eqn:TW.
          -- apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
             pose proof (INS x TW) as E1. unfold wview. rewrite E1.
             assert (MP : m x <> None).
             { rewrite <- (WAX x). unfold in_iv, twin_iv in TW. cbn [fst snd ab_addr ab_size] in TW.
               replace (bv_unsigned x) with (shad A + (bv_unsigned x - shad A)) by lia. apply (MAPb (HB p A n) _ HbT). cbn [ab_addr ab_size]. lia. }
             destruct (m x); [discriminate| contradiction].
          -- assert (NIN : ~ in_iv (twin_iv (HB p A n)) (bv_unsigned x)).
             { intros X. assert (Y : in_ivs [twin_iv (HB p A n)] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
             rewrite (wview_ext1 (patch (HB p A n :: l)) (patch l) x (OUTS x NIN)). exact Hx.
        * intros i Hi. rewrite (INS (wa (shad A + i))).
          -- apply (MAPb (HB p A n) i HbT). cbn [ab_size]. exact Hi.
          -- unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. rewrite UWA by lia. lia.
      +
        eapply AHEAP_ext; [exact IH|]. intros x.
        destruct (in_ivs_b [twin_iv b] (bv_unsigned x)) eqn:TW.
        * apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
          rewrite (INS x TW). pose proof TW as TW'. unfold in_iv, twin_iv in TW'. cbn [fst snd] in TW'.
          assert (G : 0 <= bv_unsigned x - shad (ab_addr b) /\ 8 * (bv_unsigned x - shad (ab_addr b)) < ab_size b).
          { unfold shlen in TW'. rewrite Z.shiftr_div_pow2 in TW' by ulia. change (2^3) with 8 in TW'. Z.div_mod_to_equations. ulia. }
          pose proof (twin_bytes_sec _ _ _ _ _ b _ IH HbL HbH PRIM (proj1 G) (proj2 G)) as P2.
          pose proof (PAT b HbT PRIM _ (proj1 G) (proj2 G)) as P1.
          replace (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) with (bv_unsigned x) in P1, P2 by ulia.
          rewrite WAX in P2. unfold St.rb in P1. rewrite Z_to_bv_bv_unsigned in P1.
          assert (MP : m x <> None).
          { rewrite <- (WAX x). replace (bv_unsigned x) with (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) by lia. apply (MAPb b _ HbT). lia. }
          destruct (m x) as [y|]; [congruence| contradiction].
        * apply OUTS. intros X. assert (Y : in_ivs [twin_iv b] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
  assert (PW : forall x : word, m x = patch (w_T W) x).
  { intros x. unfold patch. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with two64 in R.
    destruct (in_ivs_b (map twin_iv (w_T W)) (bv_unsigned x)) eqn:TW; [reflexivity|].
    assert (NTW : ~ in_ivs (map twin_iv (w_T W)) (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
    pose proof (EQ (bv_unsigned x) R NTW) as E1. rewrite WAX in E1. congruence. }
  split; [| reflexivity].
  unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split. { eapply AHEAP_ext; [exact (CH (w_T W) (fun b H => H))| exact PW]. }
  split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|]. split; [exact MAP|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC| split; [exact HU| split; [exact CLS| split; [| exact INC]]]].

  apply (vfl_agree W aw LB m mo m HW). intros b x [[HbL NFA] HF] Hx.
  destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
  destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
  symmetry. apply EQ; [unfold two64; lia|].
  intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
  destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. lia.
Qed.

Definition patch1 (W : wit) (m : amem) (b : ablock) : amem := fun x => if in_ivs_b [twin_iv b] (bv_unsigned x) then m x else w_ms W x.
Definition wit_twin_in (W : wit) (m : amem) (b : ablock) : wit :=
  mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (lb_del b (w_T W)) (w_FA W) (patch1 W m b) (w_zc W).

Lemma twin_in_w : forall W aw LB m mo b,
  aw_holds_w W aw LB m mo -> In b (w_T W) ->
  (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  aw_holds_w (wit_twin_in W m b) aw (List.remove iv_eq_dec (twin_iv b) LB) m mo.
Proof.
  intros W aw LB m mo b HW HbT PAT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as ATR. destruct (HT b HbT) as [HbL HbH].
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (Nb & BRb & _).
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).
  assert (MAPb : forall g, 0 <= g < shlen (ab_size b + 7) -> m (wa (shad (ab_addr b) + g)) <> None).
  { intros g Hg. apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT| unfold in_iv, twin_iv; cbn [fst snd]; lia]. }
  assert (OUTS : forall x : word, ~ in_iv (twin_iv b) (bv_unsigned x) -> patch1 W m b x = w_ms W x).
  { intros x NIN. unfold patch1. cbn [in_ivs_b]. unfold in_iv in NIN.
    replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z.leb_spec (fst (twin_iv b)) (bv_unsigned x)); [right; apply Z.ltb_ge; lia| left; reflexivity]. }
  assert (INS : forall x : word, in_iv (twin_iv b) (bv_unsigned x) -> patch1 W m b x = m x).
  { intros x HIN. unfold patch1. cbn [in_ivs_b]. unfold in_iv in HIN.
    replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  assert (AH' : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (patch1 W m b)).
  { destruct (is_primary (ab_size b)) eqn:PRIM.
    - destruct b as [[p|c] A n]; [| destruct HbH as [q Hq]; discriminate]. cbn [ab_addr ab_size twin_iv fst snd] in *.
      eapply (AI_frame_twin AI _ _ _ _ (w_ms W) (patch1 W m (HB p A n)) p A n AH HbL PRIM).
      + intros x OUT. cbn [ALib.Frame.outside] in OUT. apply OUTS. unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. lia.
      + intros x Hx. destruct (in_ivs_b [twin_iv (HB p A n)] (bv_unsigned x)) eqn:TW.
        * apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
          pose proof (INS x TW) as E1. unfold wview. rewrite E1.
          assert (MP : m x <> None).
          { rewrite <- (WAX x). unfold in_iv, twin_iv in TW. cbn [fst snd ab_addr ab_size] in TW.
            replace (bv_unsigned x) with (shad A + (bv_unsigned x - shad A)) by lia. apply MAPb. lia. }
          destruct (m x); [discriminate| contradiction].
        * assert (NIN : ~ in_iv (twin_iv (HB p A n)) (bv_unsigned x)).
          { intros X. assert (Y : in_ivs [twin_iv (HB p A n)] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
          rewrite (wview_ext1 (patch1 W m (HB p A n)) (w_ms W) x (OUTS x NIN)). exact Hx.
      + intros i Hi. rewrite (INS (wa (shad A + i))).
        * apply MAPb. exact Hi.
        * unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. rewrite UWA by lia. lia.
    - eapply AHEAP_ext; [exact AH|]. intros x.
      destruct (in_ivs_b [twin_iv b] (bv_unsigned x)) eqn:TW.
      + apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
        rewrite (INS x TW). pose proof TW as TW'. unfold in_iv, twin_iv in TW'. cbn [fst snd] in TW'.
        assert (G : 0 <= bv_unsigned x - shad (ab_addr b) /\ 8 * (bv_unsigned x - shad (ab_addr b)) < ab_size b).
        { unfold shlen in TW'. rewrite Z.shiftr_div_pow2 in TW' by ulia. change (2^3) with 8 in TW'. Z.div_mod_to_equations. ulia. }
        pose proof (twin_bytes_sec _ _ _ _ _ b _ AH HbL HbH PRIM (proj1 G) (proj2 G)) as P2.
        pose proof (PAT _ (proj1 G) (proj2 G)) as P1.
        replace (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) with (bv_unsigned x) in P1, P2 by ulia.
        rewrite WAX in P1, P2. congruence.
      + apply OUTS. intros X. assert (Y : in_ivs [twin_iv b] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
  assert (TIN : forall a, in_ivs (map twin_iv (w_T W)) a -> in_iv (twin_iv b) a \/ in_ivs (map twin_iv (lb_del b (w_T W))) a).
  { intros a X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
    destruct (ablock_eq_dec b' b) as [->|NE]; [left; exact Hin| right]. apply in_ivs_In. exists (twin_iv b'). split; [| exact Hin].
    apply in_map. apply lb_del_In. split; assumption. }
  unfold aw_holds_w, wit_twin_in. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|].
  split. { intros b0 Hb0. apply lb_del_In in Hb0 as [Hb0 _]. exact (HT b0 Hb0). }
  split. { unfold lb_del. apply List.NoDup_filter. exact ND. }
  split; [exact HFA|]. split; [exact NDF|].
  split.
  { intros v. split.
    - intros Hv. apply in_remove in Hv as [Hv NEv]. apply HLB in Hv as [H|[(b0 & H0 & ->)|H]]; [left; exact H| | right; right; exact H].
      right; left. exists b0. split; [| reflexivity]. apply lb_del_In. split; [exact H0|]. intros ->. apply NEv. reflexivity.
    - intros H. apply in_in_remove.
      + destruct H as [(b0 & Vb0 & ->)|[(b0 & Hb0 & ->)|(b0 & Vb0 & ->)]].
        * destruct (LB_user_facts W aw LB m mo b0 HW Vb0) as (U0 & B1 & _). pose proof (usz_le b0) as UL. unfold twin_iv, user_iv. intros E. injection E as E1 _. ulia.
        * apply lb_del_In in Hb0 as [Hb0 NE]. intros E. apply NE. apply (shadow_iv_inj _ _ _ _ _ b0 b AH (proj1 (HT b0 Hb0)) HbL).
          unfold twin_iv in E. injection E as E1 _. exact E1.
        * destruct Vb0 as [[Hb0L _] HF0]. intros E. assert (b0 = b) as ->; [| exact (heap_not_fake b HbH HF0)].
          apply (shadow_iv_inj _ _ _ _ _ b0 b AH Hb0L HbL). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1.
      + apply HLB. destruct H as [H|[(b0 & Hb0 & ->)|H]]; [left; exact H| | right; right; exact H].
        right; left. exists b0. split; [| reflexivity]. apply lb_del_In in Hb0 as [Hb0 _]. exact Hb0. }
  split.
  { intros a Ha NTW. destruct (in_ivs_b [twin_iv b] a) eqn:TW.
    - apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW]. apply INS. rewrite UWA by (unfold two64 in Ha; lia). exact TW.
    - assert (NIN : ~ in_iv (twin_iv b) a).
      { intros X. assert (Y : in_ivs [twin_iv b] a) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
      rewrite OUTS by (rewrite UWA by (unfold two64 in Ha; lia); exact NIN). apply EQ; [exact Ha|].
      intros X. destruct (TIN a X) as [Y|Y]; [exact (NIN Y)| exact (NTW Y)]. }
  split.
  { intros a Ha. apply MAP. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb'). apply lb_del_In in Hb' as [Hb' _].
    apply in_ivs_In. exists (twin_iv b'). split; [apply in_map; exact Hb'| exact Hin]. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC|]. split; [exact HU|]. split; [exact CLS|]. split.
  -
    apply (vfl_agree W aw LB m mo (patch1 W m b) HW). intros b0 x [[Hb0L NFA0] HF0] Hx.
    destruct (AI_fake _ _ _ _ _ b0 AH Hb0L HF0) as (BK0 & HI0 & A80 & N80 & NP0 & _).
    destruct (user_app_band _ _ BK0 ltac:(lia)) as [B1 B2].
    apply OUTS. rewrite UWA by lia. unfold in_iv, twin_iv. cbn [fst snd]. lia.
  - intros b0 Vb0 HH0 NT0. destruct (ablock_eq_dec b0 b) as [->|NE]; [exact PAT|].
    apply (INC b0 Vb0 HH0). intros X. apply NT0. apply lb_del_In. split; assumption.
Qed.

Lemma shad_band_sep : forall s a, 0x7fff8000 <= s < 0x10007fff8000 -> 0 <= a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> shad s <> shad a.
Proof. intros s a S A0 B. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. Z.div_mod_to_equations. ulia. Qed.

Lemma twin_owner_w : forall W aw LB m mo b A' n',
  aw_holds_w W aw LB m mo -> In b (w_T W) -> In (A', n') LB -> shad A' = shad (ab_addr b) ->
  A' = ab_addr b /\ n' = ab_size b /\ 1 <= ab_size b <= AREQMAX.
Proof.
  intros W aw LB m mo b A' n' HW HbT H' SH. pose proof HW as (AH & HT & _). pose proof atop_range as AR.
  destruct (HT b HbT) as [Hb HH]. destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & (BK & _) & _).
  destruct (user_app_band _ _ BK ltac:(ulia)) as [B1 B2].
  destruct (LB_cases W aw LB m mo _ HW H') as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
  - unfold user_iv in E. injection E as -> ->. rewrite (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 Vb') Hb SH). rewrite (usz_heap b HH). auto.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & T3). unfold twin_iv in E. injection E as -> _.
    apply (shad_band_sep (shad (ab_addr b')) (ab_addr b)); [ulia| ulia| ulia| exact SH].
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & T3 & _). unfold fsh_iv in E. injection E as -> _.
    apply (shad_band_sep (shad (ab_addr b')) (ab_addr b)); [ulia| ulia| ulia| exact SH].
Qed.

Lemma LB_same_addr : forall W aw LB m mo A0 n0 n1, aw_holds_w W aw LB m mo -> In (A0, n0) LB -> In (A0, n1) LB -> n0 = n1.
Proof.
  intros W aw LB m mo A0 n0 n1 HW H0 H1. pose proof HW as (AH & HT & _ & HFA & _). pose proof atop_range as AR.
  assert (SAME : forall b b', In b (w_LBa W) -> In b' (w_LBa W) -> ab_addr b = ab_addr b' -> b = b').
  { intros b b' Hb Hb' EA. apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb Hb'). rewrite EA. reflexivity. }
  destruct (LB_cases W aw LB m mo _ HW H0) as [(b & Vb & E)|[(b & Hb & E)|(b & Vb & E)]];
  destruct (LB_cases W aw LB m mo _ HW H1) as [(b' & Vb' & E')|[(b' & Hb' & E')|(b' & Vb' & E')]];
    unfold user_iv, twin_iv, fsh_iv in E, E'; injection E as EA EN; injection E' as EA' EN'.
  all: try (destruct (LB_user_facts W aw LB m mo b HW Vb) as (? & ? & ? & ?)); try (destruct (LB_user_facts W aw LB m mo b' HW Vb') as (? & ? & ? & ?)).
  all: try (destruct (LB_twin_facts W aw LB m mo b HW Hb) as (? & ? & ?)); try (destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (? & ? & ?)).
  all: try (destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (? & ? & ? & ? & ?)); try (destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (? & ? & ? & ? & ?)).
  all: try ulia.
  - rewrite (SAME b b' (proj1 Vb) (proj1 Vb') ltac:(congruence)) in EN. congruence.
  - assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (HT b' Hb'))); congruence). congruence.
  - exfalso. assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (proj1 Vb'))); congruence).
    exact (heap_not_fake b (proj2 (HT b Hb)) (proj2 Vb')).
  - exfalso. assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (HT b' Hb'))); congruence).
    exact (heap_not_fake b (proj2 (HT b Hb')) (proj2 Vb)).
  - assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (proj1 Vb'))); congruence). congruence.
Qed.

Lemma twin_T_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> In b (w_T W) ->
  In b (w_LBa W) /\ vis W b /\ In (user_iv b) LB /\ In (twin_iv b) LB /\ (exists p, b = HB p (ab_addr b) (ab_size b))
  /\ 1 <= ab_size b <= AREQMAX /\ ab_addr b mod 16 = 0 /\ user_band (ab_addr b) /\ ~ user_band (shad (ab_addr b)).
Proof.
  intros W aw LB m mo b HW HbT. pose proof HW as (AH & HT & _ & HFA & _ & HLB & _). destruct (HT b HbT) as [HbL HH].
  assert (VB : vis W b) by (split; [exact HbL| intros X; exact (heap_not_fake b HH (proj2 (HFA b X)))]).
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HH) as (N & (BK & _ & _ & AL) & _).
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3). destruct (user_app_band _ _ BK ltac:(ulia)) as [B1 B2].
  split; [exact HbL|]. split; [exact VB|].
  split; [apply HLB; left; exists b; split; [exact VB| reflexivity]|].
  split; [apply HLB; right; left; exists b; split; [exact HbT| reflexivity]|].
  split. { destruct b as [[q|c] A n]; [exists q; reflexivity| destruct HH as [q Hq]; discriminate]. }
  split; [exact N|]. split; [exact AL|]. split; [unfold user_band; ulia| unfold user_band; ulia].
Qed.

Lemma twin_container : forall W aw LB m mo b v, aw_holds_w W aw LB m mo -> In b (w_T W) -> In v LB ->
  (forall a, in_iv (twin_iv b) a -> in_iv v a) -> v = twin_iv b.
Proof.
  intros W aw LB m mo b v HW HbT Hv SUB. destruct (twin_T_facts W aw LB m mo b HW HbT) as (_ & _ & _ & HTW & _).
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  assert (WNE : in_iv (twin_iv b) (shad (ab_addr b))) by (unfold in_iv, twin_iv; cbn [fst snd]; ulia).
  destruct v as [Av nv]. destruct (Z.eq_dec Av (shad (ab_addr b))) as [->|NA].
  - unfold twin_iv. f_equal. exact (LB_same_addr W aw LB m mo _ _ _ HW Hv HTW).
  - exfalso. apply (aw_blocks_disj_asan aw LB m mo (Av, nv) (twin_iv b) (shad (ab_addr b)) (ex_intro _ W HW) Hv HTW); [cbn [fst twin_iv]; exact NA| exact (SUB _ WNE)| exact WNE].
Qed.

Lemma LB_classify : forall W aw LB m mo, aw_holds_w W aw LB m mo ->
     (forall v, In v LB -> user_band (fst v) -> 0 < snd v -> exists b, vis W b /\ v = user_iv b)
  /\ (forall v, In v LB -> ~ user_band (fst v) -> (exists b, In b (w_T W) /\ v = twin_iv b) \/ (exists b, visf W b /\ v = fsh_iv b)).
Proof.
  intros W aw LB m mo HW. split.
  - intros v Hv UB P. destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    + exists b. split; [exact Vb| reflexivity].
    + exfalso. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). unfold user_band, twin_iv in UB. cbn [fst] in UB. ulia.
    + exfalso. destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & T3 & _). unfold user_band, fsh_iv in UB. cbn [fst] in UB. ulia.
  - intros v Hv NUB. destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    + exfalso. apply NUB. destruct (LB_user_facts W aw LB m mo b HW Vb) as (P & B1 & _). unfold user_band, user_iv. cbn [fst]. ulia.
    + left. exists b. split; [exact Hb| reflexivity].
    + right. exists b. split; [exact Vb| reflexivity].
Qed.

Lemma hb_unique : forall L RNG st LBa m b b' p, AHEAP AI L RNG st LBa m -> In b LBa -> In b' LBa ->
  ab_kind b = ABHeap p -> ab_kind b' = ABHeap p -> b = b'.
Proof.
  intros L RNG st LBa m b b' p AH Hb Hb' K K'. pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND. clear AH.
  induction LBa as [|x l IH]; [destruct Hb|]. cbn [hb_ids flat_map] in ND.
  assert (INID : forall y, In y l -> ab_kind y = ABHeap p -> In p (hb_ids l)).
  { intros y Hy Ky. unfold hb_ids. apply in_flat_map. exists y. split; [exact Hy|]. rewrite Ky. left. reflexivity. }
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
  - reflexivity.
  - exfalso. rewrite K in ND. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID b' Hb' K')).
  - exfalso. rewrite K' in ND. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID b Hb K)).
  - apply IH; [exact Hb| exact Hb'|]. destruct (ab_kind x); cbn [app] in ND; [apply NoDup_cons_iff in ND as [_ ND]; exact ND| exact ND].
Qed.

Lemma lb_remove_In : forall L RNG st LBa m p A n b, AHEAP AI L RNG st LBa m -> In (HB p A n) LBa ->
  (In b (lb_remove p LBa) <-> (In b LBa /\ b <> HB p A n)).
Proof.
  intros L RNG st LBa m p A n b AH HP. rewrite AFreeRep.In_lb_remove. split.
  - intros [Hb NK]. split; [exact Hb|]. intros ->. apply NK. reflexivity.
  - intros [Hb NE]. split; [exact Hb|]. intros K. apply NE. exact (hb_unique L RNG st LBa m b (HB p A n) p AH Hb HP K eq_refl).
Qed.

Definition LB_free (LB : blocks) (A n : Z) : blocks := List.remove iv_eq_dec (shad A, shlen (n + 7)) (List.remove iv_eq_dec (A, n) LB).

Lemma LB_free_In : forall LB A n v, In v (LB_free LB A n) <-> (In v LB /\ v <> (A, n) /\ v <> (shad A, shlen (n + 7))).
Proof.
  intros LB A n v. unfold LB_free. split.
  - intros H. apply in_remove in H as [H N2]. apply in_remove in H as [H N1]. auto.
  - intros (H & N1 & N2). apply in_in_remove; [exact N2|]. apply in_in_remove; [exact N1| exact H].
Qed.

Lemma lb_remove_fake : forall p LBa b, In b LBa -> is_fake b -> In b (lb_remove p LBa).
Proof. intros p LBa b Hb [c K]. apply AFreeRep.In_lb_remove. split; [exact Hb|]. rewrite K. discriminate. Qed.

Lemma vfl_keep : forall W aw LB m mo (m' : amem), aw_realW aw LB m mo W ->
  (forall b x, visf W b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  forall b, visf W b -> exists flg, bytes_at asegs m' (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg.
Proof.
  intros W aw LB m mo m' [HW EM] KEEPF. apply (vfl_agree W aw LB m mo m' HW). intros b x Vb Hx.
  pose proof HW as (AH & _). pose proof Vb as [[HbL _] HF]. destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (_ & _ & _ & _ & N64 & _).
  rewrite EM. apply (KEEPF b x Vb). lia.
Qed.
Lemma pres_block : forall LBp sp (m m' : amem) b x, aheap_pres (aci AI) LBp sp m m' -> In b LBp -> 0 <= ab_addr b -> ab_addr b + ab_size b <= 2^64 ->
  ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x).
Proof.
  intros LBp sp m m' b x PRES Hb A0 AH Hx. apply (proj1 (PRES x ltac:(lia) ltac:(right; right; left; exists b; split; [exact Hb| lia]))).
Qed.

Lemma twin_keep : forall L RNG' st' LBa' (m m' : amem) LBx b,
  AHEAP AI L RNG' st' LBa' m' -> In b LBa' -> is_heap b -> twins_pres LBx m m' -> In b LBx ->
  (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  forall g, 0 <= g -> 8 * g < ab_size b -> m' (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof.
  intros L RNG' st' LBa' m m' LBx b AH' Hb' HH TW HbX OLD g G0 G1.
  destruct (is_primary (ab_size b)) eqn:PRIM; [| exact (twin_bytes_sec _ _ _ _ _ b g AH' Hb' HH PRIM G0 G1)].
  destruct b as [[p|c] A n]; [| destruct HH as [q Hq]; discriminate]. cbn [ab_addr ab_size] in *.
  rewrite (TW p A n HbX PRIM g); [exact (OLD g G0 G1)|].
  unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia.
Qed.

Lemma twins_pres_band : forall L RNG st LBa (m m' : amem), AHEAP AI L RNG st LBa m ->
  (forall a, 0x800bde00 <= a < shad ATOP -> m' (wa a) = m (wa a)) -> twins_pres LBa m m'.
Proof.
  intros L RNG st LBa m m' AH OUT p A n Hin PR i Hi.
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH Hin ltac:(exists p; reflexivity)) as (N & (BK & N0 & HI & AL) & _). cbn [ab_addr ab_size] in *.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. apply OUT. lia.
Qed.

Lemma aw_real_malloc : forall aw aw' LB m mo W RNG' st' p A n m' mo' sp,
  aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) RNG' st' (HB p A n :: w_LBa W) m' -> ACCT aw' (w_L W) RNG' st' (HB p A n :: w_LBa W) mo' ->
  aheap_pres (aci AI) (w_LBa W) sp m m' ->
  twins_pres (w_LBa W) m m' -> ablock_shadow m' A n ->
  let W1 := mkWit (w_L W) RNG' st' (HB p A n :: w_LBa W) (w_T W) (w_FA W) m' (w_zc W) in
  aw_realW aw' ((A, n) :: LB) m' mo' W1 /\ vis W1 (HB p A n) /\ ~ In (HB p A n) (w_T W)
  /\ user_band A /\ (forall a, in_iv (A, n) a -> ~ in_user LB a) /\ (forall a, in_iv (shad A, shlen (n + 7)) a -> ~ in_user LB a).
Proof.
  intros aw aw' LB m mo W RNG' st' p A n m' mo' sp [HW EM] AH' AC' PRES TW PATN W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH' ltac:(left; reflexivity) ltac:(exists p; reflexivity)) as (NN & BRN & _). cbn [ab_addr ab_size] in NN, BRN.
  destruct (twin_band _ _ BRN NN) as (TN1 & TN2 & TN3 & _). pose proof BRN as (BKN & _ & HIN & ALN).
  destruct (user_app_band _ _ BKN ltac:(ulia)) as [BN1 BN2].
  assert (DISJ : forall b, In b (w_LBa W) -> A + n <= ab_addr b \/ ab_addr b + ab_size b <= A).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p A n) b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  assert (NT : ~ In (HB p A n) (w_T W)) by (intros X; exact (NIN (proj1 (HT _ X)))).
  assert (NFA : ~ In (HB p A n) (w_FA W)) by (intros X; exact (NIN (proj1 (HFA _ X)))).

  assert (HW1 : aw_holds_w W1 aw' ((A, n) :: LB) m' mo').
  { unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
    split; [exact AH'|]. split. { intros b Hb. destruct (HT b Hb) as [H1 H2]. split; [right; exact H1| exact H2]. }
    split; [exact ND|]. split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [right; exact H1| exact H2]. }
    split; [exact NDF|]. split.
    { intros v. cbn [In]. rewrite (HLB v). unfold vis, visf. cbn [w_LBa w_FA]. split.
      - intros [<-|[(b & [Hb NF] & ->)|[H|(b & [[Hb NF] HF] & ->)]]].
        + left. exists (HB p A n). split; [split; [left; reflexivity| exact NFA]| reflexivity].
        + left. exists b. split; [split; [right; exact Hb| exact NF]| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [split; [right; exact Hb| exact NF]| exact HF]| reflexivity].
      - intros [(b & [[<-|Hb] NF] & ->)|[H|(b & [[[<-|Hb] NF] HF] & ->)]].
        + left. reflexivity.
        + right. left. exists b. split; [split; assumption| reflexivity].
        + right. right. left. exact H.
        + exfalso. exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) HF).
        + right. right. right. exists b. split; [split; [split; assumption| exact HF]| reflexivity]. }
    split; [intros a _ _; reflexivity|].
    split.
    {
      intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT).
      destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
      pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(right; exact HbL) HbH (proj1 G) (proj2 G)) as P.
      replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
    split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [exfalso; exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) FK)| exact (CLS b Hb FK)]. }
    split.
    2:{
        intros b [[<-|HbL] NFAb] HHb NTb; [exact PATN|].
        apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(right; exact HbL) HHb TW HbL).
        intros g G0 G1. exact (INC b (conj HbL NFAb) HHb NTb g G0 G1). }

    intros b [[[<-|HbL] NFAb] FKb]; [exfalso; exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) FKb)|].
    assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] _] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block (w_LBa W) sp m m' b0 x PRES Hb0); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [left; reflexivity| exact NFA]|]. split; [exact NT|].
  split; [unfold user_band; ulia|]. split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b (proj1 Vb)). ulia.
    + destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & _). ulia.
  -
    intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b HW Vb) as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj A n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b H1) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj A n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b H1) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
Qed.

Lemma aw_real_free : forall aw aw' LB m mo W RNG' st' p A n m' mo' sp,
  aw_realW aw LB m mo W -> In (HB p A n) (w_LBa W) ->
  AHEAP AI (w_L W) RNG' st' (lb_remove p (w_LBa W)) m' -> ACCT aw' (w_L W) RNG' st' (lb_remove p (w_LBa W)) mo' ->
  aheap_pres (aci AI) (lb_remove p (w_LBa W)) sp m m' ->
  twins_pres (lb_remove p (w_LBa W)) m m' ->
  let W1 := mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W))
                  (w_FA W) m' (w_zc W) in
  aw_realW aw' (LB_free LB A n) m' mo' W1.
Proof.
  intros aw aw' LB m mo W RNG' st' p A n m' mo' sp [HW EM] HP AH' AC' PRES TW W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A n)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A n b AH HP)).
  set (T' := List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W)) in *.
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A n).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A n)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH HP ltac:(exists p; reflexivity)) as (NP & BRP & _). cbn [ab_addr ab_size] in NP, BRP.
  destruct (twin_band _ _ BRP NP) as (TP1 & TP2 & TP3 & _). pose proof BRP as (BKP & _). destruct (user_app_band _ _ BKP ltac:(ulia)) as [BP1 BP2].
  assert (SAMESH : forall b, In b (w_LBa W) -> shad (ab_addr b) = shad A -> b = HB p A n).
  { intros b Hb E. apply (shadow_iv_inj _ _ _ _ _ b (HB p A n) AH Hb HP). exact E. }
  split; [| reflexivity].
  unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc]. fold T'.
  split; [exact AH'|].
  split. { intros b Hb. apply INT' in Hb as [Hb NE]. destruct (HT b Hb) as [H1 H2]. split; [apply RM; split; assumption| exact H2]. }
  split; [apply NoDup_filter; exact ND|].
  split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [exact (lb_remove_fake p _ b H1 H2)| exact H2]. }
  split; [exact NDF|]. split.
  { intros v. rewrite LB_free_In. unfold vis, visf. cbn [w_LBa w_FA]. split.
    - intros (Hv & N1 & N2). destruct (LB_cases W aw LB m mo v HW Hv) as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + left. exists b. split; [| reflexivity]. split; [| exact NF]. apply RM. split; [exact Hb|]. intros ->. apply N1. reflexivity.
      + right. left. exists b. split; [| reflexivity]. apply INT'. split; [exact Hb|]. intros ->. apply N2. reflexivity.
      + right. right. exists b. split; [| reflexivity]. split; [split; [exact (lb_remove_fake p _ b Hb HF)| exact NF]| exact HF].
    - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + apply RM in Hb as [Hb NE]. split; [apply HLB; left; exists b; split; [split; assumption| reflexivity]|].
        destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (NPb & B1 & B2 & _). split.
        * intros X. unfold user_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact Hb| rewrite X1; reflexivity].
        * intros X. unfold user_iv in X. injection X as X1 _. ulia.
      + apply INT' in Hb as [Hb NE]. split; [apply HLB; right; left; exists b; split; [exact Hb| reflexivity]|].
        destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). split.
        * intros X. unfold twin_iv in X. injection X as X1 _. ulia.
        * intros X. unfold twin_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact (proj1 (HT b Hb))| exact X1].
      + assert (HbL : In b (w_LBa W)) by (apply RM in Hb; tauto).
        split; [apply HLB; right; right; exists b; split; [split; [split; assumption| exact HF]| reflexivity]|].
        destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj HbL NF) HF)) as (T1 & T2 & T3 & _). split.
        * intros X. unfold fsh_iv in X. injection X as X1 _. ulia.
        * intros X. unfold fsh_iv in X. injection X as X1 _. pose proof (SAMESH b HbL X1) as ->. exact (heap_not_fake (HB p A n) (ex_intro _ p eq_refl) HF). }
  split; [intros a _ _; reflexivity|].
  split.
  { intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT). apply INT' in HbT as [HbT NE].
    destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
    unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
    assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
    { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
    pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(apply RM; split; assumption) HbH (proj1 G) (proj2 G)) as P.
    replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
  split. { intros b Hb FK. exact (CLS b (proj1 (proj1 (RM b) Hb)) FK). }
  split.
  2:{
      intros b [HbR NFAb] HHb NTb. pose proof (proj1 (RM b) HbR) as [HbL NEb].
      apply (twin_keep _ _ _ _ m m' (lb_remove p (w_LBa W)) b AH' HbR HHb TW HbR).
      intros g G0 G1. apply (INC b (conj HbL NFAb) HHb); [| exact G0| exact G1].
      intros X. apply NTb. apply INT'. split; [exact X| exact NEb]. }

  intros b [[HbR NFAb] FKb]. apply RM in HbR as [HbL _].
  assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
  apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] FK0] Hx.
  destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
  apply (pres_block (lb_remove p (w_LBa W)) sp m m' b0 x PRES (lb_remove_fake p _ b0 Hb0 FK0)); [ulia| ulia| exact Hx].
Qed.

Lemma LB_free_char : forall W aw LB m mo p A n, aw_holds_w W aw LB m mo -> In (HB p A n) (w_LBa W) ->
  let T' := List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W) in
  forall v, In v (LB_free LB A n) <->
       (exists b, (In b (lb_remove p (w_LBa W)) /\ ~ In b (w_FA W)) /\ v = user_iv b)
    \/ (exists b, In b T' /\ v = twin_iv b)
    \/ (exists b, ((In b (lb_remove p (w_LBa W)) /\ ~ In b (w_FA W)) /\ is_fake b) /\ v = fsh_iv b).
Proof.
  intros W aw LB m mo p A n HW HP T'.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A n)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A n b AH HP)).
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A n).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A n)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH HP ltac:(exists p; reflexivity)) as (NP & BRP & _). cbn [ab_addr ab_size] in NP, BRP.
  destruct (twin_band _ _ BRP NP) as (TP1 & TP2 & TP3 & _). pose proof BRP as (BKP & _). destruct (user_app_band _ _ BKP ltac:(ulia)) as [BP1 BP2].
  assert (SAMESH : forall b, In b (w_LBa W) -> shad (ab_addr b) = shad A -> b = HB p A n).
  { intros b Hb E. apply (shadow_iv_inj _ _ _ _ _ b (HB p A n) AH Hb HP). exact E. }
  intros v. rewrite LB_free_In. split.
  - intros (Hv & N1 & N2). destruct (LB_cases W aw LB m mo v HW Hv) as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + left. exists b. split; [| reflexivity]. split; [| exact NF]. apply RM. split; [exact Hb|]. intros ->. apply N1. reflexivity.
    + right. left. exists b. split; [| reflexivity]. apply INT'. split; [exact Hb|]. intros ->. apply N2. reflexivity.
    + right. right. exists b. split; [| reflexivity]. split; [split; [exact (lb_remove_fake p _ b Hb HF)| exact NF]| exact HF].
  - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + apply RM in Hb as [Hb NE]. split; [apply HLB; left; exists b; split; [split; assumption| reflexivity]|].
      destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (NPb & B1 & B2 & _). split.
      * intros X. unfold user_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact Hb| rewrite X1; reflexivity].
      * intros X. unfold user_iv in X. injection X as X1 _. ulia.
    + apply INT' in Hb as [Hb NE]. split; [apply HLB; right; left; exists b; split; [exact Hb| reflexivity]|].
      destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). split.
      * intros X. unfold twin_iv in X. injection X as X1 _. ulia.
      * intros X. unfold twin_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact (proj1 (HT b Hb))| exact X1].
    + assert (HbL : In b (w_LBa W)) by (apply RM in Hb; tauto).
      split; [apply HLB; right; right; exists b; split; [split; [split; assumption| exact HF]| reflexivity]|].
      destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj HbL NF) HF)) as (T1 & T2 & T3 & _). split.
      * intros X. unfold fsh_iv in X. injection X as X1 _. ulia.
      * intros X. unfold fsh_iv in X. injection X as X1 _. pose proof (SAMESH b HbL X1) as ->. exact (heap_not_fake (HB p A n) (ex_intro _ p eq_refl) HF).
Qed.

Lemma aw_real_realloc : forall aw aw' LB m mo W RNG' st' p A nold q UB n m' mo' sp,
  aw_realW aw LB m mo W -> In (HB p A nold) (w_LBa W) ->
  AHEAP AI (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) m' -> ACCT aw' (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) mo' ->
  aheap_pres (aci AI) (lb_remove p (w_LBa W)) sp m m' ->
  twins_pres (lb_remove p (w_LBa W)) m m' -> ablock_shadow m' UB n ->
  let T' := List.filter (fun x => if ablock_eq_dec x (HB p A nold) then false else true) (w_T W) in
  let W1 := mkWit (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) T' (w_FA W) m' (w_zc W) in
  aw_realW aw' ((UB, n) :: LB_free LB A nold) m' mo' W1 /\ vis W1 (HB q UB n) /\ ~ In (HB q UB n) T'
  /\ user_band UB /\ (forall a, in_iv (UB, n) a -> ~ in_user (LB_free LB A nold) a)
  /\ (forall a, in_iv (shad UB, shlen (n + 7)) a -> ~ in_user (LB_free LB A nold) a).
Proof.
  intros aw aw' LB m mo W RNG' st' p A nold q UB n m' mo' sp [HW EM] HP AH' AC' PRES TW PATN T' W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A nold)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A nold b AH HP)).
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A nold).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A nold)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  pose proof (LB_free_char W aw LB m mo p A nold HW HP) as CHAR. cbv zeta in CHAR. fold T' in CHAR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  destruct (heap_block_facts _ _ _ _ _ (HB q UB n) AH' ltac:(left; reflexivity) ltac:(exists q; reflexivity)) as (NN & BRN & _). cbn [ab_addr ab_size] in NN, BRN.
  destruct (twin_band _ _ BRN NN) as (TN1 & TN2 & TN3 & _). pose proof BRN as (BKN & _ & HIN & ALN).
  destruct (user_app_band _ _ BKN ltac:(ulia)) as [BN1 BN2].
  assert (DISJ : forall b, In b (lb_remove p (w_LBa W)) -> UB + n <= ab_addr b \/ ab_addr b + ab_size b <= UB).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB q UB n) b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  assert (NT : ~ In (HB q UB n) T').
  { intros X. apply INT' in X as [X NE]. apply NIN. apply RM. split; [exact (proj1 (HT _ X))| exact NE]. }
  assert (NFA : ~ In (HB q UB n) (w_FA W)) by (intros X; exact (heap_not_fake (HB q UB n) (ex_intro _ q eq_refl) (proj2 (HFA _ X)))).
  assert (HW1 : aw_holds_w W1 aw' ((UB, n) :: LB_free LB A nold) m' mo').
  { unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
    split; [exact AH'|].
    split. { intros b Hb. apply INT' in Hb as [Hb NE]. destruct (HT b Hb) as [H1 H2]. split; [right; apply RM; split; assumption| exact H2]. }
    split; [apply NoDup_filter; exact ND|].
    split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [right; exact (lb_remove_fake p _ b H1 H2)| exact H2]. }
    split; [exact NDF|]. split.
    { intros v. cbn [In]. rewrite (CHAR v). unfold vis, visf. cbn [w_LBa w_FA]. split.
      - intros [<-|[(b & [Hb NF] & ->)|[H|(b & [[Hb NF] HF] & ->)]]].
        + left. exists (HB q UB n). split; [split; [left; reflexivity| exact NFA]| reflexivity].
        + left. exists b. split; [split; [right; exact Hb| exact NF]| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [split; [right; exact Hb| exact NF]| exact HF]| reflexivity].
      - intros [(b & [[<-|Hb] NF] & ->)|[H|(b & [[[<-|Hb] NF] HF] & ->)]].
        + left. reflexivity.
        + right. left. exists b. split; [split; assumption| reflexivity].
        + right. right. left. exact H.
        + exfalso. exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) HF).
        + right. right. right. exists b. split; [split; [split; assumption| exact HF]| reflexivity]. }
    split; [intros a _ _; reflexivity|].
    split.
    { intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT). apply INT' in HbT as [HbT NE].
      destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
      pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(right; apply RM; split; assumption) HbH (proj1 G) (proj2 G)) as P.
      replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
    split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [exfalso; exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) FK)| exact (CLS b (proj1 (proj1 (RM b) Hb)) FK)]. }
    split.
    2:{
        intros b [[<-|HbR] NFAb] HHb NTb; [exact PATN|]. pose proof (proj1 (RM b) HbR) as [HbL NEb].
        apply (twin_keep _ _ _ _ m m' (lb_remove p (w_LBa W)) b AH' ltac:(right; exact HbR) HHb TW HbR).
        intros g G0 G1. apply (INC b (conj HbL NFAb) HHb); [| exact G0| exact G1].
        intros X. apply NTb. apply INT'. split; [exact X| exact NEb]. }
    intros b [[[<-|HbR] NFAb] FKb]; [exfalso; exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) FKb)|].
    apply RM in HbR as [HbL _].
    assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] FK0] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block (lb_remove p (w_LBa W)) sp m m' b0 x PRES (lb_remove_fake p _ b0 Hb0 FK0)); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [left; reflexivity| exact NFA]|]. split; [exact NT|].
  split; [unfold user_band; ulia|]. split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b Hb). ulia.
    + apply INT' in Hb as [Hb _]. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + apply RM in Hb as [Hb _]. destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj Hb NF) HF)) as (T1 & T2 & _). ulia.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + apply RM in Hb as [Hb _]. destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (_ & B1 & _). ulia.
    + apply INT' in Hb as [Hb NE]. destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj UB n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b ltac:(apply RM; split; assumption)) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + pose proof Hb as HbR. apply RM in Hb as [Hb _]. destruct (LB_shadow_hull W aw LB m mo b HW (or_intror (conj (conj Hb NF) HF))) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj UB n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b HbR) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
Qed.

Lemma twin_same : forall L RNG st LBa RNG' st' LBa' (m m' : amem) LBt b g,
  AHEAP AI L RNG st LBa m -> AHEAP AI L RNG' st' LBa' m' -> In b LBa -> In b LBa' -> is_heap b -> twins_pres LBt m m' -> In b LBt ->
  0 <= g -> 8 * g < ab_size b -> m' (wa (shad (ab_addr b) + g)) = m (wa (shad (ab_addr b) + g)).
Proof.
  intros L RNG st LBa RNG' st' LBa' m m' LBt b g AH AH' Hb Hb' HH TW HbT G0 G1.
  destruct (is_primary (ab_size b)) eqn:PRIM.
  - destruct b as [[p|c] A n]; [| destruct HH as [q Hq]; discriminate]. cbn [ab_addr ab_size] in *.
    apply (TW p A n HbT PRIM g). unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia.
  - rewrite (twin_bytes_sec _ _ _ _ _ b g AH Hb HH PRIM G0 G1), (twin_bytes_sec _ _ _ _ _ b g AH' Hb' HH PRIM G0 G1). reflexivity.
Qed.

Lemma aw_real_stable : forall aw LB m mo W RNG' st' LBa' m' LBp LBk sp LBt,
  twins_pres LBt m m' -> (forall b, In b (w_LBa W) -> In b LBa' -> In (twin_iv b) LBk -> In b LBt) ->
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' LBa' m' -> aheap_pres (aci AI) LBp sp m m' ->
  (forall v, In v LBk -> user_band (fst v) -> 0 < snd v -> exists b, In b LBp /\ v = user_iv b) ->
  (forall v, In v LBk -> ~ user_band (fst v) ->
        (exists b, In b (w_LBa W) /\ In b LBa' /\ is_heap b /\ v = twin_iv b)
     \/ (exists b, In b (w_LBa W) /\ In b LBp /\ is_fake b /\ v = fsh_iv b)) ->
  forall a, 0 <= a < 2 ^ 64 -> (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a -> m' (wa a) = m (wa a).
Proof.
  intros aw LB m mo W RNG' st' LBa' m' LBp LBk sp LBt TW TWIN [HW EM] AH' PRES KU KT a Ha ST.
  pose proof HW as (AH & _). rewrite EM in AH.
  assert (CL : aclient_addr (aci AI) LBp sp a -> m' (wa a) = m (wa a)) by (intros C; exact (proj1 (PRES a Ha C))).
  destruct ST as [S|[S|S]]; [apply CL; left; exact S| apply CL; right; left; exact S|].
  apply in_ivs_In in S as (v & Hv & Hin).
  destruct (Z_lt_dec (fst v) 0x7fff8000) as [LT|GE]; [| destruct (Z_le_dec 0x10007fff8000 (fst v)) as [GE2|LT2]].
  - destruct (KU v Hv ltac:(left; exact LT) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL. right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
  - destruct (KU v Hv ltac:(right; exact GE2) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL. right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
  - destruct (KT v Hv ltac:(unfold user_band; ulia)) as [(b & Hb & Hb' & HH & ->)|(b & Hb & HbP & HF & ->)].
    + destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (Nb & BRb & _).
      destruct (twin_band _ _ BRb Nb) as (T1 & T2 & T3 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. clear - Hin Nb. Z.div_mod_to_equations. ulia. }
      replace a with (shad (ab_addr b) + (a - shad (ab_addr b))) by ulia.
      exact (twin_same _ _ _ _ _ _ _ m m' LBt b (a - shad (ab_addr b)) AH AH' Hb Hb' HH TW (TWIN b Hb Hb' Hv) (proj1 G) (proj2 G)).
    +
      destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
      destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (F1 & F2 & F3 & E1 & E2).
      unfold in_iv, fsh_iv in Hin. cbn [fst snd] in Hin.
      apply CL. right; right; right. exists (8 * (a - ASHOFF)). split.
      * right. right. destruct b as [[q|c] F k]; [destruct HF as [d HF]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size] in *. split; [exact HbP| ulia].
      * unfold shad. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by ulia. ulia.
Qed.

Lemma aw_real_stable_x : forall aw LB m mo W RNG' st' LBa' m' LBp LBk sp (X : Z -> Prop) LBt,
  twins_pres LBt m m' -> (forall b, In b (w_LBa W) -> In b LBa' -> In (twin_iv b) LBk -> In b LBt) ->
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' LBa' m' ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBp sp a -> ~ X a -> m' (wa a) = m (wa a)) ->
  (forall a, X a -> shad ATOP <= a < shad (2 ^ 47)) -> ATOP <= sp -> (forall v, In v LBk -> In v LB) ->
  (forall v, In v LBk -> user_band (fst v) -> 0 < snd v -> exists b, In b LBp /\ v = user_iv b) ->
  (forall v, In v LBk -> ~ user_band (fst v) ->
        (exists b, In b (w_LBa W) /\ In b LBa' /\ is_heap b /\ v = twin_iv b)
     \/ (exists b, In b (w_LBa W) /\ In b LBp /\ is_fake b /\ v = fsh_iv b)) ->
  forall a, 0 <= a < 2 ^ 64 -> (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a -> m' (wa a) = m (wa a).
Proof.
  intros aw LB m mo W RNG' st' LBa' m' LBp LBk sp X LBt TW TWIN [HW EM] AH' PRES XB SPA SUB KU KT a Ha ST.
  pose proof HW as (AH & _). rewrite EM in AH. pose proof atop_range as AR.
  assert (XZ : X a -> 0x7fff8000 + 0x7fff7f800000 / 8 <= a < 0x10007fff8000).
  { intros Xa. apply XB in Xa. unfold shad, ASHOFF in Xa. rewrite !Z.shiftr_div_pow2 in Xa by lia. change (2^3) with 8 in Xa.
    clear - Xa AR. Z.div_mod_to_equations. lia. }
  assert (CL : aclient_addr (aci AI) LBp sp a -> ~ X a -> m' (wa a) = m (wa a)) by (intros C NX; exact (PRES a Ha C NX)).
  destruct ST as [S|[S|S]].
  - apply CL; [left; exact S|]. intros Xa. apply XZ in Xa. clear - Xa S SPA AR. lia.
  - apply CL; [right; left; exact S|]. intros Xa. apply XZ in Xa. destruct S as (r & Hr & Hin).
    pose proof (AI_aci_img AI r Hr) as HI. unfold AIMG_HI in HI. clear - Xa Hin HI. lia.
  - apply in_ivs_In in S as (v & Hv & Hin).
    destruct (Z_lt_dec (fst v) 0x7fff8000) as [LT|GE]; [| destruct (Z_le_dec 0x10007fff8000 (fst v)) as [GE2|LT2]].
    + destruct (KU v Hv ltac:(left; exact LT) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL.
      * right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
      * intros Xa. apply XZ in Xa. unfold in_iv in Hin.

        destruct (LB_cases W aw LB m mo _ HW (SUB _ Hv)) as [(b0 & Vb & E)|[(b0 & Hb0 & E)|(b0 & Vb & E)]]; rewrite E in Hin, LT.
        -- destruct (LB_user_facts W aw LB m mo b0 HW Vb) as (_ & BD & _). cbn [fst snd user_iv] in Hin, LT. clear - Xa Hin LT BD. ulia.
        -- destruct (LB_twin_facts W aw LB m mo b0 HW Hb0) as (T1 & _). cbn [fst twin_iv] in LT. clear - LT T1. lia.
        -- destruct (LB_fsh_facts W aw LB m mo b0 HW Vb) as (T1 & _). cbn [fst fsh_iv] in LT. clear - LT T1. lia.
    + destruct (KU v Hv ltac:(right; exact GE2) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL.
      * right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
      * intros Xa. apply XZ in Xa. unfold in_iv in Hin. clear - Xa Hin GE2. lia.
    + destruct (KT v Hv ltac:(unfold user_band; ulia)) as [(b & Hb & Hb' & HH & ->)|(b & Hb & HbP & HF & ->)].
      * destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (Nb & BRb & _).
        destruct (twin_band _ _ BRb Nb) as (T1 & T2 & T3 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
        assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
        { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. clear - Hin Nb. Z.div_mod_to_equations. ulia. }
        replace a with (shad (ab_addr b) + (a - shad (ab_addr b))) by ulia.
        exact (twin_same _ _ _ _ _ _ _ m m' LBt b (a - shad (ab_addr b)) AH AH' Hb Hb' HH TW (TWIN b Hb Hb' Hv) (proj1 G) (proj2 G)).
      * destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
        destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (F1 & F2 & F3 & E1 & E2).
        unfold in_iv, fsh_iv in Hin. cbn [fst snd] in Hin.
        apply CL.
        -- right; right; right. exists (8 * (a - ASHOFF)). split.
           ++ right. right. destruct b as [[q|c] F k]; [destruct HF as [d HF]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size] in *. split; [exact HbP| ulia].
           ++ unfold shad. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by ulia. ulia.
        -- intros Xa. apply XB in Xa. unfold shad, ASHOFF in Xa, E1, Hin. rewrite !Z.shiftr_div_pow2 in Xa by lia. change (2^3) with 8 in Xa.
           clear - Xa Hin E1 E2 HI. unfold ASHOFF in *. Z.div_mod_to_equations. ulia.
Qed.

Lemma freed_apart : forall aw LB m mo W A n a,
  aw_realW aw LB m mo W -> In (A, n) LB -> In (shad A, shlen (n + 7)) LB ->
  in_iv (A, n) a \/ in_iv (shad A, shlen (n + 7)) a -> ~ in_user (LB_free LB A n) a.
Proof.
  intros aw LB m mo W A n a AR H0 HT Ha U. pose proof (aw_real_holds _ _ _ _ _ AR) as AWH. destruct AR as [HW _].
  apply in_ivs_In in U as (b' & Hb' & Hin). apply LB_free_In in Hb' as (Hb' & N1 & N2). destruct b' as [A' n'].
  destruct Ha as [Ha|Ha].
  - apply (aw_blocks_disj_asan aw LB m mo (A, n) (A', n') a AWH H0 Hb'); [| exact Ha| exact Hin].
    cbn [fst]. intros <-. apply N1. f_equal. exact (LB_same_addr W aw LB m mo A n' n HW Hb' H0).
  - apply (aw_blocks_disj_asan aw LB m mo (shad A, shlen (n + 7)) (A', n') a AWH HT Hb'); [| exact Ha| exact Hin].
    cbn [fst]. intros <-. apply N2. f_equal. exact (LB_same_addr W aw LB m mo (shad A) n' _ HW Hb' HT).
Qed.

Variable Cw : client_world.
Definition K_FRAMEz : Z := 7.
Definition K_FTWINz : Z := 8.
Definition K_TWINz : Z := 9.

Definition ZC_BASE : Z := 2^47.
Definition ZC_BAND : Z := 2^47 + 2^46.

Definition PRIST_BASE : Z := 2^47 + 2^46.
Definition prist_win : window := Win PRIST_BASE 0 K_STACK.
Definition aprist (st : astate) : Prop := APristLaw.aprist st.

Lemma prist_tied : aw_tied prist_win.
Proof. left. split; [reflexivity|]. unfold prist_win, PRIST_BASE, AW_BAND. cbn [w_lo]. lia. Qed.
Definition zc_win (zc : Z) : window := Win (ZC_BASE + zc) 0 K_STACK.
Definition c24inv (W : wit) (ws : list window) : Prop :=
  forall b, vis W b -> is_heap b -> c24 (ab_size b) ->
    exists w, In w ws /\ heap_kind w /\ 0 < w_len w /\ in_iv (user_iv b) (w_lo w).
Definition ties (W : wit) (ws : list window) : Prop :=
     (forall b, In b (w_T W) -> In (Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) ws)
  /\ (forall w, In w ws -> w_kind w = K_TWINz -> exists b, In b (w_T W) /\ w_iv w = twin_iv b)
  /\ (forall b, visf W b -> In (Win (ab_addr b) (ab_size b - 8) K_FRAMEz) ws /\ In (Win (shad (ab_addr b)) (shlen (ab_size b)) K_FTWINz) ws)
  /\ (forall w, In w ws -> w_kind w = K_FRAMEz -> exists b, visf W b /\ w_iv w = user_iv b)
  /\ (forall w, In w ws -> w_kind w = K_FTWINz -> exists b, visf W b /\ w_iv w = fsh_iv b)

  /\ (forall w, In w ws -> w_kind w = K_STACK -> w_len w = 0 -> w_lo w < ZC_BAND -> w = zc_win (w_zc W)) /\ In (zc_win (w_zc W)) ws

  /\ (forall w, In w ws -> w_kind w = K_STACK -> w_lo w < ZC_BASE -> w_lo w = ATOP + 4096)

  /\ c24inv W ws /\ ghost_apart ws

  /\ (In prist_win ws -> aprist (w_st W)).
Lemma window_eq_dec : forall x y : window, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma ghost_apart_sub : forall ws ws', ghost_apart ws -> (forall w, In w ws' -> In w ws) -> ghost_apart ws'.
Proof. intros ws ws' GA I w w' Hw Hw' K K' a Ha. exact (GA w w' (I w Hw) (I w' Hw') K K' a Ha). Qed.

Lemma ghost_apart_new_ghosts : forall ws ws' LB ceil, windows_wf ws LB ceil -> ghost_apart ws ->
  (forall w, In w ws' -> In w ws \/ (w_kind w <> K_BLOCK /\ (K_GHOST <= w_kind w -> forall a, in_iv (w_iv w) a -> ~ in_user LB a))) ->
  ghost_apart ws'.
Proof.
  intros ws ws' LB ceil WF GA NEW w w' Hw Hw' K K' a Ha Ha'.
  destruct (NEW w' Hw') as [Hw0'|[NB _]]; [| exact (NB K')].
  destruct (NEW w Hw) as [Hw0|[_ FR]]; [exact (GA w w' Hw0 Hw0' K K' a Ha Ha')|].
  apply (FR K a Ha). pose proof (proj1 (Forall_forall _ _) WF w' Hw0') as (_ & _ & _ & [[KS _]|[[_ B]|[KS _]]]);
    [rewrite K' in KS; unfold K_BLOCK, K_STACK in KS; lia| | rewrite K' in KS; unfold K_BLOCK, K_SUB in KS; lia].
  unfold in_user. apply in_ivs_In. exists (w_iv w'). split; [exact B| exact Ha'].
Qed.

Lemma ghost_apart_new_block : forall ws LB ceil A n, windows_wf ws LB ceil -> ghost_apart ws ->
  (forall a, in_iv (A, n) a -> ~ in_user LB a) -> ghost_apart (ws ++ [Win A n K_BLOCK]).
Proof.
  intros ws LB ceil A n WF GA FR w w' Hw Hw' K K' a Ha Ha'.
  apply in_app_or in Hw as [Hw|[<-|[]]]; [| cbn [w_kind] in K; unfold K_BLOCK, K_GHOST in K; lia].
  apply in_app_or in Hw' as [Hw'|[<-|[]]]; [exact (GA w w' Hw Hw' K K' a Ha Ha')|].
  apply (FR a Ha'). pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & [[KS _]|[[KB _]|[_ (b & Hb & SUB)]]]);
    [rewrite KS in K; unfold K_STACK, K_GHOST in K; lia| rewrite KB in K; unfold K_BLOCK, K_GHOST in K; lia|].
  unfold in_user. apply in_ivs_In. exists b. split; [exact Hb| exact (SUB a Ha)].
Qed.

Lemma ties_set_ms : forall W ms ws, ties (set_ms W ms) ws <-> ties W ws.
Proof. intros W ms ws. unfold ties, c24inv, set_ms, visf, vis. cbn [w_T w_LBa w_FA w_zc w_st]. tauto. Qed.
Lemma ties_ext : forall W W' ws, w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W -> ties W ws ->
  (forall b, is_heap b -> vis W' b -> vis W b) -> (aprist (w_st W) -> aprist (w_st W')) -> ties W' ws.
Proof.
  intros W W' ws ET EV EZ (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HV PS. unfold ties. rewrite ET, EZ.
  split; [exact T1|]. split; [exact T2|]. split; [intros b Hb; apply T3; apply EV; exact Hb|].
  split; [intros w Hw K; destruct (T4 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [intros w Hw K; destruct (T5 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [exact T6| split; [exact T7| split; [exact T8|]]].
  split; [intros b Vb HH CC; exact (C24 b (HV b HH Vb) HH CC)| split; [exact GA| intros IP; exact (PS (PR IP))]].
Qed.

Lemma ties_burn : forall W W' ws ws' c,
  ties W ws -> w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W - c -> c <= w_zc W ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win (w_zc W)) \/ w = zc_win (w_zc W - c)) ->
  (forall b, is_heap b -> vis W' b -> vis W b) ->
  ZC_BASE + (w_zc W - c) < ZC_BAND -> (aprist (w_st W) -> aprist (w_st W')) ->
  ties W' ws'.
Proof.
  intros W W' ws ws' c (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EV EZ CZ WS HV ZB PS. unfold ties. rewrite ET, EZ.
  assert (KEEP : forall w, In w ws -> w_kind w <> K_STACK -> In w ws').
  { intros w Hw NK. apply WS. left. split; [exact Hw|]. intros ->. apply NK. reflexivity. }
  assert (OLD : forall w, In w ws' -> w_kind w <> K_STACK -> In w ws).
  { intros w Hw NK. apply WS in Hw as [[Hw _]| ->]; [exact Hw| exfalso; apply NK; reflexivity]. }
  split. { intros b Hb. apply KEEP; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_STACK; ulia]. }
  split. { intros w Hw K. apply T2; [apply OLD; [exact Hw| rewrite K; unfold K_TWINz, K_STACK; ulia]| exact K]. }
  split. { intros b Vb. apply EV in Vb. destruct (T3 b Vb) as [X Y]. split; apply KEEP; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_STACK; ulia. }
  split. { intros w Hw K. destruct (T4 w (OLD w Hw ltac:(rewrite K; unfold K_FRAMEz, K_STACK; ulia)) K) as (b & Vb & E). exists b. split; [apply EV; exact Vb| exact E]. }
  split. { intros w Hw K. destruct (T5 w (OLD w Hw ltac:(rewrite K; unfold K_FTWINz, K_STACK; ulia)) K) as (b & Vb & E). exists b. split; [apply EV; exact Vb| exact E]. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [[Hw NE]| ->]; [exfalso; exact (NE (T6 w Hw K Z0 B0))| reflexivity]. }
  split; [apply WS; right; reflexivity|].
  split. { intros w Hw K P. apply WS in Hw as [[Hw _]| ->]; [exact (T8 w Hw K P)| unfold zc_win in P; cbn [w_lo] in P; lia]. }
  split.
  - intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto].
    apply KEEP; [exact Hw|]. unfold heap_kind, K_BLOCK, K_STACK in *. lia.
  - split.
    + intros w w' Hw Hw' K K' a Ha. apply (GA w w'); [apply OLD; [exact Hw| unfold K_GHOST, K_STACK in *; lia]| apply OLD; [exact Hw'| rewrite K'; unfold K_BLOCK, K_STACK; lia]| exact K| exact K'| exact Ha].
    + intros IP. apply PS, PR. apply WS in IP as [[IP _]|E]; [exact IP| exfalso].
      unfold prist_win, zc_win, PRIST_BASE, ZC_BAND in *. injection E as E. lia.
Qed.

Lemma ties_grow_heap : forall W ws L' RNG' st' ms' b,
  ties W ws -> is_heap b -> 0 < ab_size b ->
  ghost_apart ((ws ++ [Win (ab_addr b) (ab_size b) K_BLOCK]) ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]) ->
  (In prist_win ws -> aprist st') ->
  ties (mkWit L' RNG' st' (b :: w_LBa W) (b :: w_T W) (w_FA W) ms' (w_zc W))
       ((ws ++ [Win (ab_addr b) (ab_size b) K_BLOCK]) ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]).
Proof.
  intros W ws L' RNG' st' ms' b (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HH POS GAN PS.
  set (WB := Win (ab_addr b) (ab_size b) K_BLOCK). set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz).
  assert (INC : forall w, In w ws -> In w ((ws ++ [WB]) ++ [WT])) by (intros w Hw; apply in_or_app; left; apply in_or_app; left; exact Hw).
  assert (CASES : forall w, In w ((ws ++ [WB]) ++ [WT]) -> In w ws \/ w = WB \/ w = WT).
  { intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [| right; right; reflexivity]. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right; left; reflexivity]. }
  assert (VF : forall b', visf (mkWit L' RNG' st' (b :: w_LBa W) (b :: w_T W) (w_FA W) ms' (w_zc W)) b' <-> visf W b').
  { intros b'. unfold visf, vis. cbn [w_LBa w_FA In]. split.
    - intros [[[<-|Hb] NF] FK]; [exfalso; exact (heap_not_fake _ HH FK)| auto].
    - intros [[Hb NF] FK]. auto. }
  unfold ties. cbn [w_T w_zc].
  split. { intros b' [<-|Hb']; [apply in_or_app; right; left; reflexivity| exact (INC _ (T1 b' Hb'))]. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [right; exact Hb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_TWINz in K. ulia.
           - exists b. split; [left; reflexivity| reflexivity]. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y]. split; apply INC; assumption. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_FRAMEz in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FRAMEz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_FTWINz in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FTWINz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - exact (T6 w Hw0 K).
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_STACK in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [exact (INC _ T7)|].
  split. { intros w Hw K P. destruct (CASES w Hw) as [Hw0|[->| ->]]; [exact (T8 w Hw0 K P)| |]; exfalso; cbn [w_kind WB WT] in K; unfold K_BLOCK, K_TWINz, K_STACK in K; ulia. }
  split; [| split; [exact GAN| cbn [w_st]; intros IP; destruct (CASES _ IP) as [IP0|[E|E]]; [exact (PS IP0)| |]; exfalso; unfold prist_win, WB, WT in E; injection E as _ _ E; unfold K_STACK, K_BLOCK, K_TWINz in E; ulia]].
  intros b' [[<-|Hb'] NF] HH' CC.
  - exists WB. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    split; [unfold heap_kind, WB; cbn [w_kind]; unfold K_BLOCK, K_GHOST; lia|]. split; [exact POS|].
    unfold in_iv, user_iv, WB. cbn [w_lo fst snd]. rewrite (usz_heap b HH). lia.
  - destruct (C24 b' (conj Hb' NF) HH' CC) as (w & Hw & X). exists w. split; [exact (INC _ Hw)| exact X].
Qed.

Lemma ties_free : forall W aw LB m mo ws ws1 ws2 p A n RNG' st' ms',
  aw_holds_w W aw LB m mo -> ties W ws -> In (HB p A n) (w_T W) ->
  (forall w, In w ws1 <-> In w ws /\ w <> Win A n K_BLOCK) ->
  (forall w, In w ws2 <-> In w ws1 /\ w <> Win (shad A) (shlen (n + 7)) K_TWINz) ->
  (In prist_win ws -> aprist st') ->
  ties (mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W))
              (w_FA W) ms' (w_zc W)) ws2.
Proof.
  intros W aw LB m mo ws ws1 ws2 p A n RNG' st' ms' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HbT IN1 IN2 PS.
  pose proof HW as (AH & HT & _ & HFA & _). destruct (HT _ HbT) as [HbL HbH].
  set (b := HB p A n) in *. set (WB := Win A n K_BLOCK) in *. set (WT := Win (shad A) (shlen (n + 7)) K_TWINz) in *.
  assert (INT' : forall x, In x (List.filter (fun x => if ablock_eq_dec x b then false else true) (w_T W)) <-> In x (w_T W) /\ x <> b).
  { intros x. rewrite filter_In. destruct (ablock_eq_dec x b); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  assert (KEEP : forall w, In w ws -> w <> WB -> w <> WT -> In w ws2) by (intros w Hw N1 N2; apply IN2; split; [apply IN1; split; assumption| exact N2]).
  assert (OLD : forall w, In w ws2 -> In w ws /\ w <> WT) by (intros w Hw; apply IN2 in Hw as [Hw N2]; apply IN1 in Hw as [Hw _]; auto).
  assert (VF : forall b', visf (mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x b then false else true) (w_T W))
                                      (w_FA W) ms' (w_zc W)) b' <-> visf W b').
  { intros b'. unfold visf, vis. cbn [w_LBa w_FA]. rewrite (lb_remove_In _ _ _ _ _ p A n b' AH HbL). fold b. split.
    - intros [[[Hb' _] NF] FK]. auto.
    - intros [[Hb' NF] FK]. split; [split; [split; [exact Hb'| intros ->; exact (heap_not_fake b HbH FK)]| exact NF]| exact FK]. }
  unfold ties. cbn [w_T w_zc].
  split. { intros b' Hb'. apply INT' in Hb' as [Hb' NE]. apply KEEP; [exact (T1 b' Hb')| unfold WB; intros X; injection X as _ _ X; unfold K_TWINz, K_BLOCK in X; ulia|].
           unfold WT. intros X. injection X as X1 X2. apply NE. apply (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 (HT b' Hb')) HbL). unfold b. cbn [ab_addr]. exact X1. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 NWT]. destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [| exact E]. apply INT'. split; [exact Hb'|].
           intros ->. apply NWT. destruct w as [wl wn wk]. unfold w_iv, twin_iv, b in E. cbn [w_lo w_len w_kind ab_addr ab_size] in E, K. injection E as -> ->. subst wk. reflexivity. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y].
           split; apply KEEP; try assumption; unfold WB, WT; intros Z; injection Z as _ _ Z; unfold K_FRAMEz, K_FTWINz, K_TWINz, K_BLOCK in Z; ulia. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K Z0 B0. destruct (OLD w Hw) as [Hw0 _]. exact (T6 w Hw0 K Z0 B0). }
  split; [apply KEEP; [exact T7| |]; unfold zc_win, WB, WT; intros Z; injection Z as _ _ Z; unfold K_STACK, K_BLOCK, K_TWINz in Z; ulia|].
  split. { intros w Hw K P. destruct (OLD w Hw) as [Hw0 _]. exact (T8 w Hw0 K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (OLD w Hw))]| cbn [w_st]; intros IP; exact (PS (proj1 (OLD _ IP)))]].
  intros b' [Hb' NF'] HH' CC. cbn [w_LBa w_FA] in Hb', NF'. apply (lb_remove_In _ _ _ _ _ p A n b' AH HbL) in Hb' as [Hb' NEb]. fold b in NEb.
  destruct (C24 b' (conj Hb' NF') HH' CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto]. apply KEEP; [exact Hw| |].
  - intros ->. unfold WB in HI. cbn [w_lo] in HI.
    destruct (AI_blocks_disjoint AI _ _ _ _ _ b' b AH Hb' HbL NEb) as [D|D]; unfold in_iv, user_iv in HI; cbn [fst snd] in HI;
      rewrite (usz_heap b' HH') in HI; unfold b in D; cbn [ab_addr ab_size] in D;
      destruct (AI_block AI _ _ _ _ _ p A n AH HbL) as (NR & _); lia.
  - intros ->. unfold heap_kind, WT in HK. cbn [w_kind] in HK. unfold K_TWINz, K_GHOST in HK. lia.
Qed.

Lemma ties_twin_out : forall W ws b,
  ties W ws ->
  ghost_apart (ws ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]) ->
  ties (set_T W (b :: w_T W)) (ws ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]).
Proof.
  intros W ws b (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) GAN.
  set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) in *.
  assert (INC : forall w, In w ws -> In w (ws ++ [WT])) by (intros w Hw; apply in_or_app; left; exact Hw).
  assert (CASES : forall w, In w (ws ++ [WT]) -> In w ws \/ w = WT) by (intros w Hw; apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right; reflexivity]).
  assert (VF : forall b', visf (set_T W (b :: w_T W)) b' <-> visf W b') by (intros b'; unfold visf, vis, set_T; cbn [w_LBa w_FA]; reflexivity).
  unfold ties. cbn [w_T w_zc set_T].
  split. { intros b' [<-|Hb']; [apply in_or_app; right; left; reflexivity| exact (INC _ (T1 b' Hb'))]. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [right; exact Hb'| exact E].
           - exists b. split; [left; reflexivity| reflexivity]. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y]. split; apply INC; assumption. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FRAMEz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FTWINz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - exact (T6 w Hw0 K).
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [exact (INC _ T7)|].
  split. { intros w Hw K P. destruct (CASES w Hw) as [Hw0| ->]; [exact (T8 w Hw0 K P)|]. exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [| split; [exact GAN| cbn [w_st set_T]; intros IP; destruct (CASES _ IP) as [IP0|E]; [exact (PR IP0)|]; exfalso; unfold prist_win, WT in E; injection E as _ _ E; unfold K_STACK, K_TWINz in E; ulia]].
  intros b' Vb' HH' CC. destruct (C24 b' Vb' HH' CC) as (w & Hw & X). exists w. split; [exact (INC _ Hw)| exact X].
Qed.

Lemma ties_twin_in : forall W aw LB m mo ws ws' b (m1 : amem),
  aw_holds_w W aw LB m mo -> ties W ws -> In b (w_T W) ->
  (forall w, In w ws' <-> In w ws /\ w <> Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) ->
  ties (wit_twin_in W m1 b) ws'.
Proof.
  intros W aw LB m mo ws ws' b m1 HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HbT IN2.
  pose proof HW as (AH & HT & _). destruct (HT _ HbT) as [HbL HbH].
  set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) in *.
  assert (KEEP : forall w, In w ws -> w <> WT -> In w ws') by (intros w Hw N2; apply IN2; split; assumption).
  assert (OLD : forall w, In w ws' -> In w ws /\ w <> WT) by (intros w Hw; apply IN2 in Hw; exact Hw).
  assert (VF : forall b', visf (wit_twin_in W m1 b) b' <-> visf W b') by (intros b'; unfold visf, vis, wit_twin_in; cbn [w_LBa w_FA]; reflexivity).
  unfold ties. cbn [w_T w_zc wit_twin_in].
  split. { intros b' Hb'. apply lb_del_In in Hb' as [Hb' NE]. apply KEEP; [exact (T1 b' Hb')|].
           unfold WT. intros X. injection X as X1 X2. apply NE. exact (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 (HT b' Hb')) HbL X1). }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 NWT]. destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [| exact E]. apply lb_del_In. split; [exact Hb'|].
           intros ->. apply NWT. destruct w as [wl wn wk]. unfold w_iv, twin_iv in E. cbn [w_lo w_len w_kind] in E, K. injection E as -> ->. subst wk. reflexivity. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y].
           split; apply KEEP; try assumption; unfold WT; intros Z; injection Z as _ _ Z; unfold K_FRAMEz, K_FTWINz, K_TWINz in Z; ulia. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K Z0 B0. destruct (OLD w Hw) as [Hw0 _]. exact (T6 w Hw0 K Z0 B0). }
  split; [apply KEEP; [exact T7|]; unfold zc_win, WT; intros Z; injection Z as _ _ Z; unfold K_STACK, K_TWINz in Z; ulia|].
  split. { intros w Hw K P. destruct (OLD w Hw) as [Hw0 _]. exact (T8 w Hw0 K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (OLD w Hw))]| cbn [w_st wit_twin_in]; intros IP; exact (PR (proj1 (OLD _ IP)))]].
  intros b' Vb' HH' CC. destruct (C24 b' Vb' HH' CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto]. apply KEEP; [exact Hw|].
  intros ->. unfold heap_kind, WT in HK. cbn [w_kind] in HK. unfold K_TWINz, K_GHOST in HK. lia.
Qed.

Lemma ties_prist : forall W ws, ties W ws -> In prist_win ws -> aprist (w_st W).
Proof. intros W ws (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR) IP. exact (PR IP). Qed.

Lemma ties_prist_del : forall W aw LB m mo ws ws',
  aw_holds_w W aw LB m mo -> ties W ws ->
  (forall w, In w ws' -> In w ws) -> (forall w, In w ws -> w <> prist_win -> In w ws') ->
  ties W ws'.
Proof.
  intros W aw LB m mo ws ws' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) SUB SUP.
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & ZC0 & ZCB & _).
  assert (KEEPK : forall w, In w ws -> w_kind w <> K_STACK -> In w ws').
  { intros w Hw NK. apply SUP; [exact Hw|]. intros ->. apply NK. reflexivity. }
  unfold ties.
  split. { intros b Hb. apply KEEPK; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_STACK; lia]. }
  split. { intros w Hw K. exact (T2 w (SUB w Hw) K). }
  split. { intros b Vb. destruct (T3 b Vb) as [X Y]. split; apply KEEPK; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_STACK; lia. }
  split. { intros w Hw K. exact (T4 w (SUB w Hw) K). }
  split. { intros w Hw K. exact (T5 w (SUB w Hw) K). }
  split. { intros w Hw K Z0 B0. exact (T6 w (SUB w Hw) K Z0 B0). }
  split. { apply SUP; [exact T7|]. unfold zc_win, prist_win, PRIST_BASE, ZC_BASE, ZTOTAL in *. intros E. injection E as E. lia. }
  split. { intros w Hw K P. exact (T8 w (SUB w Hw) K P). }
  split. { intros b Vb HH CC. destruct (C24 b Vb HH CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto].
           apply SUP; [exact Hw|]. intros ->. unfold prist_win in HL. cbn [w_len] in HL. lia. }
  split; [apply (ghost_apart_sub ws); [exact GA| exact SUB]|].
  intros IP. exact (PR (SUB _ IP)).
Qed.

Hypothesis AI_prist : APristLaw.prist_det_law (AHEAP AI).
Lemma aprist_heap : forall W aw LB m mo L RNG sta LBa,
  aw_holds_w W aw LB m mo -> AHEAP AI L RNG sta LBa m -> aprist (w_st W) -> aprist sta.
Proof.
  intros W aw LB m mo L RNG sta LBa HW AH PR. pose proof HW as (AHw & HT & _ & _ & _ & _ & SAME & _).
  apply (AI_prist (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_ms W) L RNG sta LBa m AHw AH); [| exact PR].
  intros a Ha. symmetry. apply SAME; [unfold two64, AIMG_HI in *; lia|]. intros IN.
  apply in_ivs_In in IN as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
  destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI in Ha. lia.
Qed.

Definition aw_holdsA (aw : word) (LB : blocks) (ws : list window) (m : amem) (mo : Model) : Prop :=
  exists W, aw_holds_w W aw LB m mo /\ ties W ws.
Lemma aw_holdsA_plain : forall aw LB ws m mo, aw_holdsA aw LB ws m mo -> aw_holds_asan aw LB m mo.
Proof. intros aw LB ws m mo (W & HW & _). exists W. exact HW. Qed.

Lemma aw_frameA : forall A LB ws m m' mo, aw_holdsA A LB ws m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsA A LB ws m' mo /\ (forall a, aw_dep_asan LB m' mo a <-> aw_dep_asan LB m mo a).
Proof.
  intros A LB ws m m' mo (W & HW & TI) AG DM. split; [| intros a; reflexivity].
  destruct (aw_frame_w W A LB m m' mo HW AG DM) as [ms2 H2]. exists (set_ms W ms2). split; [exact H2| apply ties_set_ms; exact TI].
Qed.

Lemma ties_keep : forall W aw LB m mo ws ws', aw_holds_w W aw LB m mo -> ties W ws -> wins_keep LB ws ws' -> ties W ws'.
Proof.
  intros W aw LB m mo ws ws' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) (KA & KB & KC).
  pose proof HW as (AH & HT & _ & HFA & _ & HLB & _ & _ & ZC0 & ZCB & _).
  assert (TG : forall w, K_GHOST <= w_kind w -> aw_tied w) by (intros w H; right; exact H).
  assert (OLDG : forall w, In w ws' -> K_GHOST <= w_kind w -> In w ws) by (intros w Hw K; apply (KA w (TG w K)); exact Hw).
  assert (NEWG : forall w, In w ws -> K_GHOST <= w_kind w -> In w ws') by (intros w Hw K; apply (KA w (TG w K)); exact Hw).
  unfold ties.
  split. { intros b Hb. apply NEWG; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_GHOST; lia]. }
  split. { intros w Hw K. apply T2; [apply OLDG; [exact Hw| rewrite K; unfold K_TWINz, K_GHOST; lia]| exact K]. }
  split. { intros b Vb. destruct (T3 b Vb) as [X Y]. split; apply NEWG; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_GHOST; lia. }
  split. { intros w Hw K. apply T4; [apply OLDG; [exact Hw| rewrite K; unfold K_FRAMEz, K_GHOST; lia]| exact K]. }
  split. { intros w Hw K. apply T5; [apply OLDG; [exact Hw| rewrite K; unfold K_FTWINz, K_GHOST; lia]| exact K]. }
  split. { intros w Hw K Z0 B0. apply T6; [| exact K| exact Z0| exact B0]. apply (KA w); [left; split; [exact K| unfold ZC_BAND, AW_BAND in *; lia]| exact Hw]. }
  split. { apply (KA (zc_win (w_zc W))); [| exact T7]. left. split; [reflexivity|]. unfold zc_win, ZC_BASE, AW_BAND, ZTOTAL in *. cbn [w_lo]. lia. }
  split. { intros w Hw K P. apply T8; [| exact K| exact P]. apply (KA w); [left; split; [exact K| unfold ZC_BASE, AW_BAND in *; lia]| exact Hw]. }
  split.
  -
    intros b Vb HH CC. destruct (C24 b Vb HH CC) as (w & Hw & HK & HL & HI).
    destruct (in_dec window_eq_dec w ws') as [Hin|Hnin]; [exists w; auto|].
    destruct (KB w Hw Hnin HK HL) as (o & Ho & Io & ALT).
    assert (INB : In (user_iv b) LB) by (apply HLB; left; exists b; split; [exact Vb| reflexivity]).
    assert (EO : o = user_iv b).
    { destruct (iv_eq_dec o (user_iv b)) as [E|NE]; [exact E| exfalso].
      assert (HAa : aw_holds_asan aw LB m mo) by (exists W; exact HW).
      destruct (Z.eq_dec (fst o) (fst (user_iv b))) as [EF|NF]; [| exact (aw_blocks_disj_asan aw LB m mo o (user_iv b) (w_lo w) HAa Ho INB NF Io HI)].

      destruct o as [oa on]. unfold user_iv in *. cbn [fst] in EF. subst oa.
      apply NE. f_equal. exact (LB_same_addr W aw LB m mo _ _ _ HW Ho INB). }
    subst o. destruct ALT as [NC|(w' & Hw' & HK' & HL' & HI')]; [exfalso; apply NC; unfold user_iv; cbn [snd]; rewrite (usz_heap b HH); exact CC|].
    exists w'. auto.
  - split.
    +
      intros w w' Hw Hw' K K' a Ha. destruct (in_dec window_eq_dec w' ws) as [Hin|Hnin].
      * exact (GA w w' (OLDG w Hw K) Hin K K' a Ha).
      * exact (KC w' Hw' Hnin K' w Hw K a Ha).
    +
      intros IP. apply PR. exact (proj1 (KA prist_win prist_tied) IP).
Qed.

Lemma aw_keepA : forall A LB ws ws' m mo, aw_holdsA A LB ws m mo -> wins_keep LB ws ws' -> aw_holdsA A LB ws' m mo.
Proof. intros A LB ws ws' m mo (W & HW & TI) WK. exists W. split; [exact HW| exact (ties_keep W A LB m mo ws ws' HW TI WK)]. Qed.
Lemma aw_ghost_apartA : forall A LB ws m mo, aw_holdsA A LB ws m mo -> ghost_apart ws.
Proof. intros A LB ws m mo (W & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _)). exact GA. Qed.

Definition AWA : alloc_world asegs IMGX :=
  AW asegs IMGX aw_holdsA aw_dep_asan aw_ceiling_asan aw_frameA aw_keepA aw_ghost_apartA
     (fun A LB ws m mo a H => aw_dep_ok_asan A LB m mo a (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b H => aw_blocks_ok_asan A LB m mo b (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b a H => aw_user_ok_asan A LB m mo b a (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b b' a H => aw_blocks_disj_asan A LB m mo b b' a (aw_holdsA_plain A LB ws m mo H))
     aw_ceiling_small_asan
     (fun A LB ws m mo b H => aw_blocks_lo_asan A LB m mo b (aw_holdsA_plain A LB ws m mo H)).

Definition heap_holdsA (dargs : list word) (m : amem) (mo : Model) : Prop := heap_holds asegs IMGX AWA Cw dargs m mo.
Definition heap_holdsX (dargs : list word) (m : amem) (mo : Model) : Prop :=
  exists md aw ws ca LB W, decode dargs = Some (md, aw, ws, ca) /\
    aw_holds_w W aw LB m mo /\ windows_wf ws LB (ATOP + 4096) /\ cw_holds Cw md ca LB ws m /\ ties W ws.
Lemma heap_holdsA_inv : forall dargs m mo, heap_holdsA dargs m mo -> heap_holdsX dargs m mo.
Proof. intros dargs m mo (md & aw & ws & ca & LB & D & (W & HA & TI) & WF & HC). exists md, aw, ws, ca, LB, W. auto. Qed.
Lemma heap_holdsA_intro : forall dargs m mo, heap_holdsX dargs m mo -> heap_holdsA dargs m mo.
Proof. intros dargs m mo (md & aw & ws & ca & LB & W & D & HA & WF & HC & TI). exists md, aw, ws, ca, LB. split; [exact D|]. split; [exists W; auto| auto]. Qed.
Lemma heap_holdsA_plain : forall dargs m mo, heap_holdsA dargs m mo -> heap_holds asegs IMGX AWA Cw dargs m mo.
Proof. intros dargs m mo H. exact H. Qed.

Lemma heap_frameA_v : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono asegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsA dargs m mo -> heap_holdsA dargs m' mo.
Proof.
  intros dargs m m' mo AG WM DM HH. apply heap_holdsA_inv in HH. destruct HH as (md & aw & ws & ca & LB & W & D & HA & WF & HC & TW).
  assert (HAa : aw_holds_asan aw LB m mo) by (exists W; exact HA).
  assert (INFP : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha I Wn. apply AG; [exact Ha|]. apply (proj2 (fp_spec IMGX dargs md aw ws ca a D)). tauto. }
  assert (NOTW : forall a, 0 <= a < ATOP + 4096 ->
            (forall w, In w ws -> w_kind w <> K_STACK -> ~ in_iv (w_iv w) a) -> ~ in_ws ws a).
  { intros a Ha H X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    - unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. ulia.
    - exact (H w Hw ltac:(rewrite K; discriminate) Hin).
    - exact (H w Hw ltac:(unfold K_SUB, K_STACK in *; ulia) Hin). }
  assert (DEPEQ : forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha Hd. destruct (aw_dep_ok_asan aw LB m mo a HAa Hd) as (C1 & NU & NI).
    apply INFP; [exact Ha| exact NI|]. apply NOTW; [exact C1|].
    intros w Hw NK Hin. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    + exact (NK K).
    + apply NU. unfold in_user. apply in_ivs_In. exists (w_iv w). auto.
    + apply NU. unfold in_user. apply in_ivs_In. exists b. auto. }
  destruct (aw_frame_w_v W aw LB m m' mo HA DEPEQ WM DM) as [ms2 HA2].
  apply heap_holdsA_intro. exists md, aw, ws, ca, LB, (set_ms W ms2). split; [exact D|]. split; [exact HA2|]. split; [exact WF|]. split; [| apply ties_set_ms; exact TW].
  apply (cw_frame Cw md ca LB ws m m' HC).
  intros a Ha U NH. apply in_ivs_In in U as (b & Hb & Hin).
  destruct (aw_blocks_ok_asan aw LB m mo b HAa Hb) as (B1 & B2 & B3 & B4 & B5).
  apply INFP; [exact Ha| exact (B5 a Hin)|]. apply NOTW; [unfold in_iv, aw_ceiling_asan in *; ulia|].
  intros w Hw NK Hw'. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [|exact Hw'].
  apply in_map. apply filter_In. split; [exact Hw|]. destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity].
Qed.

Lemma heap_frameA : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsA dargs m mo -> heap_holdsA dargs m' mo.
Proof.
  intros dargs m m' mo AG DM HH. apply (heap_frameA_v dargs m m' mo AG (wmono_of m m' DM)); [| exact HH].
  intros a Ha. apply DM. unfold AIMG_HI in Ha. lia.
Qed.

Lemma heap_frameX_v : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono asegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsX dargs m mo -> heap_holdsX dargs m' mo.
Proof. intros dargs m m' mo AG WM DM HH. apply heap_holdsA_inv. apply (heap_frameA_v dargs m m' mo AG WM DM). apply heap_holdsA_intro. exact HH. Qed.

Definition C0 (a : Z) : Prop := (0x10000 <= a < AIMG_HI) \/ (ATOP <= a < two64).

Definition cov1 (id : int) (dargs : list word) (z : Z) : Prop :=
  PrimInt63.eqb id OPID = true /\
  exists md aw ws ca, decode dargs = Some (md, aw, ws, ca) /\ (in_ws (heap_ws ws) z \/ sh_cov z).

Definition holdsA (id : int) (dargs : list word) (m : amem) (mo : Model) : Prop :=
  if PrimInt63.eqb id OPID then heap_holdsA dargs m mo else False.
Definition fpA (id : int) (dargs : list word) : list (Z * Z) := if PrimInt63.eqb id OPID then heap_fp IMGX dargs else [].
Lemma frameA : forall id args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (fpA id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  holdsA id args m model -> holdsA id args m' model.
Proof.
  intros id args m m' model AG DM H. unfold holdsA, fpA in *.
  destruct (PrimInt63.eqb id OPID); [| exact H]. exact (heap_frameA args m m' model AG DM H).
Qed.

Lemma H_ledA : forall id args m mo, PrimInt63.eqb id OPID = true -> holdsA id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Proof.
  intros id args m mo E H. unfold holdsA in H. rewrite E in H. apply heap_holdsA_inv in H.
  destruct H as (md & aw & ws & ca & LB & W & _ & HA & _). destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  exact (ACCT_led _ _ _ _ _ _ AC).
Qed.

Lemma LB_byte_cov : forall W aw LB m mo v z, aw_holds_w W aw LB m mo -> In v LB -> in_iv v z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Proof.
  intros W aw LB m mo v z HW Hv Hz. pose proof HW as (AH & HT & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 Vb)). left. unfold in_iv, user_iv in Hz. cbn [fst snd] in Hz. ulia.
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 (HT b Hb))). right. exact Hz.
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 (proj1 Vb))). right.
    destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (_ & _ & NP & _). pose proof (shlen_le7 (ab_size b) ltac:(ulia)).
    unfold in_iv, fsh_iv in Hz. cbn [fst snd] in Hz. ulia.
Qed.

Lemma H_covA : forall id args m mo z, holdsA id args m mo -> cov1 id args z ->
  PrimInt63.eqb id OPID = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H (E & md' & aw' & ws' & ca' & D' & HWs). split; [exact E|].
  unfold holdsA in H. rewrite E in H. apply heap_holdsA_inv in H. destruct H as (md & aw & ws & ca & LB & W & D & HA & WF & _).
  rewrite D in D'. injection D' as <- <- <- <-.
  destruct HWs as [HWs|SHC]; [| destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & _); exact (ACCT_cov_sh _ _ _ _ _ _ z AC SHC)].

  assert (INB : exists v, In v LB /\ in_iv v z).
  { unfold in_ws, heap_ws in HWs. apply in_ivs_In in HWs as (v & Hv & Hz). apply in_map_iff in Hv as (w & <- & Hw).
    apply filter_In in Hw as [Hw NK]. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & KD).
    destruct KD as [[K _]|[[_ HB]|[_ (b & Hb & SUB)]]].
    - rewrite K in NK. cbn in NK. discriminate.
    - exists (w_iv w). split; assumption.
    - exists b. split; [exact Hb| apply SUB; exact Hz]. }
  destruct INB as (v & Hv & Hz). exact (LB_byte_cov W aw LB m mo v z HA Hv Hz).
Qed.

Lemma H_matA : forall id args m mo mo', holdsA id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holdsA id args m mo'.
Proof.
  intros id args m mo mo' H SB ND NEW. unfold holdsA in *. destruct (PrimInt63.eqb id OPID); [| exact H].
  apply heap_holdsA_inv in H. destruct H as (md & aw & ws & ca & LB & W & D & HA & WF & HC & TW).
  apply heap_holdsA_intro. exists md, aw, ws, ca, LB, W. split; [exact D|]. split; [| split; [exact WF| split; [exact HC| exact TW]]].
  destruct HA as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & AC & HU & CLS & VFL & INC).
  repeat (split; [assumption|]). split; [eapply ACCT_mat; eassumption| split; [exact HU| split; [exact CLS| split; [exact VFL| exact INC]]]].
Qed.

Definition asan_heap_optable : St.optable :=
  asan_optable holdsA fpA frameA C0 cov1 COVP NMAX (fun id => PrimInt63.eqb id OPID) H_ledA H_covA H_matA.

Definition semvA (id : int) (dargs : list word) (m : amem) (mo : Model) (z : Z) : Prop :=
  PrimInt63.eqb id OPID = true /\
  exists md aw ws ca LB, decode dargs = Some (md, aw, ws, ca) /\ aw_holds_asan aw LB m mo /\
    exists v, In v LB /\ (in_iv v z \/ (user_band (fst v) /\ exists z0, in_iv v z0 /\ z = shad z0)).

Lemma H_semA : forall id args m mo z, holdsA id args m mo -> semvA id args m mo z ->
  PrimInt63.eqb id OPID = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z _ (E & md & aw & ws & ca & LB & D & [W HA] & v & Hv & CASE). split; [exact E|].
  destruct CASE as [Hz|(UB & z0 & Hz0 & ->)]; [exact (LB_byte_cov W aw LB m mo v z HA Hv Hz)|].
  pose proof HA as (AH & HT & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  destruct (LB_cases W aw LB m mo v HA Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - eapply (ACCT_cov aw _ _ _ _ _ mo b _ AC AH (proj1 Vb)). right.
    destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & HI & A8 & _). destruct (user_app_band _ _ BK NP) as [_ B2].
    unfold in_iv, user_iv in Hz0. cbn [fst snd] in Hz0.
    unfold shad, shlen. rewrite !Z.shiftr_div_pow2 by ulia. change (2 ^ 3) with 8. clear - Hz0 A8 NP B2. Z.div_mod_to_equations. ulia.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b HA Hb) as (T1 & T2 & T3). unfold twin_iv, user_band in UB. cbn [fst] in UB. ulia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b HA Vb) as (T1 & T2 & T3 & _). unfold fsh_iv, user_band in UB. cbn [fst] in UB. ulia.
Qed.

Lemma asan_heap_acc_user : forall (os : list St.oinst) (m : amem) (mo : Model) (acc : list (word * nat)),
  St.op_minv asan_heap_optable mo ->
  Forall (fun o => St.op_holds asan_heap_optable (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n ->
     St.op_cov asan_heap_optable os (bv_unsigned a + j) \/ Exists (fun o => semvA (fst o) (snd o) m mo (bv_unsigned a + j)) os) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ St.op_minv asan_heap_optable mo' /\
              Forall (fun o => St.op_holds asan_heap_optable (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  exact (asan_acc_user holdsA C0 cov1 COVP NMAX (fun id => PrimInt63.eqb id OPID) H_ledA H_covA H_matA semvA H_semA os m mo acc MI HO HC).
Qed.

Lemma twins_mapped : forall W aw LB m mo L' RNG' st' LBa' m', aw_holds_w W aw LB m mo -> AHEAP AI L' RNG' st' LBa' m' ->
  (forall b, In b (w_T W) -> In b LBa') ->
  forall a, in_ivs (map twin_iv (w_T W)) a -> m' (wa a) <> None.
Proof.
  intros W aw LB m mo L' RNG' st' LBa' m' HW AH' SUB a Ha. pose proof HW as (_ & HT & _).
  apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT).
  destruct (HT b HbT) as [_ HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
  assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
  { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
  pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' (SUB b HbT) HbH (proj1 G) (proj2 G)) as P.
  replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P.
Qed.

Lemma aw_real_nodelta : forall aw aw' LB m mo W RNG' st' m' mo',
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' (w_LBa W) m' -> ACCT aw' (w_L W) RNG' st' (w_LBa W) mo' ->
  (forall b x, In b (w_LBa W) -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  twins_pres (w_LBa W) m m' ->
  aw_realW aw' LB m' mo' (mkWit (w_L W) RNG' st' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
Proof.
  intros aw aw' LB m mo W RNG' st' m' mo' [HW EM] AH' AC' KEEPF TW.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  split; [| reflexivity]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|].
  split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' (fun b Hb => proj1 (HT b Hb)))|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'| split; [exact HU| split; [exact CLS| split]]].
  - apply (vfl_keep W aw LB m mo m' (conj HW EM)). intros b x [[Hb _] FK] Hx. exact (KEEPF b x Hb FK Hx).
  - intros b [HbL NFAb] HHb NTb. apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' HbL HHb TW HbL).
    intros g G0 G1. exact (INC b (conj HbL NFAb) HHb NTb g G0 G1).
Qed.

Lemma aw_real_twin_write : forall aw LB m mo W p A n (m' : amem) lo sp,
  aw_realW aw LB m mo W -> In (HB p A n) (w_T W) -> is_primary n = true ->
  ATOP + 4096 <= lo -> lo <= sp -> sp <= 2 ^ 47 ->
  munch [(lo, sp); (shad A, shad A + shlen (n + 7))] m m' -> wmono asegs m m' ->
  (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
  aw_realW aw LB m' mo (set_ms W m').
Proof.
  intros aw LB m mo W p A n m' lo sp [HW EM] HbT PRIM LO1 LO2 SP47 MU WM RDM.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as ATR.
  rewrite EM in AH. destruct (HT _ HbT) as [HbL HbH].
  destruct (LB_twin_facts W aw LB m mo _ HW HbT) as (T1 & T2 & T3). cbn [ab_addr ab_size] in T1, T2, T3.
  set (intw := fun x : word => (shad A <=? bv_unsigned x) && (bv_unsigned x <? shad A + shlen (n + 7))).
  assert (INTW : forall x, intw x = true <-> shad A <= bv_unsigned x < shad A + shlen (n + 7)).
  { intros x. unfold intw. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  assert (OUTM : forall x : word, intw x = false -> ~ (lo <= bv_unsigned x < sp) -> m' x = m x).
  { intros x NI NS. apply MU. cbn [ALib.Frame.outside]. split; [lia|]. split; [| exact I].
    destruct (intw x) eqn:E; [discriminate|]. assert (X : ~ (shad A <= bv_unsigned x < shad A + shlen (n + 7))) by (rewrite <- INTW; congruence). lia. }
  set (m1 := fun x : word => if intw x then m x else m' x).
  assert (AH1 : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m1).
  { eapply (AI_frame AI _ _ _ _ m m1 [(lo, sp)]); [exact AH | | |].
    - intros x OUT. cbn [ALib.Frame.outside] in OUT. unfold m1. destruct (intw x) eqn:E; [reflexivity|]. apply OUTM; [exact E| lia].
    - intros x Hx. unfold m1. destruct (intw x) eqn:E.
      + rewrite (wview_ext1 (fun y => if intw y then m y else m' y) m x); [exact Hx| rewrite E; reflexivity].
      + rewrite (wview_ext1 (fun y => if intw y then m y else m' y) m' x); [exact (WM x Hx)| rewrite E; reflexivity].
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. left. lia. }
  assert (AH' : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m').
  { eapply (AI_frame_twin AI _ _ _ _ m1 m' p A n AH1 HbL PRIM).
    - intros x OUT. cbn [ALib.Frame.outside] in OUT. unfold m1. destruct (intw x) eqn:E; [| reflexivity]. apply INTW in E. lia.
    - intros x Hx. destruct (intw x) eqn:E.
      + apply INTW in E. unfold wview.
        assert (MP : m' x <> None).
        { replace x with (wa (shad A + (bv_unsigned x - shad A))); [apply RDM; lia|]. unfold wa. replace (shad A + (bv_unsigned x - shad A)) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
        destruct (m' x); [discriminate| contradiction].
      + rewrite <- (wview_ext1 m1 m' x); [exact Hx| unfold m1; rewrite E; reflexivity].
    - exact RDM. }
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).

  assert (KEEPB : forall a, 0 <= a < ATOP + 4096 -> ~ (shad A <= a < shad A + shlen (n + 7)) -> m' (wa a) = m (wa a)).
  { intros a Ha NT. apply OUTM; [| rewrite UWA by lia; lia].
    destruct (intw (wa a)) eqn:E; [| reflexivity]. apply INTW in E. rewrite UWA in E by lia. contradiction. }
  split; [| reflexivity]. unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|].
  split.
  { intros a Ha. destruct (Z_le_dec (shad A) a) as [L1|]; [destruct (Z_lt_dec a (shad A + shlen (n + 7))) as [L2|]|].
    - replace a with (shad A + (a - shad A)) by lia. apply RDM. lia.
    - pose proof (MAP a Ha) as M0. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
      destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (U1 & U2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      rewrite KEEPB by lia. exact M0.
    - pose proof (MAP a Ha) as M0. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
      destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (U1 & U2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      rewrite KEEPB by lia. exact M0. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC| split; [exact HU| split; [exact CLS| split]]].
  -
    apply (vfl_agree W aw LB m mo m' HW). intros b x [[Hb NFA] HF] Hx. rewrite EM.
    destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _). destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
    apply KEEPB; lia.
  -
    intros b Vb HH NT g G0 G1. rewrite <- (INC b Vb HH NT g G0 G1).
    destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (Nb & BRb & _).
    assert (INB : in_iv (twin_iv b) (shad (ab_addr b) + g)).
    { unfold in_iv, twin_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
    destruct (in_twin_clear W aw LB m mo b _ HW Vb HH NT INB) as (R1 & NU & _).
    apply KEEPB; [exact R1|]. intros X. apply NU. apply in_ivs_In. exists (twin_iv (HB p A n)).
    split; [apply HLB; right; left; exists (HB p A n); split; [exact HbT| reflexivity]| unfold in_iv, twin_iv; cbn [fst snd ab_addr ab_size]; exact X].
Qed.

Lemma aw_real_frame_in : forall aw aw' LB m mo W RNG' st' c F n LBk m' mo' sp,
  aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) m' -> ACCT aw' (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) mo' ->
  aheap_pres (aci AI) LBk sp m m' -> n <= FRAME_MAX ->
  (forall b, In b LBk -> In b (w_LBa W)) -> (forall b, vis W b -> In b LBk) ->
  (exists flg, bytes_at asegs m' (F + n - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) (mkABlock (ABFake c) F n) flg) ->
  twins_pres (w_LBa W) m m' ->
  let fb := mkABlock (ABFake c) F n in
  let W1 := mkWit (w_L W) RNG' st' (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W) in
  aw_realW aw' ((F, n - 8) :: (shad F, shlen n) :: LB) m' mo' W1 /\ visf W1 fb
  /\ (forall a, in_iv (F, n - 8) a -> ~ in_user LB a) /\ (forall a, in_iv (shad F, shlen n) a -> ~ in_user LB a).
Proof.
  intros aw aw' LB m mo W RNG' st' c F n LBk m' mo' sp [HW EM] AH' AC' PRES NFM KEEP1 KEEP2 FLW TW fb W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  assert (FF : is_fake fb) by (exists c; reflexivity).
  destruct (AI_fake _ _ _ _ _ fb AH' ltac:(left; reflexivity) FF) as (BKF & HIF & A8F & N8F & NPF & _). cbn [ab_addr ab_size fb] in BKF, HIF, A8F, N8F, NPF.
  destruct (fsh_band _ _ BKF HIF A8F N8F ltac:(ulia)) as (FS1 & FS2 & FS3 & _). destruct (user_app_band _ _ BKF ltac:(ulia)) as [BF1 BF2].
  set (FA' := List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) in *.
  assert (INFA' : forall b, In b FA' <-> In b (w_FA W) /\ In b LBk).
  { intros b. unfold FA'. rewrite filter_In. destruct (in_dec ablock_eq_dec b LBk); split; intros [H1 H2]; try discriminate; auto. }
  assert (VIS1 : forall b, vis W1 b <-> b = fb \/ vis W b).
  { intros b. unfold vis, W1. cbn [w_LBa w_FA]. fold FA'. split.
    - intros [[<-|Hb] NF]; [left; reflexivity| right]. split; [exact (KEEP1 b Hb)|]. intros X. apply NF. apply INFA'. split; assumption.
    - intros [->|[Hb NF]]; [split; [left; reflexivity| intros X; apply INFA' in X as [_ X]; exact (NIN X)]|].
      split; [right; apply KEEP2; split; assumption| intros X; apply INFA' in X as [X _]; exact (NF X)]. }
  assert (TK : forall b, In b (w_T W) -> In b LBk).
  { intros b Hb. destruct (HT b Hb) as [HbL HbH]. apply KEEP2. split; [exact HbL|]. intros X. exact (heap_not_fake b HbH (proj2 (HFA b X))). }
  assert (DISJ : forall b, In b LBk -> F + n <= ab_addr b \/ ab_addr b + ab_size b <= F).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ fb b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size fb] in D. exact D. }
  assert (HW1 : aw_holds_w W1 aw' ((F, n - 8) :: (shad F, shlen n) :: LB) m' mo').
  { unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc W1]. fold FA'.
    split; [exact AH'|]. split. { intros b Hb. split; [right; exact (TK b Hb)| exact (proj2 (HT b Hb))]. }
    split; [exact ND|]. split. { intros b Hb. apply INFA' in Hb as [Hb HbK]. split; [right; exact HbK| exact (proj2 (HFA b Hb))]. }
    split; [apply NoDup_filter; exact NDF|]. split.
    { intros v. cbn [In]. rewrite (HLB v). unfold visf. split.
      - intros [<-|[<-|[(b & Vb & ->)|[H|(b & [Vb HF] & ->)]]]].
        + left. exists fb. split; [apply VIS1; left; reflexivity| reflexivity].
        + right. right. exists fb. split; [split; [apply VIS1; left; reflexivity| exact FF]| reflexivity].
        + left. exists b. split; [apply VIS1; right; exact Vb| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [apply VIS1; right; exact Vb| exact HF]| reflexivity].
      - intros [(b & Vb & ->)|[H|(b & [Vb HF] & ->)]].
        + apply VIS1 in Vb as [->|Vb]; [left; reflexivity| right; right; left; exists b; split; [exact Vb| reflexivity]].
        + right. right. right. left. exact H.
        + apply VIS1 in Vb as [->|Vb]; [right; left; reflexivity| right; right; right; right; exists b; split; [split; assumption| reflexivity]]. }
    split; [intros a _ _; reflexivity|].
    split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' (fun b Hb => or_intror (TK b Hb)))|].
    split; [exact ZC0|]. split.
    { assert (LE : (length FA' <= length (w_FA W))%nat) by (unfold FA'; apply filter_length_le). ulia. }
    split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [cbn [ab_size fb]; exact NFM| exact (CLS b (KEEP1 b Hb) FK)]. }
    split.
    2:{
        intros b Vb1 HHb NTb. apply VIS1 in Vb1 as [->|Vb]; [exfalso; exact (heap_not_fake fb HHb FF)|].
        apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(right; exact (KEEP2 b Vb)) HHb TW (proj1 Vb)).
        intros g G0 G1. exact (INC b Vb HHb NTb g G0 G1). }

    intros b [Vb1 FKb]. apply VIS1 in Vb1 as [->|Vb]; [cbn [ab_addr ab_size fb]; exact FLW|].
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| split; [exact Vb| exact FKb]]. intros b0 x [Vb0 _] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH (proj1 Vb0)) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block LBk sp m m' b0 x PRES (KEEP2 b0 Vb0)); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [apply VIS1; left; reflexivity| exact FF]|].
  split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b (KEEP2 b Vb)). ulia.
    + destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & _). ulia.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    pose proof (shlen_le7 n ltac:(ulia)) as LEn.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b HW Vb) as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj F n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b (TK b Hb)) A8F H4 ltac:(ulia) Hva).
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj F n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b (KEEP2 b (proj1 Vb))) A8F H4 ltac:(ulia) ltac:(ulia)).
Qed.

Lemma iv_origin : forall W aw LB m mo, aw_holds_w W aw LB m mo ->
     (forall b b', vis W b -> vis W b' -> user_iv b = user_iv b' -> b = b')
  /\ (forall b b', vis W b -> In b' (w_T W) -> user_iv b <> twin_iv b')
  /\ (forall b b', vis W b -> visf W b' -> user_iv b <> fsh_iv b')
  /\ (forall b b', In b (w_T W) -> In b' (w_T W) -> twin_iv b = twin_iv b' -> b = b')
  /\ (forall b b', In b (w_T W) -> visf W b' -> twin_iv b <> fsh_iv b')
  /\ (forall b b', visf W b -> visf W b' -> fsh_iv b = fsh_iv b' -> b = b').
Proof.
  intros W aw LB m mo HW. pose proof HW as (AH & HT & _).
  repeat split.
  - intros b b' Vb Vb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) (proj1 Vb')). unfold user_iv in E. injection E as E1 _. rewrite E1. reflexivity.
  - intros b b' Vb Hb' E. destruct (LB_user_facts W aw LB m mo b HW Vb) as (NP & B1 & _). destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & T3).
    unfold user_iv, twin_iv in E. injection E as E1 _. ulia.
  - intros b b' Vb Vb' E. destruct (LB_user_facts W aw LB m mo b HW Vb) as (NP & B1 & _). destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & T3 & _).
    unfold user_iv, fsh_iv in E. injection E as E1 _. ulia.
  - intros b b' Hb Hb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (HT b' Hb'))). unfold twin_iv in E. injection E as E1 _. exact E1.
  - intros b b' Hb Vb' E. assert (b = b') as <-.
    { apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (proj1 Vb'))). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1. }
    exact (heap_not_fake b (proj2 (HT b Hb)) (proj2 Vb')).
  - intros b b' Vb Vb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (proj1 Vb'))). unfold fsh_iv in E. injection E as E1 _. exact E1.
Qed.

Lemma aw_real_frame_out : forall aw aw' LB m mo W RNG' st' fb LBk m' mo',
  aw_realW aw LB m mo W -> visf W fb ->
  AHEAP AI (w_L W) RNG' st' LBk m' -> ACCT aw' (w_L W) RNG' st' LBk mo' ->
  (forall b, In b LBk <-> In b (w_LBa W) /\ b <> fb) ->
  (forall b x, In b (w_LBa W) -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  twins_pres (w_LBa W) m m' ->
  aw_realW aw' (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m' mo'
          (mkWit (w_L W) RNG' st' LBk (w_T W) (w_FA W) m' (w_zc W)).
Proof.
  intros aw aw' LB m mo W RNG' st' fb LBk m' mo' [HW EM] VF AH' AC' RM KEEPF TW.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  destruct (iv_origin W aw LB m mo HW) as (O1 & O2 & O3 & O5 & O6 & O8).
  destruct VF as [[HfL NfA] FF].
  set (W1 := mkWit (w_L W) RNG' st' LBk (w_T W) (w_FA W) m' (w_zc W)).
  assert (VIS1 : forall b, vis W1 b <-> vis W b /\ b <> fb).
  { intros b. unfold vis, W1. cbn [w_LBa w_FA]. rewrite RM. tauto. }
  assert (TK : forall b, In b (w_T W) -> In b LBk).
  { intros b Hb. destruct (HT b Hb) as [HbL HbH]. apply RM. split; [exact HbL|]. intros ->. exact (heap_not_fake fb HbH FF). }
  split; [| reflexivity]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split. { intros b Hb. split; [exact (TK b Hb)| exact (proj2 (HT b Hb))]. }
  split; [exact ND|]. split. { intros b Hb. destruct (HFA b Hb) as [HbL HF]. split; [apply RM; split; [exact HbL| intros ->; exact (NfA Hb)]| exact HF]. }
  split; [exact NDF|]. split.
  { intros v. fold W1. split.
    - intros Hv. apply in_remove in Hv as [Hv N2]. apply in_remove in Hv as [Hv N1].
      destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
      + left. exists b. split; [apply VIS1; split; [exact Vb| intros ->; apply N1; reflexivity]| reflexivity].
      + right. left. exists b. split; [exact Hb| reflexivity].
      + right. right. exists b. split; [split; [apply VIS1; split; [exact (proj1 Vb)| intros ->; apply N2; reflexivity]| exact (proj2 Vb)]| reflexivity].
    - intros Hv. assert (VFB : visf W fb) by (split; [split; assumption| exact FF]).
      destruct Hv as [(b & Vb & ->)|[(b & Hb & ->)|(b & [Vb HF] & ->)]].
      + apply VIS1 in Vb as [Vb NE]. apply in_in_remove; [exact (O3 b fb Vb VFB)|]. apply in_in_remove; [intros E; exact (NE (O1 b fb Vb (proj1 VFB) E))|].
        apply HLB. left. exists b. split; [exact Vb| reflexivity].
      + apply in_in_remove; [exact (O6 b fb Hb VFB)|]. apply in_in_remove; [intros E; exact (O2 fb b (proj1 VFB) Hb (eq_sym E))|].
        apply HLB. right. left. exists b. split; [exact Hb| reflexivity].
      + apply VIS1 in Vb as [Vb NE]. apply in_in_remove; [intros E; exact (NE (O8 b fb (conj Vb HF) VFB E))|].
        apply in_in_remove; [intros E; exact (O3 fb b (proj1 VFB) (conj Vb HF) (eq_sym E))|].
        apply HLB. right. right. exists b. split; [split; assumption| reflexivity]. }
  split; [intros a _ _; reflexivity|].
  split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' TK)|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
  split. { intros b Hb FK. exact (CLS b (proj1 (proj1 (RM b) Hb)) FK). }
  split.
  2:{ intros b Vb1 HHb NTb. apply VIS1 in Vb1 as [Vb NEb].
      apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(apply RM; split; [exact (proj1 Vb)| exact NEb]) HHb TW (proj1 Vb)).
      intros g G0 G1. exact (INC b Vb HHb NTb g G0 G1). }
  intros b [Vb1 FKb]. apply VIS1 in Vb1 as [Vb NEb].
  apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| split; [exact Vb| exact FKb]]. intros b0 x [[Hb0 _] FK0] Hx. exact (KEEPF b0 x Hb0 FK0 Hx).
Qed.

Lemma aw_real_flag : forall aw LB m mo W fb, aw_realW aw LB m mo W -> visf W fb ->
  exists flg, bytes_at asegs m (ab_addr fb + ab_size fb - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) fb flg.
Proof.
  intros aw LB m mo W fb [HW EM] VF. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VFL & _).
  rewrite <- EM. exact (VFL fb VF).
Qed.

Lemma aw_real_flag_rng : forall aw LB m mo W fb, aw_realW aw LB m mo W -> visf W fb ->
  exists flg, bytes_at asegs m (ab_addr fb + ab_size fb - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) fb flg
    /\ 0 <= flg < 2 ^ 64 /\ forall RNG', FRNG AI AI_fake (w_L W) RNG' -> rng RNG' flg 1.
Proof.
  intros aw LB m mo W fb AR VF. destruct (aw_real_flag aw LB m mo W fb AR VF) as (flg & BA & FL). exists flg. split; [exact BA|]. split; [exact FL|].
  destruct AR as [HW EM]. pose proof HW as (AH & _). rewrite EM in AH.
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH (proj1 (proj1 VF))) as (_ & _ & BAND & _ & A1 & A2). pose proof atop_range as ATR.
  split; [unfold AIMG_HI, KLS in BAND; lia|].
  intros RNG' FR. apply (rng_sub' RNG' (al_fake (w_L W)) 11571200 flg 1 (fk_area AI AI_fake _ _ FR)). lia.
Qed.
Lemma aw_real_fake_free : forall aw aw' LB m mo W fb flg mo',
  aw_realW aw LB m mo W -> visf W fb -> flag_law AI (w_L W) fb flg ->
  ACCT aw' (w_L W) (w_RNG W) (w_st W) (lb_del fb (w_LBa W)) mo' ->
  let m' := write_to_mem m (wa flg) [Z_to_bv 8 0] in
  aw_realW aw' (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m' mo'
          (mkWit (w_L W) (w_RNG W) (w_st W) (lb_del fb (w_LBa W)) (w_T W) (w_FA W) m' (w_zc W))
  /\ wr_at asegs m flg 1
  /\ (forall x : word, bv_unsigned x <> flg -> m' x = m x).
Proof.
  intros aw aw' LB m mo W fb flg mo' AR VF FL AC' m'. pose proof AR as [HW EM]. pose proof HW as (AH & _).
  destruct VF as [[HfL NfA] FF]. rewrite EM in AH.
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH HfL) as (AH' & WR & BAND & NOBLK & _).
  assert (F0 : 0 <= flg /\ flg + 1 <= 2^64) by (pose proof atop_range as AR'; unfold AIMG_HI, KLS in BAND; lia).
  assert (OUT : forall x : word, bv_unsigned x <> flg -> m' x = m x).
  { intros x NE. unfold m'. rewrite (write_to_mem_spec [Z_to_bv 8 0] m flg x (proj1 F0) ltac:(cbn [length]; lia)). cbn [length].
    destruct (Z.leb_spec0 flg (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (flg + Z.of_nat 1)); cbn [andb]; try reflexivity. exfalso. lia. }
  split; [| split; [exact WR| exact OUT]].
  apply (aw_real_frame_out aw aw' LB m mo W (w_RNG W) (w_st W) fb (lb_del fb (w_LBa W)) m' mo' AR (conj (conj HfL NfA) FF) AH' AC').
  - intros b. apply lb_del_In.
  - intros b x Hb _ Hx. apply OUT. intros E.
    assert (UX : bv_unsigned (wa x) = x).
    { unfold wa. apply Z_to_bv_small. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _). destruct (user_app_band _ _ BK NP) as [_ B2].
      pose proof atop_range as AR'. unfold bv_modulus. lia. }
    rewrite UX in E. subst x. exact (NOBLK b Hb Hx).
  -
    intros p0 A0 n0 Hin PR i Hi. apply OUT.
    destruct (heap_block_facts _ _ _ _ _ (HB p0 A0 n0) AH Hin ltac:(exists p0; reflexivity)) as (N0 & BR0 & _). cbn [ab_addr ab_size] in N0, BR0.
    destruct (twin_band _ _ BR0 N0) as (T1 & T2 & _). pose proof atop_range as AR'. unfold AIMG_HI, KLS in BAND.
    unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma aw_real_burn : forall aw LB m mo W c,
  aw_realW aw LB m mo W -> 0 <= c <= w_zc W ->
  aw_realW aw LB m mo (mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (w_FA W) (w_ms W) (w_zc W - c)).
Proof.
  intros aw LB m mo W c [HW EM] C. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  split; [| exact EM]. unfold aw_holds_w, vis, visf. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [exact EQ|]. split; [exact MAP|]. split; [ulia|]. split; [ulia|]. split; [exact AC| split; [exact HU| split; [exact CLS| split; [exact VFL| exact INC]]]].
Qed.

Lemma aw_real_abandon : forall aw LB m mo W fb c,
  aw_realW aw LB m mo W -> visf W fb -> 1 <= c <= w_zc W ->
  aw_realW aw (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m mo
          (mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (fb :: w_FA W) (w_ms W) (w_zc W - c)).
Proof.
  intros aw LB m mo W fb c [HW EM] VFB C. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  destruct (iv_origin W aw LB m mo HW) as (O1 & O2 & O3 & O5 & O6 & O8).
  pose proof VFB as [[HfL NfA] FF].
  split; [| exact EM]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split; [exact HT|]. split; [exact ND|].
  split. { intros b [<-|Hb]; [split; assumption| exact (HFA b Hb)]. }
  split; [constructor; assumption|]. split.
  { intros v. unfold vis, visf. cbn [In w_LBa w_FA]. split.
    - intros Hv. apply in_remove in Hv as [Hv N2]. apply in_remove in Hv as [Hv N1].
      destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
      + left. exists b. split; [| reflexivity]. split; [exact (proj1 Vb)|]. intros [<-|X]; [apply N1; reflexivity| exact (proj2 Vb X)].
      + right. left. exists b. split; [exact Hb| reflexivity].
      + right. right. exists b. split; [| reflexivity]. split; [| exact (proj2 Vb)]. split; [exact (proj1 (proj1 Vb))|].
        intros [<-|X]; [apply N2; reflexivity| exact (proj2 (proj1 Vb) X)].
    - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + assert (Vb : vis W b) by (split; [exact Hb| intros X; apply NF; right; exact X]).
        assert (NE : b <> fb) by (intros ->; apply NF; left; reflexivity).
        apply in_in_remove; [exact (O3 b fb Vb VFB)|]. apply in_in_remove; [intros E; exact (NE (O1 b fb Vb (proj1 VFB) E))|].
        apply HLB. left. exists b. split; [exact Vb| reflexivity].
      + apply in_in_remove; [exact (O6 b fb Hb VFB)|].
        apply in_in_remove; [intros E; exact (O2 fb b (proj1 VFB) Hb (eq_sym E))|]. apply HLB. right. left. exists b. split; [exact Hb| reflexivity].
      + assert (Vb : visf W b) by (split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact HF]).
        assert (NE : b <> fb) by (intros ->; apply NF; left; reflexivity).
        apply in_in_remove; [intros E; exact (NE (O8 b fb Vb VFB E))|].
        apply in_in_remove; [intros E; exact (O3 fb b (proj1 VFB) Vb (eq_sym E))|]. apply HLB. right. right. exists b. split; [exact Vb| reflexivity]. }
  split; [exact EQ|]. split; [exact MAP|].
  split; [ulia|]. split; [cbn [length]; ulia|]. split; [exact AC| split; [exact HU| split; [exact CLS| split]]].
  - intros b [[Hb NF] FK]. apply VFL. split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact FK].
  - intros b [Hb NF] HHb NTb. apply (INC b); [split; [exact Hb| intros X; apply NF; right; exact X]| exact HHb| exact NTb].
Qed.

Lemma aw_real_cls : forall aw LB m mo W c F n, aw_realW aw LB m mo W -> In (mkABlock (ABFake c) F n) (w_LBa W) -> c <= 2.
Proof.
  intros aw LB m mo W c F n [HW EM] Hb. pose proof HW as (AH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLS & _).
  assert (FK : is_fake (mkABlock (ABFake c) F n)) by (exists c; reflexivity).
  pose proof (CLS _ Hb FK) as SZ. destruct (fk_class AI AI_fake _ _ _ _ _ _ AH Hb FK) as (c' & K & C0 & EN).
  cbn [ab_kind ab_size] in K, EN, SZ. injection K as <-. unfold FRAME_MAX in SZ.
  destruct (Z_le_gt_dec c 2) as [LE|GT]; [exact LE| exfalso].
  pose proof (Z.pow_le_mono_r 2 3 c ltac:(lia) ltac:(lia)) as P. change (2 ^ 3) with 8 in P. lia.
Qed.

Lemma filter_length_split : forall {T} (f p : T -> bool) (l : list T),
  length (List.filter f l) = (length (List.filter (fun x => f x && p x) l) + length (List.filter (fun x => f x && negb (p x)) l))%nat.
Proof. intros T f p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (f x), (p x); cbn [andb negb length]; lia. Qed.

Lemma aw_real_fake_count : forall aw LB m mo W ws, aw_realW aw LB m mo W -> ties W ws ->
  Z.of_nat (length (List.filter fakeb (w_LBa W))) <= Z.of_nat (length ws) + ZTOTAL.
Proof.
  intros aw LB m mo W ws [HW EM] (T1 & T2 & T3 & _). pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & _).
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as NDL.
  set (inFA := fun b : ablock => if in_dec ablock_eq_dec b (w_FA W) then true else false).
  rewrite (filter_length_split fakeb inFA (w_LBa W)).
  assert (L1 : (length (List.filter (fun x => fakeb x && inFA x) (w_LBa W)) <= length (w_FA W))%nat).
  { apply NoDup_incl_length; [apply NoDup_filter; exact NDL|]. intros b Hb. apply filter_In in Hb as [_ Hb]. apply andb_prop in Hb as [_ Hb].
    unfold inFA in Hb. destruct (in_dec ablock_eq_dec b (w_FA W)); [assumption| discriminate]. }
  assert (L2 : (length (List.filter (fun x => fakeb x && negb (inFA x)) (w_LBa W)) <= length ws)%nat).
  { set (fw := fun b : ablock => Win (ab_addr b) (ab_size b - 8) K_FRAMEz).
    rewrite <- (length_map fw). apply NoDup_incl_length.
    - apply Finite.Injective_map_NoDup_in; [| apply NoDup_filter; exact NDL].
      intros b b' Hb Hb' E. apply filter_In in Hb as [Hb _]. apply filter_In in Hb' as [Hb' _]. unfold fw in E. injection E as E1 E2.
      destruct (ablock_eq_dec b b') as [->|NE]; [reflexivity| exfalso].
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NE) as D.
      destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & _). destruct (blk_facts _ _ _ _ _ b' AH Hb') as (NP' & _). lia.
    - intros w Hw. apply in_map_iff in Hw as (b & <- & Hb). apply filter_In in Hb as [HbL Hb]. apply andb_prop in Hb as [FK NF].
      apply fakeb_spec in FK. unfold inFA in NF. destruct (in_dec ablock_eq_dec b (w_FA W)) as [|NI]; [discriminate|].
      exact (proj1 (T3 b (conj (conj HbL NI) FK))). }
  lia.
Qed.

Lemma frame_in_visf : forall aw LB m mo W RNG' st' c F n LBk (m' : amem),
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) m' ->
  (forall b, In b LBk -> In b (w_LBa W)) -> (forall b, vis W b -> In b LBk) ->
  let fb := mkABlock (ABFake c) F n in
  let W1 := mkWit (w_L W) RNG' st' (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W) in
  forall b, visf W1 b <-> b = fb \/ visf W b.
Proof.
  intros aw LB m mo W RNG' st' c F n LBk m' [HW EM] AH' KEEP1 KEEP2 fb W1 b.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  assert (FF : is_fake fb) by (exists c; reflexivity).
  unfold visf, vis, W1. cbn [w_LBa w_FA]. rewrite filter_In. split.
  - intros [[[<-|Hb] NF] FK]; [left; reflexivity| right]. split; [split; [exact (KEEP1 b Hb)|]| exact FK].
    intros X. apply NF. split; [exact X|]. destruct (in_dec ablock_eq_dec b LBk); [reflexivity| contradiction].
  - intros [->|[[Hb NF] FK]].
    + split; [split; [left; reflexivity|]| exact FF]. intros [_ X]. destruct (in_dec ablock_eq_dec fb LBk) as [I|]; [exact (NIN I)| discriminate].
    + split; [split; [right; apply KEEP2; split; assumption|]| exact FK]. intros [X _]. exact (NF X).
Qed.

Lemma ties_frame_in : forall W W1 ws ws' fb,
  ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W -> is_fake fb -> (forall b, visf W1 b <-> b = fb \/ visf W b) ->
  (forall w, In w ws' <-> In w ws \/ w = Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz \/ w = Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) -> ghost_apart ws' ->
  (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 ws ws' fb (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EZ FF EV WS HV GAN PS. unfold ties. rewrite ET, EZ.
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb FF); reflexivity).
  split. { intros b Hb. apply WS. left. exact (T1 b Hb). }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]]; [exact (T2 w Hw K)| |]; cbn [w_kind] in K; unfold K_TWINz, K_FRAMEz, K_FTWINz in K; lia. }
  split. { intros b Vb. apply EV in Vb as [->|Vb]; [split; apply WS; [right; left| right; right]; reflexivity|].
           destruct (T3 b Vb) as [X Y]. split; apply WS; left; assumption. }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]].
           - destruct (T4 w Hw K) as (b & Vb & E). exists b. split; [apply EV; right; exact Vb| exact E].
           - exists fb. split; [apply EV; left; reflexivity|]. unfold w_iv. cbn [w_lo w_len]. symmetry. exact UF.
           - cbn [w_kind] in K. unfold K_FRAMEz, K_FTWINz in K. lia. }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]].
           - destruct (T5 w Hw K) as (b & Vb & E). exists b. split; [apply EV; right; exact Vb| exact E].
           - cbn [w_kind] in K. unfold K_FRAMEz, K_FTWINz in K. lia.
           - exists fb. split; [apply EV; left; reflexivity| reflexivity]. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [Hw|[->| ->]]; [exact (T6 w Hw K Z0 B0)| |]; cbn [w_kind] in K; unfold K_STACK, K_FRAMEz, K_FTWINz in K; lia. }
  split; [apply WS; left; exact T7|].
  split. { intros w Hw K P. apply WS in Hw as [Hw|[->| ->]]; [exact (T8 w Hw K P)| |]; cbn [w_kind] in K; unfold K_STACK, K_FRAMEz, K_FTWINz in K; lia. }
  split; [| split; [exact GAN| intros IP; apply PS, PR; apply WS in IP as [IP|[E|E]]; [exact IP| |]; exfalso; unfold prist_win in E; injection E as _ _ E; unfold K_STACK, K_FRAMEz, K_FTWINz in E; lia]].
  intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & X). exists w. split; [apply WS; left; exact Hw| exact X].
Qed.

Lemma frame_windows_inj : forall W aw LB m mo b fb, aw_holds_w W aw LB m mo -> visf W b -> visf W fb ->
  (Win (ab_addr b) (ab_size b - 8) K_FRAMEz = Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz
   \/ Win (shad (ab_addr b)) (shlen (ab_size b)) K_FTWINz = Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) -> b = fb.
Proof.
  intros W aw LB m mo b fb HW Vb Vf E. pose proof HW as (AH & _).
  apply (shadow_iv_inj _ _ _ _ _ b fb AH (proj1 (proj1 Vb)) (proj1 (proj1 Vf))).
  destruct E as [E|E]; injection E as E1 _; [rewrite E1; reflexivity| exact E1].
Qed.
Lemma ties_frame_out : forall W W1 aw LB m mo ws ws' fb,
  aw_holds_w W aw LB m mo -> ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W -> visf W fb -> (forall b, visf W1 b <-> visf W b /\ b <> fb) ->
  (forall w, In w ws' <-> In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) ->
  (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 aw LB m mo ws ws' fb HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EZ VF EV WS HV PS. unfold ties. rewrite ET, EZ.
  assert (KEEPK : forall w, In w ws -> w_kind w <> K_FRAMEz -> w_kind w <> K_FTWINz -> In w ws').
  { intros w Hw N1 N2. apply WS. split; [exact Hw|]. split; intros ->; [apply N1| apply N2]; reflexivity. }
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb (proj2 VF)); reflexivity).
  split. { intros b Hb. apply KEEPK; [exact (T1 b Hb)| |]; cbn [w_kind]; unfold K_TWINz, K_FRAMEz, K_FTWINz; lia. }
  split. { intros w Hw K. apply WS in Hw as [Hw _]. exact (T2 w Hw K). }
  split. { intros b Vb. apply EV in Vb as [Vb NE]. destruct (T3 b Vb) as [X Y].
           split; apply WS; (split; [assumption|]); split; intros E;
             try (apply NE; apply (frame_windows_inj W aw LB m mo b fb HW Vb VF); (left; exact E) || (right; exact E)); discriminate E. }
  split. { intros w Hw K. apply WS in Hw as (Hw & N1 & _). destruct (T4 w Hw K) as (b & Vb & E). exists b. split; [| exact E]. apply EV. split; [exact Vb|].
           intros ->. apply N1. destruct w as [lo len kd]. unfold w_iv in E. cbn [w_lo w_len w_kind] in E, K. rewrite UF in E. injection E as -> ->. rewrite K. reflexivity. }
  split. { intros w Hw K. apply WS in Hw as (Hw & _ & N2). destruct (T5 w Hw K) as (b & Vb & E). exists b. split; [| exact E]. apply EV. split; [exact Vb|].
           intros ->. apply N2. destruct w as [lo len kd]. unfold w_iv, fsh_iv in E. cbn [w_lo w_len w_kind] in E, K. injection E as -> ->. rewrite K. reflexivity. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [Hw _]. exact (T6 w Hw K Z0 B0). }
  split; [apply KEEPK; [exact T7| |]; unfold zc_win; cbn [w_kind]; unfold K_STACK, K_FRAMEz, K_FTWINz; lia|].
  split. { intros w Hw K P. apply WS in Hw as [Hw _]. exact (T8 w Hw K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (proj1 (WS w) Hw))]| intros IP; exact (PS (PR (proj1 (proj1 (WS _) IP))))]].
  intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & HK & X). exists w. split; [| split; [exact HK| exact X]].
  apply KEEPK; [exact Hw| |]; unfold heap_kind, K_GHOST, K_FRAMEz, K_FTWINz in *; lia.
Qed.

Lemma ties_abandon : forall W W1 aw LB m mo ws ws' fb c,
  aw_holds_w W aw LB m mo -> ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W - c -> c <= w_zc W -> visf W fb -> (forall b, visf W1 b <-> visf W b /\ b <> fb) ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz
                           /\ w <> zc_win (w_zc W)) \/ w = zc_win (w_zc W - c)) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) ->
  ZC_BASE + (w_zc W - c) < ZC_BAND -> (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 aw LB m mo ws ws' fb c HW TI ET EZ CZ VF EV WS HV ZB PS.

  set (wsm := List.filter (fun w => if window_eq_dec w (Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz) then false
                                     else if window_eq_dec w (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) then false else true) ws).
  assert (WSM : forall w, In w wsm <-> In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz).
  { intros w. unfold wsm. rewrite filter_In.
    destruct (window_eq_dec w (Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz)); [split; [intros [_ X]; discriminate| intros (_ & X & _); contradiction]|].
    destruct (window_eq_dec w (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz)); [split; [intros [_ X]; discriminate| intros (_ & _ & X); contradiction]|]. tauto. }
  set (Wm := mkWit (w_L W1) (w_RNG W1) (w_st W1) (w_LBa W1) (w_T W1) (w_FA W1) (w_ms W1) (w_zc W)).
  assert (TM : ties Wm wsm).
  { apply (ties_frame_out W Wm aw LB m mo ws wsm fb HW TI); [exact ET| reflexivity| exact VF| | exact WSM| exact HV| exact PS].
    intros b. unfold Wm, visf, vis. cbn [w_LBa w_FA]. exact (EV b). }
  apply (ties_burn Wm W1 wsm ws' c TM); [reflexivity| intros b; unfold Wm, visf, vis; cbn [w_LBa w_FA]; reflexivity| exact EZ| exact CZ| | intros b _ V; exact V| exact ZB| intros P; exact P].
  intros w. rewrite (WS w). unfold Wm. cbn [w_zc]. rewrite (WSM w). tauto.
Qed.

Lemma ghost_window_entry : forall W aw LB m mo ws w, aw_holds_w W aw LB m mo -> ties W ws -> In w ws ->
  (w_kind w = K_TWINz \/ w_kind w = K_FRAMEz \/ w_kind w = K_FTWINz) ->
  In (w_iv w) LB /\ forall b, In b LB -> b <> w_iv w -> forall a, in_iv (w_iv w) a -> ~ in_iv b a.
Proof.
  intros W aw LB m mo ws w HW (T1 & T2 & T3 & T4 & T5 & _) Hw K. pose proof HW as (_ & _ & _ & _ & _ & HLB & _).
  assert (INW : In (w_iv w) LB).
  { apply HLB. destruct K as [K|[K|K]].
    - destruct (T2 w Hw K) as (b & Hb & E). right. left. exists b. split; [exact Hb| exact E].
    - destruct (T4 w Hw K) as (b & Vb & E). left. exists b. split; [exact (proj1 Vb)| exact E].
    - destruct (T5 w Hw K) as (b & Vb & E). right. right. exists b. split; [exact Vb| exact E]. }
  split; [exact INW|]. intros b Hb NE a Ha.
  destruct (Z.eq_dec (fst (w_iv w)) (fst b)) as [EA|NA].
  - exfalso. apply NE. destruct b as [A0 n0]. destruct (w_iv w) as [A1 n1] eqn:EW. cbn [fst] in EA. subst A1.
    rewrite (LB_same_addr W aw LB m mo A0 n1 n0 HW INW Hb). reflexivity.
  - exact (aw_blocks_disj_asan aw LB m mo (w_iv w) b a (ex_intro _ W HW) INW Hb NA Ha).
Qed.

Lemma shadow_in_law_w : forall W aw LB m mo b g, aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  0 <= g -> 8 * g < ab_size b ->
  m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof. intros W aw LB m mo b g HW Vb HH NT G0 G1. exact (proj2 (proj2 (twin_out_w W aw LB m mo b HW Vb HH NT)) g G0 G1). Qed.

Lemma LB_entry_heap : forall W aw LB m mo ws v, aw_holds_w W aw LB m mo -> ties W ws -> In v LB -> user_band (fst v) ->
  (forall w, In w ws -> w_kind w = K_FRAMEz -> w_iv w <> v) ->
  exists b, vis W b /\ is_heap b /\ v = user_iv b /\ (In b (w_T W) <-> In (twin_iv b) LB).
Proof.
  intros W aw LB m mo ws v HW (T1 & T2 & T3 & _) Hv UB NF. pose proof HW as (AH & HT & _ & _ & _ & HLB & _).
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - exists b. split; [exact Vb|]. destruct (kind_cases b) as [HH|HF].
    + split; [exact HH|]. split; [reflexivity|]. split.
      * intros HbT. apply HLB. right. left. exists b. split; [exact HbT| reflexivity].
      * intros IN. destruct (LB_cases W aw LB m mo _ HW IN) as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
        -- exfalso. destruct (LB_user_facts W aw LB m mo b' HW Vb') as (NP' & B1 & _). pose proof (usz_le b') as UL.
           destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (N & BR & _). destruct (twin_band _ _ BR N) as (TB1 & TB2 & TB3 & _).
           unfold twin_iv, user_iv in E. injection E as E1 _. lia.
        -- replace b with b'; [exact Hb'|]. symmetry. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) (proj1 (HT b' Hb'))).
           unfold twin_iv in E. injection E as E1 _. exact E1.
        -- exfalso. destruct Vb' as [[Hb'L _] HF']. assert (b = b') as <-; [| exact (heap_not_fake b HH HF')].
           apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) Hb'L). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1.
    + exfalso. destruct (T3 b (conj Vb HF)) as [WF0 _]. apply (NF _ WF0 eq_refl). unfold w_iv, user_iv. cbn [w_lo w_len]. rewrite (usz_fake b HF). reflexivity.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (X1 & X2 & X3). unfold user_band, twin_iv in UB. cbn [fst] in UB. lia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (X1 & X2 & X3 & _). unfold user_band, fsh_iv in UB. cbn [fst] in UB. lia.
Qed.

Lemma stk0_sp_bound : forall W ws w L RNG st LBa (m : amem) sp, ties W ws -> In w ws -> w_kind w = K_STACK -> w_lo w < ZC_BASE ->
  AHEAP AI L RNG st LBa m -> sp - w_lo w <= 8384352 -> sp <= al_top L.
Proof.
  intros W ws w L RNG st LBa m sp (_ & _ & _ & _ & _ & _ & _ & T8 & _) Hw K P AH D. rewrite (T8 w Hw K P) in D.
  destruct (AI_layout AI _ _ _ _ _ AH) as (S1 & _ & S2 & S3 & _). lia.
Qed.

End AsanWorld.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Actr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Definition is_heap (b : ablock) : Prop := exists p, ab_kind b = ABHeap p.
Definition is_fake (b : ablock) : Prop := exists c, ab_kind b = ABFake c.
Lemma kind_cases : forall b, is_heap b \/ is_fake b.
Proof. intros [[p|c] A n]; [left; exists p| right; exists c]; reflexivity. Qed.
Lemma heap_not_fake : forall b, is_heap b -> is_fake b -> False.
Proof. intros [[p|c] A n] [q E] [d E']; cbn in *; congruence. Qed.
Lemma ablock_eq_dec : forall x y : ablock, {x = y} + {x <> y}.
Proof. decide equality; try apply Z.eq_dec. decide equality; [apply N.eq_dec| apply Z.eq_dec]. Defined.

Definition lb_del (b : ablock) (LBa : list ablock) : list ablock := List.filter (fun x => if ablock_eq_dec x b then false else true) LBa.
Lemma lb_del_In : forall b LBa x, In x (lb_del b LBa) <-> In x LBa /\ x <> b.
Proof. intros b LBa x. unfold lb_del. rewrite filter_In. destruct (ablock_eq_dec x b); split; intros [H1 H2]; try discriminate; try contradiction; auto. Qed.

Section FakeIface.
Context {rc : runConstT}.
Variable AI : AMallocIface2.

Definition flag_law (L : alayout) (b : ablock) (flg : Z) : Prop :=
  forall RNG st LBa m, AHEAP AI L RNG st LBa m -> In b LBa ->
    AHEAP AI L RNG st (lb_del b LBa) (write_to_mem m (wa flg) [Z_to_bv 8 0])
    /\ wr_at bsegs m flg 1 /\ ((AIMG_HI <= flg /\ flg < KLS) \/ (0x10007fff8000 <= flg /\ flg < ATOP))
    /\ (forall b', In b' LBa -> ~ (ab_addr b' <= flg < ab_addr b' + ab_size b'))

    /\ al_fake L <= flg /\ flg < al_fake L + 11571200.
Record fake_iface : Type := mkFakeIface {
  FLG : alayout -> ablock -> Z;
  FRNG : alayout -> footprint -> Prop;
  fk_facts :> forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b ->
     ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0 /\ ab_size b mod 8 = 0 /\ 64 <= ab_size b
     /\ wr_at bsegs m (ab_addr b) (ab_size b) /\ wr_at bsegs m (shad (ab_addr b)) (shlen (ab_size b));
  fk_class : forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b ->
     exists c, ab_kind b = ABFake c /\ 0 <= c /\ ab_size b = 64 * 2 ^ c;
  fk_law : forall L b, is_fake b -> flag_law L b (FLG L b);
  fk_rng : forall L RNG st LBa m b, AHEAP AI L RNG st LBa m -> In b LBa -> is_fake b -> FRNG L RNG ->
     rng RNG (ab_addr b) (ab_size b) /\ rng RNG (shad (ab_addr b)) (shlen (ab_size b)) /\ rng RNG (FLG L b) 1;
  fk_area : forall L RNG, FRNG L RNG -> rng RNG (al_fake L) 11571200 }.
End FakeIface.

Abbreviation AI_fake_law := fake_iface.

Section ImgxOk.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Definition imgx_ok (IMGX : list iv) : Prop := forall v, In v IMGX -> 0 <= snd v /\
  (   (exists r, In r (aci AI) /\ fst r <= fst v /\ fst v + snd v <= snd r)
   \/ (exists r, In r (aci AI) /\ fst r <= 8 * (fst v - ASHOFF) /\ 8 * (fst v - ASHOFF) + 8 * snd v <= snd r)
   \/ (ATOP <= 8 * (fst v - ASHOFF) /\ 8 * (fst v - ASHOFF) + 8 * snd v <= 2 ^ 47)).
End ImgxOk.

Lemma is_primary_le : forall n, 0 <= n <= 64512 -> is_primary n = true.
Proof.
  intros n Hn. unfold is_primary, needed0, rounded_size, rz_size, rz_log, K_MAX_SIZE, rup.
  apply Z.leb_le.
  repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end;
    rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.
Qed.

Section AsanWorld.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.

Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).

Definition PUBSH : list (Z * Z) := [(0x800b9c60, 0x800b9db8); (0x800b9dd0, 0x800bde20); (0x800bde28, 0x800bdfb8); (0x800bdfc0, 0x800be03d); (0x800be03e, 0x800be0e0)].

Definition STGSH : list (Z * Z) := [(0x800b7c58, 0x800b9c60)].
Definition SHLIT : list (Z * Z) := ActrA.IMGSH ++ STGSH ++ PUBSH.
Lemma IMGSH_SHLIT : forall v, In v ActrA.IMGSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. left. exact H. Qed.
Lemma STGSH_SHLIT : forall v, In v STGSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma PUBSH_SHLIT : forall v, In v PUBSH -> In v SHLIT.
Proof. intros v H. unfold SHLIT. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
Lemma SHLIT_cases : forall v, In v SHLIT ->
  v = (0x7fffa000, 0x7fffc6a0) \/ (In v (STGSH ++ PUBSH) /\ 0x800b7c58 <= fst v /\ fst v <= snd v /\ snd v <= 0x800be0e0).
Proof.
  intros v H. unfold SHLIT in H. apply in_app_or in H. destruct H as [H|H].
  - left. unfold ActrA.IMGSH in H. cbn [In] in H. destruct H as [<-|[]]. reflexivity.
  - right. split; [exact H|]. unfold STGSH, PUBSH in H. cbn [In app] in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.
Definition sh_cov (z : Z) : Prop :=
  (exists a', ATOP <= a' < 2^47 /\ z = shad a') \/ (exists v, In v SHLIT /\ fst v <= z < snd v).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.

Variable UNIV : list (list Z).

Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (wa a) = m (wa a)) -> wmono bsegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> wmono bsegs m m'.

Definition usz (b : ablock) : Z := match ab_kind b with ABFake _ => ab_size b - 8 | ABHeap _ => ab_size b end.
Definition user_iv (b : ablock) : iv := (ab_addr b, usz b).
Lemma usz_le : forall b, ab_size b - 8 <= usz b <= ab_size b.
Proof. intros [[p|c] A n]; unfold usz; cbn; lia. Qed.
Lemma usz_heap : forall b, is_heap b -> usz b = ab_size b.
Proof. intros [[p|c] A n] [q E]; unfold usz; cbn in *; [reflexivity| discriminate]. Qed.
Lemma usz_fake : forall b, is_fake b -> usz b = ab_size b - 8.
Proof. intros [[p|c] A n] [q E]; unfold usz; cbn in *; [discriminate| reflexivity]. Qed.
Ltac usz_facts :=
  repeat match goal with
         | |- context [usz ?b] => lazymatch goal with H' : ab_size b - 8 <= usz b <= ab_size b |- _ => fail | _ => pose proof (usz_le b) end
         | H : context [usz ?b] |- _ => lazymatch goal with H' : ab_size b - 8 <= usz b <= ab_size b |- _ => fail | _ => pose proof (usz_le b) end
         end.
Ltac ulia := usz_facts; lia.
Definition twin_iv (b : ablock) : iv := (shad (ab_addr b), shlen (ab_size b + 7)).
Definition fsh_iv (b : ablock) : iv := (shad (ab_addr b), shlen (ab_size b)).
Definition ZTOTAL : Z := 1024.
Definition FRAME_MAX : Z := 256.

Variable AI_fake : fake_iface AI.

Record wit := mkWit { w_L : alayout; w_RNG : footprint; w_st : astate; w_LBa : list ablock; w_T : list ablock; w_FA : list ablock;
                      w_ms : amem; w_zc : Z }.
Definition vis (W : wit) (b : ablock) : Prop := In b (w_LBa W) /\ ~ In b (w_FA W).
Definition visf (W : wit) (b : ablock) : Prop := vis W b /\ is_fake b.

Definition aw_holds_w (W : wit) (aw : word) (LB : blocks) (m : amem) (mo : Model) : Prop :=
     AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_ms W)
  /\ (forall b, In b (w_T W) -> In b (w_LBa W) /\ is_heap b) /\ List.NoDup (w_T W)
  /\ (forall b, In b (w_FA W) -> In b (w_LBa W) /\ is_fake b) /\ List.NoDup (w_FA W)
  /\ (forall v, In v LB <->    (exists b, vis W b /\ v = user_iv b) \/ (exists b, In b (w_T W) /\ v = twin_iv b)
                            \/ (exists b, visf W b /\ v = fsh_iv b))
  /\ (forall a, 0 <= a < two64 -> ~ in_ivs (map twin_iv (w_T W)) a -> w_ms W (wa a) = m (wa a))
  /\ (forall a, in_ivs (map twin_iv (w_T W)) a -> m (wa a) <> None)
  /\ 0 <= w_zc W /\ Z.of_nat (length (w_FA W)) + w_zc W <= ZTOTAL
  /\ ACCT aw (w_L W) (w_RNG W) (w_st W) (w_LBa W) mo
  /\ incl UNIV (al_U (w_L W))
  /\ (forall b, In b (w_LBa W) -> is_fake b -> ab_size b <= FRAME_MAX)
  /\ (forall b, visf W b ->
        exists flg, bytes_at bsegs (w_ms W) (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg)
  /\ (forall b, vis W b -> is_heap b -> ~ In b (w_T W) -> forall g, 0 <= g -> 8 * g < ab_size b ->
        m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
Definition aw_holds_asan (aw : word) (LB : blocks) (m : amem) (mo : Model) : Prop := exists W, aw_holds_w W aw LB m mo.

Definition aw_ceiling_asan (_ : Model) : Z := ATOP + 4096.
Definition aw_dep_asan (LB : blocks) (_ : amem) (_ : Model) (a : Z) : Prop :=
  0 <= a < ATOP + 4096 /\ ~ in_user LB a /\ ~ in_ivs IMGX a.

Fixpoint in_ivs_b (l : list iv) (a : Z) : bool :=
  match l with
  | [] => false
  | v :: l' => ((fst v <=? a) && (a <? fst v + snd v)) || in_ivs_b l' a
  end.
Lemma in_ivs_b_spec : forall l a, in_ivs_b l a = true <-> in_ivs l a.
Proof.
  induction l as [|v l IH]; intros a; cbn [in_ivs_b].
  - split; [discriminate| intros H; inversion H].
  - rewrite in_ivs_cons, <- IH. unfold in_iv. rewrite orb_true_iff, andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Definition to_ivl (v : iv) : ivl := (fst v, fst v + snd v).
Lemma outside_map : forall l x, outside (map to_ivl l) x <-> ~ in_ivs l x.
Proof.
  induction l as [|v l IH]; intros x; cbn [map outside].
  - split; [intros _ H; inversion H| intros _; exact I].
  - unfold to_ivl at 1. cbn [fst snd]. rewrite IH, in_ivs_cons. unfold in_iv. tauto.
Qed.
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto| rewrite IH; tauto]. Qed.

Lemma wview_ext1 : forall (m1 m2 : amem) x, m1 x = m2 x -> wview bsegs m1 x = wview bsegs m2 x.
Proof. intros m1 m2 x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma heap_block_facts : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b ->
  1 <= ab_size b <= AREQMAX /\ ablock_range (ab_addr b) (ab_size b) /\ wr_at bsegs ms (ab_addr b) (ab_size b).
Proof.
  intros L RNG st LBa ms [k A n] AH Hb [p Hp]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (N & BR & _ & _ & _ & WR & _). auto.
Qed.

Lemma blk_facts : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa ->
  0 < ab_size b /\ ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0
  /\ wr_at bsegs ms (ab_addr b) (ab_size b).
Proof.
  intros L RNG st LBa ms b AH Hb. destruct (kind_cases b) as [HH|HF].
  - destruct (heap_block_facts L RNG st LBa ms b AH Hb HH) as (N & (BK & N0 & HI & AL) & WR).
    split; [ulia|]. split; [exact BK|]. split; [exact HI|]. split; [clear -AL; Z.div_mod_to_equations; ulia| exact WR].
  - destruct (AI_fake L RNG st LBa ms b AH Hb HF) as (BK & HI & A8 & N8 & NP & WR & _). split; [ulia|]. split; [exact BK|]. split; [exact HI|]. split; [exact A8| exact WR].
Qed.

Lemma twin_band : forall A n, ablock_range A n -> 1 <= n <= AREQMAX ->
  0x7fff8000 <= shad A /\ shad A + shlen (n + 7) <= 0x10007fff8000 /\ 1 <= shlen (n + 7) /\ shad A + shlen (n + 7) = shad (A + n + 7).
Proof.
  intros A n (BK & N0 & HI & AL) N. pose proof atop_range as AR. unfold ablk, AIMG_HI, KLS, AREQMAX in *.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8.
  repeat split; Z.div_mod_to_equations; ulia.
Qed.
Lemma fsh_band : forall A n, ablk A (A + n) -> A + n <= ATOP -> A mod 8 = 0 -> n mod 8 = 0 -> 0 < n ->
  0x7fff8000 <= shad A /\ shad A + shlen n <= 0x10007fff8000 /\ 1 <= shlen n /\ 8 * (shad A - ASHOFF) = A /\ 8 * shlen n = n.
Proof.
  intros A n BK HI A8 N8 NP. pose proof atop_range as AR. unfold ablk, AIMG_HI, KLS in *.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8.
  repeat split; Z.div_mod_to_equations; ulia.
Qed.
Lemma user_app_band : forall A n, ablk A (A + n) -> 0 < n -> (A + n <= 0x7fff8000 \/ 0x10007fff8000 <= A) /\ 6492160 <= A.
Proof. intros A n BK NP. unfold ablk, AIMG_HI, KLS in BK. ulia. Qed.

Lemma LB_cases : forall W aw LB m mo v, aw_holds_w W aw LB m mo -> In v LB ->
     (exists b, vis W b /\ v = user_iv b) \/ (exists b, In b (w_T W) /\ v = twin_iv b)
  \/ (exists b, visf W b /\ v = fsh_iv b).
Proof. intros W aw LB m mo v (_ & _ & _ & _ & _ & HLB & _) Hv. apply HLB. exact Hv. Qed.

Lemma usz_pos : forall L RNG st LBa ms b, AHEAP AI L RNG st LBa ms -> In b LBa -> 0 < usz b.
Proof.
  intros L RNG st LBa ms b AH Hb. destruct (kind_cases b) as [HH|HF].
  - rewrite (usz_heap b HH). destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & _). exact NP.
  - rewrite (usz_fake b HF). destruct (AI_fake L RNG st LBa ms b AH Hb HF) as (_ & _ & _ & _ & N64 & _). lia.
Qed.
Lemma LB_user_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> vis W b ->
  0 < usz b /\ (ab_addr b + ab_size b <= 0x7fff8000 \/ 0x10007fff8000 <= ab_addr b) /\ 6492160 <= ab_addr b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros W aw LB m mo b (AH & _) [Hb _]. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _).
  destruct (user_app_band _ _ BK NP) as [B1 B2]. split; [exact (usz_pos _ _ _ _ _ b AH Hb)|]. auto.
Qed.
Lemma LB_twin_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> In b (w_T W) ->
  0x7fff8000 <= shad (ab_addr b) /\ shad (ab_addr b) + shlen (ab_size b + 7) <= 0x10007fff8000 /\ 1 <= shlen (ab_size b + 7).
Proof.
  intros W aw LB m mo b (AH & HT & _) Hb. destruct (HT b Hb) as [HbL HbH].
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (N & BR & _). destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _). auto.
Qed.
Lemma LB_fsh_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> visf W b ->
  0x7fff8000 <= shad (ab_addr b) /\ shad (ab_addr b) + shlen (ab_size b) <= 0x10007fff8000 /\ 1 <= shlen (ab_size b)
  /\ 8 * (shad (ab_addr b) - ASHOFF) = ab_addr b /\ 8 * shlen (ab_size b) = ab_size b.
Proof.
  intros W aw LB m mo b (AH & _) [[Hb _] HF]. destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
  exact (fsh_band _ _ BK HI A8 N8 ltac:(ulia)).
Qed.

Definition fakeb (b : ablock) : bool := match ab_kind b with ABFake _ => true | ABHeap _ => false end.
Lemma fakeb_spec : forall b, fakeb b = true <-> is_fake b.
Proof. intros [[p|c] A n]; unfold fakeb, is_fake; cbn; split; intros H; try discriminate; try (exists c; reflexivity); try reflexivity. destruct H as [d H]. discriminate. Qed.
Definition set_ms (W : wit) (ms : amem) : wit := mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (w_FA W) ms (w_zc W).

Lemma bytes_at_agreeN : forall (m m' : amem) a bs,
  bytes_at bsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at bsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [ulia|]. split; [ulia|]. intros i Hi.
  unfold mrd in *. rewrite E by ulia. apply H. exact Hi.
Qed.

Lemma IMGX_class : forall a, in_ivs IMGX a -> a < AIMG_HI \/ (0x7fff8000 <= a < 0x800be200) \/ (shad ATOP <= a < shad (2 ^ 47)).
Proof.
  intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). destruct (IMGX_aci w Hw) as (N0 & [(r & Hr & R1 & R2)|[(r & Hr & R1 & R2)|(S1 & S2)]]);
    unfold in_iv in Hin.
  - left. pose proof (AI_aci_img AI r Hr). lia.
  - right. left. pose proof (AI_aci_img AI r Hr) as HI. pose proof (AI_aci_lo AI r Hr) as LO. unfold AIMG_HI, ASHOFF in *. lia.
  - right. right. pose proof atop_range as AR. unfold shad, ASHOFF in *. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_tight : forall A n, ablk A (A + n) -> A + n <= ATOP -> 0 < n -> 0x800be200 <= shad A /\ shad A + shlen (n + 7) <= shad ATOP.
Proof.
  intros A n BK HI NP. pose proof atop_range as AR. pose proof ATOP_al16 as A16. unfold ablk, AIMG_HI, KLS in BK.
  unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia.
Qed.

Lemma sh_cov_band : forall a, sh_cov a -> (0x7fffa000 <= a < 0x800be0e0) \/ (shad ATOP <= a < 0x10007fff8000).
Proof.
  intros a [(a' & R & ->)|(v & Hv & R)].
  - right. pose proof atop_range as AR. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
  - left. destruct (SHLIT_cases v Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in R|]; lia.
Qed.
Lemma blk_not_IMGX : forall L RNG st LBa ms b a, AHEAP AI L RNG st LBa ms -> In b LBa ->
  (ab_addr b <= a < ab_addr b + ab_size b \/ shad (ab_addr b) <= a < shad (ab_addr b) + shlen (ab_size b + 7)) -> ~ in_ivs IMGX a.
Proof.
  intros L RNG st LBa ms b a AH Hb Ha II. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _).
  destruct (shadow_tight _ _ BK HI NP) as [T1 T2]. destruct (user_app_band _ _ BK NP) as [B1 B2]. pose proof atop_range as AR.
  assert (SHT : shad (2 ^ 47) = 0x10007fff8000) by reflexivity.
  assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (IMGX_class a II) as [C|[C|C]]; unfold AIMG_HI in *; destruct Ha as [Ha|Ha]; lia.
Qed.

Lemma blk_byte_private : forall W aw LB m mo b x, aw_holds_w W aw LB m mo -> In b (w_LBa W) -> ab_addr b <= x < ab_addr b + ab_size b ->
  forall v, In v LB -> in_iv v x -> v = user_iv b /\ vis W b.
Proof.
  intros W aw LB m mo b x HW Hb Hx v Hv Hin. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & _).
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _). destruct (user_app_band _ _ BK NP) as [B1 B2].
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b' & Vb' & ->)|[(b' & Hb' & ->)|(b' & Vb' & ->)]]; unfold in_iv in Hin; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
  - destruct (ablock_eq_dec b' b) as [->|NE]; [split; [reflexivity| exact Vb']| exfalso].
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b' b AH (proj1 Vb') Hb NE) as D. ulia.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). ulia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & _). ulia.
Qed.

Lemma flagw_facts : forall W aw LB m mo b x, aw_holds_w W aw LB m mo -> visf W b -> ab_addr b + ab_size b - 8 <= x < ab_addr b + ab_size b ->
  0 <= x < two64 /\ ~ in_ivs (map twin_iv (w_T W)) x /\ ~ in_user LB x /\ ~ in_ivs IMGX x /\ x < ATOP + 4096
  /\ ab_addr b <= x < ab_addr b + ab_size b.
Proof.
  intros W aw LB m mo b x HW [[HbL NFA] HF] Hx. pose proof HW as (AH & _). pose proof atop_range as AR.
  destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
  destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
  split; [unfold two64; lia|]. split.
  { intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
    destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. lia. }
  split.
  { intros IU. unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin).
    destruct (blk_byte_private W aw LB m mo b x HW HbL ltac:(lia) v Hv Hin) as [-> _].
    unfold in_iv, user_iv in Hin. cbn [fst snd] in Hin. rewrite (usz_fake b HF) in Hin. lia. }
  assert (INB : ab_addr b <= x < ab_addr b + ab_size b) by lia.
  split; [intros II; exact (blk_not_IMGX _ _ _ _ _ b x AH HbL (or_introl INB) II)|]. split; lia.
Qed.
Lemma vfl_agree : forall W aw LB m mo (ms' : amem), aw_holds_w W aw LB m mo ->
  (forall b x, visf W b -> ab_addr b + ab_size b - 8 <= x < ab_addr b + ab_size b -> ms' (wa x) = w_ms W (wa x)) ->
  forall b, visf W b -> exists flg, bytes_at bsegs ms' (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg.
Proof.
  intros W aw LB m mo ms' HW AG b Vb. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VFL & _).
  destruct (VFL b Vb) as (flg & BA & FL). exists flg. split; [| exact FL].
  eapply bytes_at_agreeN; [exact BA|]. intros x Hx. rewrite length_le8 in Hx. apply (AG b x Vb). lia.
Qed.

Lemma gran_disj : forall A n B k a, 0 <= A -> 0 <= B -> 0 <= n -> 0 <= k -> (A + n <= B \/ B + k <= A) -> A mod 8 = 0 -> B mod 8 = 0 ->
  shad A <= a < shad A + shlen (n + 7) -> shad B <= a < shad B + shlen (k + 7) -> False.
Proof.
  intros A n B k a A0 B0 N0 K0 D A8 B8 H1 H2. unfold shad, shlen, ASHOFF in *. rewrite !Z.shiftr_div_pow2 in * by ulia. change (2^3) with 8 in *.
  destruct D; Z.div_mod_to_equations; ulia.
Qed.
Lemma shlen_le7 : forall n, 0 <= n -> shlen n <= shlen (n + 7).
Proof. intros n N. unfold shlen. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. Z.div_mod_to_equations. ulia. Qed.

Lemma LB_shadow_hull : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> (In b (w_T W) \/ visf W b) ->
  In b (w_LBa W) /\ 0 <= ab_addr b /\ 0 < ab_size b /\ ab_addr b mod 8 = 0.
Proof.
  intros W aw LB m mo b HW HB. pose proof HW as (AH & HT & _).
  assert (Hb : In b (w_LBa W)) by (destruct HB as [HbT|[[Hb _] _]]; [exact (proj1 (HT b HbT))| exact Hb]).
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & A8 & _). destruct (user_app_band _ _ BK NP) as [_ B2].
  split; [exact Hb|]. split; [ulia|]. split; [exact NP| exact A8].
Qed.

Lemma in_twin_clear : forall W aw LB m mo b a, aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) -> in_iv (twin_iv b) a ->
  0 <= a < ATOP + 4096 /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof.
  intros W aw LB m mo b a HW Vb HH NT Ha. pose proof HW as (AH & HT & _). pose proof atop_range as AR. destruct Vb as [Hb NFA].
  destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & BR & _). pose proof BR as (BK & N0 & HI & AL).
  destruct (shadow_tight _ _ BK HI ltac:(ulia)) as [ST1 ST2]. destruct (twin_band _ _ BR N) as (TB1 & TB2 & TB3 & _). unfold in_iv, twin_iv in Ha. cbn [fst snd] in Ha.
  assert (SA : shad ATOP < ATOP + 4096) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by ulia; change (2^3) with 8; Z.div_mod_to_equations; ulia).
  split; [ulia|]. split.
  - intros U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Hva.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b' & Vb' & ->)|[(b' & Hb' & ->)|(b' & Vb' & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b' HW Vb') as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b' HW (or_introl Hb')) as (H1 & H2 & H3 & H4).
      assert (NE : b <> b') by (intros ->; exact (NT Hb')).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb H1 NE) as D.
      exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a ltac:(unfold ablk, AIMG_HI in BK; ulia) H2 ltac:(ulia) ltac:(ulia) D ltac:(clear -AL; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + destruct (LB_shadow_hull W aw LB m mo b' HW (or_intror Vb')) as (H1 & H2 & H3 & H4).
      assert (NE : b <> b') by (intros ->; exact (heap_not_fake _ HH (proj2 Vb'))).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb H1 NE) as D.
      pose proof (shlen_le7 (ab_size b') ltac:(ulia)) as LE.
      exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a ltac:(unfold ablk, AIMG_HI in BK; ulia) H2 ltac:(ulia) ltac:(ulia) D ltac:(clear -AL; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
  - intros X. destruct (IMGX_class a X) as [X1|[X1|X1]]; unfold AIMG_HI in *; ulia.
Qed.

Lemma aw_frame_w_v : forall W A LB m m' mo, aw_holds_w W A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono bsegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  exists ms2, aw_holds_w (set_ms W ms2) A LB m' mo.
Proof.
  intros W A LB m m' mo HW AG WM DM. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as AR.
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (st := w_st W) in *. set (LBa := w_LBa W) in *. set (T := w_T W) in *. set (ms := w_ms W) in *.
  set (tw := map twin_iv T) in *. set (FK := List.filter fakeb LBa).

  set (ms2 := fun x : word => if in_ivs_b tw (bv_unsigned x) then ms x else m' x).
  set (ms1 := fun x : word => if bv_unsigned x <? 2^47 then ms2 x else ms x).
  assert (R64 : forall x : word, 0 <= bv_unsigned x < two64).
  { intros x. pose proof (bv_unsigned_in_range 64 x) as R. exact R. }
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).

  assert (KEEP : forall x : word, ~ in_ivs tw (bv_unsigned x) -> bv_unsigned x < ATOP + 4096 -> ~ in_user LB (bv_unsigned x) -> ~ in_ivs IMGX (bv_unsigned x) ->
            ms2 x = ms x).
  { intros x NTW LT NU NI. unfold ms2. replace (in_ivs_b tw (bv_unsigned x)) with false
      by (symmetry; destruct (in_ivs_b tw (bv_unsigned x)) eqn:E; [exfalso; apply NTW; apply in_ivs_b_spec; exact E| reflexivity]).
    pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1. rewrite E1. symmetry. rewrite <- (WAX x). apply AG; [apply R64|].
    split; [pose proof (R64 x); ulia|]. split; assumption. }

  assert (DIFF : forall x : word, ms2 x <> ms x ->
            ATOP + 4096 <= bv_unsigned x \/ in_ivs (map user_iv LBa) (bv_unsigned x) \/ in_ivs (map fsh_iv FK) (bv_unsigned x) \/ in_ivs IMGX (bv_unsigned x)).
  { intros x NE.
    destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW; [exfalso; apply NE; unfold ms2; rewrite TW; reflexivity|].
    assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
    destruct (Z_lt_le_dec (bv_unsigned x) (ATOP + 4096)) as [LT|GE]; [| left; exact GE]. right.
    destruct (in_ivs_b (map user_iv LBa) (bv_unsigned x)) eqn:UB; [left; apply in_ivs_b_spec; exact UB|].
    destruct (in_ivs_b (map fsh_iv FK) (bv_unsigned x)) eqn:FB; [right; left; apply in_ivs_b_spec; exact FB|].
    destruct (in_ivs_b IMGX (bv_unsigned x)) eqn:IB; [right; right; apply in_ivs_b_spec; exact IB|]. exfalso. apply NE.
    apply KEEP; [exact NTW| exact LT| | intros II; apply in_ivs_b_spec in II; congruence].
    intros IU. unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin).
    destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    - assert (X : in_ivs (map user_iv LBa) (bv_unsigned x)) by (apply in_ivs_In; exists (user_iv b); split; [apply in_map; exact (proj1 Vb)| exact Hin]).
      apply in_ivs_b_spec in X. congruence.
    - apply NTW. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact Hb| exact Hin].
    - assert (X : in_ivs (map fsh_iv FK) (bv_unsigned x)).
      { apply in_ivs_In. exists (fsh_iv b). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact (proj1 (proj1 Vb))| apply fakeb_spec; exact (proj2 Vb)]. }
      apply in_ivs_b_spec in X. congruence. }

  assert (AH1 : AHEAP AI L RNG st LBa ms1).
  { eapply (AI_frame AI L RNG st LBa ms ms1 (map to_ivl (map user_iv LBa) ++ map to_ivl (map fsh_iv FK) ++ map to_ivl IMGX ++ [(ATOP + 4096, 2^47)])); [exact AH | | |].
    - intros x OUT. unfold ms1. destruct (bv_unsigned x <? 2^47) eqn:LT; [|reflexivity]. apply Z.ltb_lt in LT.
      destruct (decide (ms2 x = ms x)) as [E|NE]; [exact E| exfalso].
      apply outside_app in OUT as [O1 O234]. apply outside_app in O234 as [O2 O34]. apply outside_app in O34 as [O3 O4]. cbn [outside] in O4.
      rewrite outside_map in O1, O2, O3. destruct (DIFF x NE) as [G|[U|[F|I']]]; [ulia| exact (O1 U)| exact (O2 F)| exact (O3 I')].
    - intros x Hx. destruct (bv_unsigned x <? 2^47) eqn:LT;
        [| rewrite (wview_ext1 ms1 ms x) by (unfold ms1; rewrite LT; reflexivity); exact Hx].
      destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW;
        [rewrite (wview_ext1 ms1 ms x) by (unfold ms1, ms2; rewrite LT, TW; reflexivity); exact Hx|].
      assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
      pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1.
      rewrite (wview_ext1 ms1 m' x) by (unfold ms1, ms2; rewrite LT, TW; reflexivity).
      apply (WM x). rewrite <- (wview_ext1 ms m x E1). exact Hx.
    - apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv). apply in_map_iff in Hv as (b & <- & Hb).
        unfold to_ivl, user_iv. cbn [fst snd]. right. left. exists b. split; [exact Hb|]. ulia.
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv). apply in_map_iff in Hv as (b & <- & Hb).
        apply filter_In in Hb as [Hb FB]. apply fakeb_spec in FB.
        destruct (AI_fake L RNG st LBa ms b AH Hb FB) as (BK & HI & A8 & N8 & NP & _).
        destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (_ & _ & _ & E1 & E2).
        unfold to_ivl, fsh_iv. cbn [fst snd]. right. right.
        replace (shad (ab_addr b) + shlen (ab_size b) - shad (ab_addr b)) with (shlen (ab_size b)) by ulia. rewrite E1, E2.
        right. right. destruct b as [[p|c] F k]; [destruct FB as [d FB]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size]. split; [exact Hb| ulia].
      + apply Forall_forall. intros iv0 Hin. apply in_map_iff in Hin as (v & <- & Hv).
        destruct (IMGX_aci v Hv) as (R3 & [(r & Hr & R1 & R2)|[(r & Hr & R1 & R2)|(S1 & S2)]]); unfold to_ivl; cbn [fst snd].
        * left. right. left. exists r. split; [exact Hr|]. ulia.
        * right. right. right. left. exists r. split; [exact Hr|]. ulia.
        * right. right. left. ulia.
      + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. left. ulia. }

  assert (AH2 : AHEAP AI L RNG st LBa ms2).
  { eapply (AI_frame_top L RNG st LBa ms1 ms2); [exact AH1 | |].
    - intros a Ha. unfold ms1. unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus; ulia). replace (a <? 2^47) with true by (symmetry; apply Z.ltb_lt; ulia). reflexivity.
    - intros x Hx. destruct (bv_unsigned x <? 2^47) eqn:LT;
        [rewrite <- (wview_ext1 ms1 ms2 x) by (unfold ms1; rewrite LT; reflexivity); exact Hx|].
      rewrite (wview_ext1 ms1 ms x) in Hx by (unfold ms1; rewrite LT; reflexivity).
      destruct (in_ivs_b tw (bv_unsigned x)) eqn:TW;
        [rewrite (wview_ext1 ms2 ms x) by (unfold ms2; rewrite TW; reflexivity); exact Hx|].
      assert (NTW : ~ in_ivs tw (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
      pose proof (EQ (bv_unsigned x) (R64 x) NTW) as E1. rewrite WAX in E1.
      rewrite (wview_ext1 ms2 m' x) by (unfold ms2; rewrite TW; reflexivity).
      apply (WM x). rewrite <- (wview_ext1 ms m x E1). exact Hx. }
  exists ms2. unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH2|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split.
  { intros a Ha NTW. unfold ms2. unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus, two64 in *; ulia).
    replace (in_ivs_b tw a) with false; [reflexivity|]. symmetry. destruct (in_ivs_b tw a) eqn:E; [| reflexivity]. exfalso. apply NTW. apply in_ivs_b_spec. exact E. }
  split.
  { intros a Ha. pose proof (MAP a Ha) as M0.
    assert (R : 0 <= a < two64 \/ ~ (0 <= a < two64)) by ulia. destruct R as [R|R].
    + unfold wa in *. apply (DM a); [| exact M0]. split; [| exact (proj2 R)].
      apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
      destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI. ulia.
    +   exfalso.
      apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
      destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold two64 in *. ulia. }
  split; [exact ZC0| split; [exact ZCB| split; [exact AC| split; [exact HU| split; [exact CLS| split]]]]].
  -
    apply (vfl_agree W A LB m mo ms2 HW). intros b x Vb Hx.
    destruct (flagw_facts W A LB m mo b x HW Vb Hx) as (XR & NTW & NU & NI & LT & _).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply Z_to_bv_small; unfold bv_modulus, two64 in *; lia).
    apply KEEP; rewrite UX; assumption.
  -
    intros b Vb HH NT g G0 G1. rewrite <- (INC b Vb HH NT g G0 G1). symmetry.
    destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (Nb & BRb & _).
    destruct (in_twin_clear W A LB m mo b (shad (ab_addr b) + g) HW Vb HH NT) as (R1 & NU & NI).
    { unfold in_iv, twin_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. ulia. }
    pose proof atop_range as ATR. apply AG; [unfold two64; ulia|]. split; [exact R1|]. split; [exact NU| exact NI].
Qed.

Lemma aw_frame_w : forall W A LB m m' mo, aw_holds_w W A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  exists ms2, aw_holds_w (set_ms W ms2) A LB m' mo.
Proof.
  intros W A LB m m' mo HW AG DM. apply (aw_frame_w_v W A LB m m' mo HW AG (wmono_of m m' DM)).
  intros a Ha. apply DM. unfold AIMG_HI in Ha. lia.
Qed.

Lemma aw_frame_asan : forall A LB m m' mo, aw_holds_asan A LB m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holds_asan A LB m' mo /\ (forall a, aw_dep_asan LB m' mo a <-> aw_dep_asan LB m mo a).
Proof.
  intros A LB m m' mo [W HW] AG DM. split; [| intros a; reflexivity].
  destruct (aw_frame_w W A LB m m' mo HW AG DM) as [ms2 H2]. exists (set_ms W ms2). exact H2.
Qed.

Lemma aw_dep_ok_asan : forall A LB m mo a, aw_holds_asan A LB m mo -> aw_dep_asan LB m mo a ->
  0 <= a < aw_ceiling_asan mo /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof. intros A LB m mo a _ H. exact H. Qed.

Lemma aw_blocks_ok_asan : forall A LB m mo b, aw_holds_asan A LB m mo -> In b LB ->
  0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= aw_ceiling_asan mo /\ aw_ceiling_asan mo < two64 /\
  (forall a, in_iv b a -> ~ in_ivs IMGX a).
Proof.
  intros A LB m mo v [W HW] Hv. pose proof atop_range as AR. unfold aw_ceiling_asan, two64.
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv].
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 Vb)). left. unfold in_iv, user_iv in Ha. cbn [fst snd] in Ha. ulia.
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & T3). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & HT & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 (HT b Hb))). right. exact Ha.
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & T3 & _). repeat (split; [ulia|]).
    intros a Ha. pose proof HW as (AH & _). apply (blk_not_IMGX _ _ _ _ _ b a AH (proj1 (proj1 Vb))). right.
    assert (LE7 : shlen (ab_size b) <= shlen (ab_size b + 7)).
    { destruct (blk_facts _ _ _ _ _ b AH (proj1 (proj1 Vb))) as (NP & _). unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    unfold in_iv, fsh_iv in Ha. cbn [fst snd] in Ha. lia.
Qed.

Lemma wr_at_mapped : forall (ms : amem) A n a, wr_at bsegs ms A n -> A <= a < A + n -> 6492160 <= a -> a < two64 -> find_segment bsegs a 1 = None ->
  ms (Z_to_bv 64 a) <> None.
Proof.
  intros ms A n a (_ & _ & WR) Ha LO HI SEG. pose proof (WR (a - A) ltac:(ulia)) as W. replace (A + (a - A)) with a in W by ulia.
  unfold wview, wa in W. destruct (ms (Z_to_bv 64 a)); [discriminate|].
  rewrite Z_to_bv_small in W by (unfold bv_modulus, two64 in *; ulia). rewrite SEG in W. congruence.
Qed.

Lemma aw_user_ok_asan : forall A LB m mo b a, aw_holds_asan A LB m mo -> In b LB -> in_iv b a ->
  m (Z_to_bv 64 a) <> None /\ find_segment bsegs a 1 = None.
Proof.
  intros A LB m mo v a [W HW] Hv Ha. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & _).
  pose proof atop_range as AR.
  assert (NTWB : 6492160 <= a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> ~ in_ivs (map twin_iv (w_T W)) a).
  { intros _ BA X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
    destruct (LB_twin_facts W A LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. ulia. }
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; unfold in_iv in Ha; cbn [fst snd user_iv twin_iv fsh_iv] in Ha.
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI).
    destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (_ & _ & _ & _ & WR).
    assert (SEG : find_segment bsegs a 1 = None) by (apply ref_find_segment_none; ulia).
    split; [| exact SEG].
    assert (R : 0 <= a < two64) by (unfold two64; ulia).
    change (Z_to_bv 64 a) with (wa a). rewrite <- (EQ a R (NTWB ltac:(ulia) ltac:(ulia))). unfold wa.
    apply (wr_at_mapped (w_ms W) (ab_addr b) (ab_size b) a WR ltac:(ulia) ltac:(ulia) ltac:(unfold two64; ulia) SEG).
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _).
    split; [| apply ref_find_segment_none; ulia].
    apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact Hb| exact Ha].
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & T3 & _).
    destruct Vb as [[HbL NFA] HF]. destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (_ & _ & _ & _ & _ & _ & WRS).
    assert (SEG : find_segment bsegs a 1 = None) by (apply ref_find_segment_none; ulia).
    split; [| exact SEG].
    assert (R : 0 <= a < two64) by (unfold two64; ulia).

    assert (NTW : ~ in_ivs (map twin_iv (w_T W)) a).
    { intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
      destruct (HT b' Hb') as [Hb'L Hb'H].
      assert (NE : b' <> b) by (intros ->; exact (heap_not_fake b Hb'H HF)).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b' b AH Hb'L HbL NE) as D.
      destruct (heap_block_facts _ _ _ _ _ b' AH Hb'L Hb'H) as (N' & (BK' & N0' & HI' & AL') & _).
      destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      unfold shad, shlen, ASHOFF, ablk, AIMG_HI, KLS, AREQMAX in *. rewrite !Z.shiftr_div_pow2 in * by ulia. change (2^3) with 8 in *.
      destruct D; Z.div_mod_to_equations; ulia. }
    change (Z_to_bv 64 a) with (wa a). rewrite <- (EQ a R NTW). unfold wa.
    apply (wr_at_mapped (w_ms W) _ _ a WRS Ha ltac:(ulia) ltac:(unfold two64; ulia) SEG).
Qed.

Lemma aw_blocks_disj_asan : forall A LB m mo b b' a, aw_holds_asan A LB m mo -> In b LB -> In b' LB -> fst b <> fst b' ->
  in_iv b a -> ~ in_iv b' a.
Proof.
  intros A LB m mo v v' a [W HW] Hv Hv' NE Ha Ha'. pose proof HW as (AH & HT & ND & HFA & NDF & _).

  assert (CL : forall w, In w LB -> in_iv w a ->
            (exists b, vis W b /\ w = user_iv b /\ ab_addr b <= a < ab_addr b + ab_size b /\ (a < 0x7fff8000 \/ 0x10007fff8000 <= a))
         \/ (exists b, In b (w_LBa W) /\ fst w = shad (ab_addr b) /\ shad (ab_addr b) <= a < shad (ab_addr b) + shlen (ab_size b + 7)
                       /\ 0x7fff8000 <= a < 0x10007fff8000 /\ 0 <= ab_addr b /\ 0 < ab_size b /\ ab_addr b mod 8 = 0)).
  { intros w Hw Hin. unfold in_iv in Hin.
    destruct (LB_cases W A LB m mo w HW Hw) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
    - left. exists b. destruct (LB_user_facts W A LB m mo b HW Vb) as (NP & B1 & B2 & HI). split; [exact Vb|]. split; [reflexivity|]. split; [ulia| ulia].
    - right. exists b. destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & T2 & _). destruct (LB_shadow_hull W A LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      split; [exact H1|]. split; [reflexivity|]. split; [exact Hin|]. split; [ulia|]. auto.
    - right. exists b. destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & T2 & _). destruct (LB_shadow_hull W A LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE. split; [exact H1|]. split; [reflexivity|]. split; [ulia|]. split; [ulia|]. auto. }
  destruct (CL v Hv Ha) as [(b & Vb & -> & R & BA)|(b & Hb & E & R & BA & B0 & BP & B8)];
  destruct (CL v' Hv' Ha') as [(b' & Vb' & -> & R' & BA')|(b' & Hb' & E' & R' & BA' & B0' & BP' & B8')]; try ulia.
  -
    assert (NB : b <> b') by (intros ->; apply NE; reflexivity).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH (proj1 Vb) (proj1 Vb') NB) as D. ulia.
  -
    assert (NB : b <> b') by (intros ->; apply NE; rewrite E, E'; reflexivity).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NB) as D.
    exact (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a B0 B0' ltac:(ulia) ltac:(ulia) D B8 B8' R R').
Qed.

Lemma aw_ceiling_small_asan : forall mo, aw_ceiling_asan mo <= OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.two62Z.
Proof. intros mo. pose proof atop_range as AR. unfold aw_ceiling_asan. change OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.two62Z with (2^62). ulia. Qed.

Lemma aw_blocks_lo_asan : forall A LB m mo b, aw_holds_asan A LB m mo -> In b LB -> 4096 <= fst b.
Proof.
  intros A LB m mo v [W HW] Hv.
  destruct (LB_cases W A LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst user_iv twin_iv fsh_iv].
  - destruct (LB_user_facts W A LB m mo b HW Vb) as (_ & _ & B2 & _). ulia.
  - destruct (LB_twin_facts W A LB m mo b HW Hb) as (T1 & _). ulia.
  - destruct (LB_fsh_facts W A LB m mo b HW Vb) as (T1 & _). ulia.
Qed.

Definition user_band (A : Z) : Prop := A < 0x7fff8000 \/ 0x10007fff8000 <= A.

Definition set_T (W : wit) (T : list ablock) : wit := mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) T (w_FA W) (w_ms W) (w_zc W).

Lemma twin_mapped_ms : forall L RNG st LBa ms b g, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b ->
  0 <= g -> 8 * g < ab_size b ->
  ms (wa (shad (ab_addr b) + g)) <> None.
Proof.
  intros L RNG st LBa ms [k A n] g AH Hb [p Hp] G0 G1. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (N & BR & _ & _ & (bs & CELL & _) & _).
  destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _).
  destruct CELL as [[[LEN _] (B0 & B1 & BRD)] _]. cbn [ALib.Cells.cells_bytes ALib.Cells.cbytes] in B1, BRD. rewrite app_nil_r in B1, BRD. cbn in LEN.
  assert (GZ : g < shlen (n + 7)) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -G0 G1; Z.div_mod_to_equations; lia).
  assert (GL : (Z.to_nat g < length bs)%nat) by (rewrite LEN; lia).
  specialize (BRD (Z.to_nat g) GL). rewrite Z2Nat.id in BRD by lia.
  rewrite (Shadow.mrd_no_image bsegs ms 0x631000 (2^64) (shad A + g) (RtCells.TwinB.no_image_asan 0x631000 (2^64) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) in BRD.
  rewrite BRD. intros E. apply nth_error_None in E. lia.
Qed.
Lemma twin_bytes_sec : forall L RNG st LBa ms b g, AHEAP AI L RNG st LBa ms -> In b LBa -> is_heap b -> is_primary (ab_size b) = false ->
  0 <= g -> 8 * g < ab_size b ->
  ms (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof.
  intros L RNG st LBa ms [k A n] g AH Hb [p Hp] NP G0 G1. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (AI_block AI L RNG st LBa ms p A n AH Hb) as (_ & _ & _ & _ & (bs & _ & SH) & _). exact (SH NP g G0 G1).
Qed.

Lemma shadow_iv_inj : forall L RNG st LBa ms b b', AHEAP AI L RNG st LBa ms -> In b LBa -> In b' LBa ->
  shad (ab_addr b) = shad (ab_addr b') -> b = b'.
Proof.
  intros L RNG st LBa ms b b' AH Hb Hb' E. destruct (ablock_eq_dec b b') as [EQ|NE]; [exact EQ| exfalso].
  destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & A8 & _). destruct (blk_facts _ _ _ _ _ b' AH Hb') as (NP' & BK' & HI' & A8' & _).
  destruct (user_app_band _ _ BK NP) as [_ B2]. destruct (user_app_band _ _ BK' NP') as [_ B2'].
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NE) as D.
  unfold shad, ASHOFF in E. rewrite !Z.shiftr_div_pow2 in E by ulia. change (2^3) with 8 in E. destruct D; Z.div_mod_to_equations; ulia.
Qed.

Lemma twin_out_w : forall W aw LB m mo b,
  aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  aw_holds_w (set_T W (b :: w_T W)) aw (twin_iv b :: LB) m mo
  /\ ~ In (twin_iv b) LB
  /\ (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
Proof.
  intros W aw LB m mo b HW Vb HH NT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as AR. destruct Vb as [Hb NFA].
  destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & BR & _). destruct (twin_band _ _ BR N) as (T1 & T2 & T3 & _).

  assert (MEQ : forall a, in_iv (twin_iv b) a -> w_ms W (wa a) = m (wa a)).
  { intros a Ha. apply EQ; [unfold in_iv, twin_iv in Ha; cbn [fst snd] in Ha; unfold two64; ulia|].
    intros X. apply in_ivs_In in X as (w & Hw & Hwa). apply in_map_iff in Hw as (b' & <- & Hb'T).
    destruct (HT b' Hb'T) as [Hb'L Hb'H].
    assert (NE : b <> b') by (intros ->; exact (NT Hb'T)).
    destruct (heap_block_facts _ _ _ _ _ b' AH Hb'L Hb'H) as (N' & BR' & _).
    destruct BR as (BK & N0 & HI & AL). destruct BR' as (BK' & N0' & HI' & AL').
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb'L NE) as D.
    unfold in_iv, twin_iv in Ha, Hwa. cbn [fst snd] in Ha, Hwa.
    refine (gran_disj (ab_addr b) (ab_size b) (ab_addr b') (ab_size b') a _ _ _ _ D _ _ Ha Hwa); unfold ablk, AIMG_HI, KLS in *; try ulia; Z.div_mod_to_equations; ulia. }
  assert (PAT : forall g, 0 <= g -> 8 * g < ab_size b ->
            m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))).
  { intros g G0 G1. exact (INC b (conj Hb NFA) HH NT g G0 G1). }
  assert (NIN : ~ In (twin_iv b) LB).
  { intros X. destruct (LB_cases W aw LB m mo _ HW X) as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
    - destruct (LB_user_facts W aw LB m mo b' HW Vb') as (_ & B1 & _). unfold twin_iv, user_iv in E. injection E as E1 E2. ulia.
    - apply NT. replace b with b'; [exact Hb'|]. symmetry. apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb (proj1 (HT b' Hb'))).
      unfold twin_iv in E. injection E as E1 _. exact E1.
    - destruct Vb' as [[Hb'L _] HF']. assert (b = b') as <-; [| exact (heap_not_fake b HH HF')].
      apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb Hb'L). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1. }
  split; [| split; [exact NIN| exact PAT]].
  unfold aw_holds_w, set_T. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split. { intros b0 [<-|Hb0]; [split; [exact Hb| exact HH]| exact (HT b0 Hb0)]. }
  split; [constructor; assumption|]. split; [exact HFA|]. split; [exact NDF|]. split.
  { intros v. cbn [In]. rewrite (HLB v). split.
    - intros [<-|[H|[(b0 & H0 & ->)|H]]]; [right; left; exists b; split; [left; reflexivity| reflexivity]| left; exact H| right; left; exists b0; split; [right; exact H0| reflexivity]| right; right; exact H].
    - intros [H|[(b0 & [<-|H0] & ->)|H]]; [right; left; exact H| left; reflexivity| right; right; left; exists b0; split; [exact H0| reflexivity]| right; right; right; exact H]. }
  split.
  { intros a Ha NTW. apply EQ; [exact Ha|]. intros X. apply NTW. cbn [map]. apply in_ivs_cons. right. exact X. }
  split; [| split; [exact ZC0| split; [exact ZCB| split; [exact AC| split; [exact HU| split; [exact CLS| split; [exact VFL|]]]]]]].
  2:{ intros b0 Vb0 HH0 NT0. apply (INC b0 Vb0 HH0). intros X. apply NT0. right. exact X. }
  intros a Ha. cbn [map] in Ha. apply in_ivs_cons in Ha as [Ha|Ha]; [| exact (MAP a Ha)].
  pose proof Ha as Ha'. unfold in_iv, twin_iv in Ha'. cbn [fst snd] in Ha'.
  assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
  { unfold shlen in Ha'. rewrite Z.shiftr_div_pow2 in Ha' by ulia. change (2^3) with 8 in Ha'. Z.div_mod_to_equations. ulia. }
  pose proof (PAT (a - shad (ab_addr b)) (proj1 G) (proj2 G)) as P. replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia.
  intros X. rewrite X in P. discriminate.
Qed.

Definition aw_realW (aw : word) (LB : blocks) (m : amem) (mo : Model) (W : wit) : Prop := aw_holds_w W aw LB m mo /\ w_ms W = m.

Lemma aw_real_holds : forall aw LB m mo W, aw_realW aw LB m mo W -> aw_holds_asan aw LB m mo.
Proof. intros aw LB m mo W [H _]. exists W. exact H. Qed.

Definition wit_of (W : wit) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) : Prop :=
  w_L W = L /\ w_RNG W = RNG /\ w_st W = st /\ w_LBa W = LBa.
Definition aw_real (aw : word) (LB : blocks) (m : amem) (mo : Model) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) : Prop :=
  exists W, wit_of W L RNG st LBa /\ aw_realW aw LB m mo W.
Lemma wit_of_refl : forall W, wit_of W (w_L W) (w_RNG W) (w_st W) (w_LBa W).
Proof. intros W. repeat split. Qed.
Lemma aw_real_of : forall aw LB m mo W, aw_realW aw LB m mo W -> aw_real aw LB m mo (w_L W) (w_RNG W) (w_st W) (w_LBa W).
Proof. intros aw LB m mo W H. exists W. split; [apply wit_of_refl| exact H]. Qed.
Lemma aw_realW_AHEAP : forall aw LB m mo W, aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m /\ ACCT aw (w_L W) (w_RNG W) (w_st W) (w_LBa W) mo /\ incl UNIV (al_U (w_L W)).
Proof. intros aw LB m mo W [(AH & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & HU & _) EM]. rewrite <- EM. auto. Qed.
Lemma aw_real_AHEAP : forall aw LB m mo L RNG st LBa, aw_real aw LB m mo L RNG st LBa ->
  AHEAP AI L RNG st LBa m /\ ACCT aw L RNG st LBa mo /\ incl UNIV (al_U L).
Proof. intros aw LB m mo L RNG st LBa (W & (<- & <- & <- & <-) & H). exact (aw_realW_AHEAP _ _ _ _ _ H). Qed.

Lemma LB_band : forall W aw LB m mo a, aw_holds_w W aw LB m mo -> in_user LB a ->
  (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP) \/ (0x800be200 <= a < 0x10007fff8000).
Proof.
  intros W aw LB m mo a HW IU. pose proof HW as (AH & HT & _). pose proof atop_range as AR.
  unfold in_user in IU. apply in_ivs_In in IU as (v & Hv & Hin). unfold in_iv in Hin.
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
  - destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (N0 & BK & TOP & _). unfold ablk, AIMG_HI, KLS in *. ulia.
  - destruct (HT b Hb) as [HbL HH]. destruct (heap_block_facts _ _ _ _ _ b AH HbL HH) as (N & (BK & N0 & HI & AL) & _).
    destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3).
    right; right. split; [| ulia]. unfold ablk, AIMG_HI, KLS in BK. revert Hin. unfold shad, ASHOFF.
    rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. intros Hin. Z.div_mod_to_equations. ulia.
  - destruct (blk_facts _ _ _ _ _ b AH (proj1 (proj1 Vb))) as (N0 & BK & TOP & _).
    destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & T3 & T4 & T5).
    right; right. split; [| ulia]. unfold ablk, AIMG_HI, KLS in BK. unfold ASHOFF in T4. ulia.
Qed.

Lemma aw_real_user_band : forall aw LB m mo L RNG st LBa a, aw_real aw LB m mo L RNG st LBa -> in_user LB a ->
  (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP) \/ (0x800be200 <= a < 0x10007fff8000).
Proof. intros aw LB m mo L RNG st LBa a (W & _ & [HW _]) IU. exact (LB_band W aw LB m mo a HW IU). Qed.

Lemma blk_band : forall L RNG st LBa (m : amem) b x, AHEAP AI L RNG st LBa m -> In b LBa -> ab_addr b <= x < ab_addr b + ab_size b ->
  (AIMG_HI <= x < KLS) \/ (0x10007fff8000 <= x < ATOP).
Proof.
  intros L RNG st LBa m b x AH Hb Hx. destruct (blk_facts _ _ _ _ _ b AH Hb) as (N0 & BK & TOP & _). unfold ablk in BK. ulia.
Qed.

Lemma AHEAP_ext : forall L RNG st LBa (m1 m2 : amem), AHEAP AI L RNG st LBa m1 -> (forall x : word, m2 x = m1 x) -> AHEAP AI L RNG st LBa m2.
Proof.
  intros L RNG st LBa m1 m2 AH E. eapply (AI_frame AI _ _ _ _ m1 m2 []); [exact AH | intros x _; apply E | | apply Forall_nil].
  intros x Hx. rewrite (wview_ext1 m2 m1 x (E x)). exact Hx.
Qed.

Lemma aw_holds_real_w : forall W aw LB m mo,
  aw_holds_w W aw LB m mo ->
  (forall b, In b (w_T W) -> is_primary (ab_size b) = false -> forall g, 0 <= g -> 8 * g < ab_size b ->
     St.rb bsegs m (shad (ab_addr b) + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  aw_realW aw LB m mo (set_ms W m).
Proof.
  intros W aw LB m mo HW PAT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as ATR.
  set (patch := fun (l : list ablock) (x : word) => if in_ivs_b (map twin_iv l) (bv_unsigned x) then m x else w_ms W x).
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).

  assert (MAPb : forall b g, In b (w_T W) -> 0 <= g < shlen (ab_size b + 7) -> m (wa (shad (ab_addr b) + g)) <> None).
  { intros b g HbT Hg. apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT| unfold in_iv, twin_iv; cbn [fst snd]; lia]. }
  assert (CH : forall l, (forall b, In b l -> In b (w_T W)) -> AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (patch l)).
  { induction l as [|b l IH]; intros SUB.
    - eapply AHEAP_ext; [exact AH|]. intros x. unfold patch. cbn [map in_ivs_b]. reflexivity.
    - specialize (IH ltac:(intros x Hx; apply SUB; right; exact Hx)).
      assert (HbT : In b (w_T W)) by (apply SUB; left; reflexivity). destruct (HT b HbT) as [HbL HbH].
      destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (Nb & BRb & _).
      assert (OUTS : forall x : word, ~ in_iv (twin_iv b) (bv_unsigned x) -> patch (b :: l) x = patch l x).
      { intros x NIN. unfold patch. cbn [map in_ivs_b]. unfold in_iv in NIN.
        replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct (Z.leb_spec (fst (twin_iv b)) (bv_unsigned x)); [right; apply Z.ltb_ge; lia| left; reflexivity]. }
      assert (INS : forall x : word, in_iv (twin_iv b) (bv_unsigned x) -> patch (b :: l) x = m x).
      { intros x HIN. unfold patch. cbn [map in_ivs_b]. unfold in_iv in HIN.
        replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with true; [reflexivity|].
        symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      destruct (is_primary (ab_size b)) eqn:PRIM.
      +
        destruct b as [[p|c] A n]; [| destruct HbH as [q Hq]; discriminate]. cbn [ab_addr ab_size twin_iv fst snd] in *.
        eapply (AI_frame_twin AI _ _ _ _ (patch l) (patch (HB p A n :: l)) p A n IH HbL PRIM).
        * intros x OUT. cbn [ALib.Frame.outside] in OUT. apply OUTS. unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. lia.
        * intros x Hx. destruct (in_ivs_b [twin_iv (HB p A n)] (bv_unsigned x)) eqn:TW.
          -- apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
             pose proof (INS x TW) as E1. unfold wview. rewrite E1.
             assert (MP : m x <> None).
             { rewrite <- (WAX x). unfold in_iv, twin_iv in TW. cbn [fst snd ab_addr ab_size] in TW.
               replace (bv_unsigned x) with (shad A + (bv_unsigned x - shad A)) by lia. apply (MAPb (HB p A n) _ HbT). cbn [ab_addr ab_size]. lia. }
             destruct (m x); [discriminate| contradiction].
          -- assert (NIN : ~ in_iv (twin_iv (HB p A n)) (bv_unsigned x)).
             { intros X. assert (Y : in_ivs [twin_iv (HB p A n)] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
             rewrite (wview_ext1 (patch (HB p A n :: l)) (patch l) x (OUTS x NIN)). exact Hx.
        * intros i Hi. rewrite (INS (wa (shad A + i))).
          -- apply (MAPb (HB p A n) i HbT). cbn [ab_size]. exact Hi.
          -- unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. rewrite UWA by lia. lia.
      +
        eapply AHEAP_ext; [exact IH|]. intros x.
        destruct (in_ivs_b [twin_iv b] (bv_unsigned x)) eqn:TW.
        * apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
          rewrite (INS x TW). pose proof TW as TW'. unfold in_iv, twin_iv in TW'. cbn [fst snd] in TW'.
          assert (G : 0 <= bv_unsigned x - shad (ab_addr b) /\ 8 * (bv_unsigned x - shad (ab_addr b)) < ab_size b).
          { unfold shlen in TW'. rewrite Z.shiftr_div_pow2 in TW' by ulia. change (2^3) with 8 in TW'. Z.div_mod_to_equations. ulia. }
          pose proof (twin_bytes_sec _ _ _ _ _ b _ IH HbL HbH PRIM (proj1 G) (proj2 G)) as P2.
          pose proof (PAT b HbT PRIM _ (proj1 G) (proj2 G)) as P1.
          replace (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) with (bv_unsigned x) in P1, P2 by ulia.
          rewrite WAX in P2. unfold St.rb in P1. rewrite Z_to_bv_bv_unsigned in P1.
          assert (MP : m x <> None).
          { rewrite <- (WAX x). replace (bv_unsigned x) with (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) by lia. apply (MAPb b _ HbT). lia. }
          destruct (m x) as [y|]; [congruence| contradiction].
        * apply OUTS. intros X. assert (Y : in_ivs [twin_iv b] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
  assert (PW : forall x : word, m x = patch (w_T W) x).
  { intros x. unfold patch. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with two64 in R.
    destruct (in_ivs_b (map twin_iv (w_T W)) (bv_unsigned x)) eqn:TW; [reflexivity|].
    assert (NTW : ~ in_ivs (map twin_iv (w_T W)) (bv_unsigned x)) by (rewrite <- in_ivs_b_spec; congruence).
    pose proof (EQ (bv_unsigned x) R NTW) as E1. rewrite WAX in E1. congruence. }
  split; [| reflexivity].
  unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split. { eapply AHEAP_ext; [exact (CH (w_T W) (fun b H => H))| exact PW]. }
  split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|]. split; [exact MAP|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC| split; [exact HU| split; [exact CLS| split; [| exact INC]]]].

  apply (vfl_agree W aw LB m mo m HW). intros b x [[HbL NFA] HF] Hx.
  destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (BK & HI & A8 & N8 & NP & _).
  destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
  symmetry. apply EQ; [unfold two64; lia|].
  intros X. apply in_ivs_In in X as (w & Hw & Hin). apply in_map_iff in Hw as (b' & <- & Hb').
  destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. lia.
Qed.

Definition patch1 (W : wit) (m : amem) (b : ablock) : amem := fun x => if in_ivs_b [twin_iv b] (bv_unsigned x) then m x else w_ms W x.
Definition wit_twin_in (W : wit) (m : amem) (b : ablock) : wit :=
  mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (lb_del b (w_T W)) (w_FA W) (patch1 W m b) (w_zc W).

Lemma twin_in_w : forall W aw LB m mo b,
  aw_holds_w W aw LB m mo -> In b (w_T W) ->
  (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  aw_holds_w (wit_twin_in W m b) aw (List.remove iv_eq_dec (twin_iv b) LB) m mo.
Proof.
  intros W aw LB m mo b HW HbT PAT. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  pose proof atop_range as ATR. destruct (HT b HbT) as [HbL HbH].
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HbH) as (Nb & BRb & _).
  assert (WAX : forall x : word, wa (bv_unsigned x) = x) by (intros x; unfold wa; apply Z_to_bv_bv_unsigned).
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).
  assert (MAPb : forall g, 0 <= g < shlen (ab_size b + 7) -> m (wa (shad (ab_addr b) + g)) <> None).
  { intros g Hg. apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT| unfold in_iv, twin_iv; cbn [fst snd]; lia]. }
  assert (OUTS : forall x : word, ~ in_iv (twin_iv b) (bv_unsigned x) -> patch1 W m b x = w_ms W x).
  { intros x NIN. unfold patch1. cbn [in_ivs_b]. unfold in_iv in NIN.
    replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z.leb_spec (fst (twin_iv b)) (bv_unsigned x)); [right; apply Z.ltb_ge; lia| left; reflexivity]. }
  assert (INS : forall x : word, in_iv (twin_iv b) (bv_unsigned x) -> patch1 W m b x = m x).
  { intros x HIN. unfold patch1. cbn [in_ivs_b]. unfold in_iv in HIN.
    replace ((fst (twin_iv b) <=? bv_unsigned x) && (bv_unsigned x <? fst (twin_iv b) + snd (twin_iv b))) with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  assert (AH' : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) (patch1 W m b)).
  { destruct (is_primary (ab_size b)) eqn:PRIM.
    - destruct b as [[p|c] A n]; [| destruct HbH as [q Hq]; discriminate]. cbn [ab_addr ab_size twin_iv fst snd] in *.
      eapply (AI_frame_twin AI _ _ _ _ (w_ms W) (patch1 W m (HB p A n)) p A n AH HbL PRIM).
      + intros x OUT. cbn [ALib.Frame.outside] in OUT. apply OUTS. unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. lia.
      + intros x Hx. destruct (in_ivs_b [twin_iv (HB p A n)] (bv_unsigned x)) eqn:TW.
        * apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
          pose proof (INS x TW) as E1. unfold wview. rewrite E1.
          assert (MP : m x <> None).
          { rewrite <- (WAX x). unfold in_iv, twin_iv in TW. cbn [fst snd ab_addr ab_size] in TW.
            replace (bv_unsigned x) with (shad A + (bv_unsigned x - shad A)) by lia. apply MAPb. lia. }
          destruct (m x); [discriminate| contradiction].
        * assert (NIN : ~ in_iv (twin_iv (HB p A n)) (bv_unsigned x)).
          { intros X. assert (Y : in_ivs [twin_iv (HB p A n)] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
          rewrite (wview_ext1 (patch1 W m (HB p A n)) (w_ms W) x (OUTS x NIN)). exact Hx.
      + intros i Hi. rewrite (INS (wa (shad A + i))).
        * apply MAPb. exact Hi.
        * unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. rewrite UWA by lia. lia.
    - eapply AHEAP_ext; [exact AH|]. intros x.
      destruct (in_ivs_b [twin_iv b] (bv_unsigned x)) eqn:TW.
      + apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW].
        rewrite (INS x TW). pose proof TW as TW'. unfold in_iv, twin_iv in TW'. cbn [fst snd] in TW'.
        assert (G : 0 <= bv_unsigned x - shad (ab_addr b) /\ 8 * (bv_unsigned x - shad (ab_addr b)) < ab_size b).
        { unfold shlen in TW'. rewrite Z.shiftr_div_pow2 in TW' by ulia. change (2^3) with 8 in TW'. Z.div_mod_to_equations. ulia. }
        pose proof (twin_bytes_sec _ _ _ _ _ b _ AH HbL HbH PRIM (proj1 G) (proj2 G)) as P2.
        pose proof (PAT _ (proj1 G) (proj2 G)) as P1.
        replace (shad (ab_addr b) + (bv_unsigned x - shad (ab_addr b))) with (bv_unsigned x) in P1, P2 by ulia.
        rewrite WAX in P1, P2. congruence.
      + apply OUTS. intros X. assert (Y : in_ivs [twin_iv b] (bv_unsigned x)) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
  assert (TIN : forall a, in_ivs (map twin_iv (w_T W)) a -> in_iv (twin_iv b) a \/ in_ivs (map twin_iv (lb_del b (w_T W))) a).
  { intros a X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
    destruct (ablock_eq_dec b' b) as [->|NE]; [left; exact Hin| right]. apply in_ivs_In. exists (twin_iv b'). split; [| exact Hin].
    apply in_map. apply lb_del_In. split; assumption. }
  unfold aw_holds_w, wit_twin_in. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|].
  split. { intros b0 Hb0. apply lb_del_In in Hb0 as [Hb0 _]. exact (HT b0 Hb0). }
  split. { unfold lb_del. apply List.NoDup_filter. exact ND. }
  split; [exact HFA|]. split; [exact NDF|].
  split.
  { intros v. split.
    - intros Hv. apply in_remove in Hv as [Hv NEv]. apply HLB in Hv as [H|[(b0 & H0 & ->)|H]]; [left; exact H| | right; right; exact H].
      right; left. exists b0. split; [| reflexivity]. apply lb_del_In. split; [exact H0|]. intros ->. apply NEv. reflexivity.
    - intros H. apply in_in_remove.
      + destruct H as [(b0 & Vb0 & ->)|[(b0 & Hb0 & ->)|(b0 & Vb0 & ->)]].
        * destruct (LB_user_facts W aw LB m mo b0 HW Vb0) as (U0 & B1 & _). pose proof (usz_le b0) as UL. unfold twin_iv, user_iv. intros E. injection E as E1 _. ulia.
        * apply lb_del_In in Hb0 as [Hb0 NE]. intros E. apply NE. apply (shadow_iv_inj _ _ _ _ _ b0 b AH (proj1 (HT b0 Hb0)) HbL).
          unfold twin_iv in E. injection E as E1 _. exact E1.
        * destruct Vb0 as [[Hb0L _] HF0]. intros E. assert (b0 = b) as ->; [| exact (heap_not_fake b HbH HF0)].
          apply (shadow_iv_inj _ _ _ _ _ b0 b AH Hb0L HbL). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1.
      + apply HLB. destruct H as [H|[(b0 & Hb0 & ->)|H]]; [left; exact H| | right; right; exact H].
        right; left. exists b0. split; [| reflexivity]. apply lb_del_In in Hb0 as [Hb0 _]. exact Hb0. }
  split.
  { intros a Ha NTW. destruct (in_ivs_b [twin_iv b] a) eqn:TW.
    - apply in_ivs_b_spec in TW. apply in_ivs_cons in TW as [TW|TW]; [| inversion TW]. apply INS. rewrite UWA by (unfold two64 in Ha; lia). exact TW.
    - assert (NIN : ~ in_iv (twin_iv b) a).
      { intros X. assert (Y : in_ivs [twin_iv b] a) by (apply in_ivs_cons; left; exact X). apply in_ivs_b_spec in Y. congruence. }
      rewrite OUTS by (rewrite UWA by (unfold two64 in Ha; lia); exact NIN). apply EQ; [exact Ha|].
      intros X. destruct (TIN a X) as [Y|Y]; [exact (NIN Y)| exact (NTW Y)]. }
  split.
  { intros a Ha. apply MAP. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb'). apply lb_del_In in Hb' as [Hb' _].
    apply in_ivs_In. exists (twin_iv b'). split; [apply in_map; exact Hb'| exact Hin]. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC|]. split; [exact HU|]. split; [exact CLS|]. split.
  -
    apply (vfl_agree W aw LB m mo (patch1 W m b) HW). intros b0 x [[Hb0L NFA0] HF0] Hx.
    destruct (AI_fake _ _ _ _ _ b0 AH Hb0L HF0) as (BK0 & HI0 & A80 & N80 & NP0 & _).
    destruct (user_app_band _ _ BK0 ltac:(lia)) as [B1 B2].
    apply OUTS. rewrite UWA by lia. unfold in_iv, twin_iv. cbn [fst snd]. lia.
  - intros b0 Vb0 HH0 NT0. destruct (ablock_eq_dec b0 b) as [->|NE]; [exact PAT|].
    apply (INC b0 Vb0 HH0). intros X. apply NT0. apply lb_del_In. split; assumption.
Qed.

Lemma shad_band_sep : forall s a, 0x7fff8000 <= s < 0x10007fff8000 -> 0 <= a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> shad s <> shad a.
Proof. intros s a S A0 B. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by ulia. change (2^3) with 8. Z.div_mod_to_equations. ulia. Qed.

Lemma twin_owner_w : forall W aw LB m mo b A' n',
  aw_holds_w W aw LB m mo -> In b (w_T W) -> In (A', n') LB -> shad A' = shad (ab_addr b) ->
  A' = ab_addr b /\ n' = ab_size b /\ 1 <= ab_size b <= AREQMAX.
Proof.
  intros W aw LB m mo b A' n' HW HbT H' SH. pose proof HW as (AH & HT & _). pose proof atop_range as AR.
  destruct (HT b HbT) as [Hb HH]. destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (N & (BK & _) & _).
  destruct (user_app_band _ _ BK ltac:(ulia)) as [B1 B2].
  destruct (LB_cases W aw LB m mo _ HW H') as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
  - unfold user_iv in E. injection E as -> ->. rewrite (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 Vb') Hb SH). rewrite (usz_heap b HH). auto.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & T3). unfold twin_iv in E. injection E as -> _.
    apply (shad_band_sep (shad (ab_addr b')) (ab_addr b)); [ulia| ulia| ulia| exact SH].
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & T3 & _). unfold fsh_iv in E. injection E as -> _.
    apply (shad_band_sep (shad (ab_addr b')) (ab_addr b)); [ulia| ulia| ulia| exact SH].
Qed.

Lemma LB_same_addr : forall W aw LB m mo A0 n0 n1, aw_holds_w W aw LB m mo -> In (A0, n0) LB -> In (A0, n1) LB -> n0 = n1.
Proof.
  intros W aw LB m mo A0 n0 n1 HW H0 H1. pose proof HW as (AH & HT & _ & HFA & _). pose proof atop_range as AR.
  assert (SAME : forall b b', In b (w_LBa W) -> In b' (w_LBa W) -> ab_addr b = ab_addr b' -> b = b').
  { intros b b' Hb Hb' EA. apply (shadow_iv_inj _ _ _ _ _ b b' AH Hb Hb'). rewrite EA. reflexivity. }
  destruct (LB_cases W aw LB m mo _ HW H0) as [(b & Vb & E)|[(b & Hb & E)|(b & Vb & E)]];
  destruct (LB_cases W aw LB m mo _ HW H1) as [(b' & Vb' & E')|[(b' & Hb' & E')|(b' & Vb' & E')]];
    unfold user_iv, twin_iv, fsh_iv in E, E'; injection E as EA EN; injection E' as EA' EN'.
  all: try (destruct (LB_user_facts W aw LB m mo b HW Vb) as (? & ? & ? & ?)); try (destruct (LB_user_facts W aw LB m mo b' HW Vb') as (? & ? & ? & ?)).
  all: try (destruct (LB_twin_facts W aw LB m mo b HW Hb) as (? & ? & ?)); try (destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (? & ? & ?)).
  all: try (destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (? & ? & ? & ? & ?)); try (destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (? & ? & ? & ? & ?)).
  all: try ulia.
  - rewrite (SAME b b' (proj1 Vb) (proj1 Vb') ltac:(congruence)) in EN. congruence.
  - assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (HT b' Hb'))); congruence). congruence.
  - exfalso. assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (proj1 Vb'))); congruence).
    exact (heap_not_fake b (proj2 (HT b Hb)) (proj2 Vb')).
  - exfalso. assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (HT b' Hb'))); congruence).
    exact (heap_not_fake b (proj2 (HT b Hb')) (proj2 Vb)).
  - assert (b = b') as <- by (apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (proj1 Vb'))); congruence). congruence.
Qed.

Lemma twin_T_facts : forall W aw LB m mo b, aw_holds_w W aw LB m mo -> In b (w_T W) ->
  In b (w_LBa W) /\ vis W b /\ In (user_iv b) LB /\ In (twin_iv b) LB /\ (exists p, b = HB p (ab_addr b) (ab_size b))
  /\ 1 <= ab_size b <= AREQMAX /\ ab_addr b mod 16 = 0 /\ user_band (ab_addr b) /\ ~ user_band (shad (ab_addr b)).
Proof.
  intros W aw LB m mo b HW HbT. pose proof HW as (AH & HT & _ & HFA & _ & HLB & _). destruct (HT b HbT) as [HbL HH].
  assert (VB : vis W b) by (split; [exact HbL| intros X; exact (heap_not_fake b HH (proj2 (HFA b X)))]).
  destruct (heap_block_facts _ _ _ _ _ b AH HbL HH) as (N & (BK & _ & _ & AL) & _).
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3). destruct (user_app_band _ _ BK ltac:(ulia)) as [B1 B2].
  split; [exact HbL|]. split; [exact VB|].
  split; [apply HLB; left; exists b; split; [exact VB| reflexivity]|].
  split; [apply HLB; right; left; exists b; split; [exact HbT| reflexivity]|].
  split. { destruct b as [[q|c] A n]; [exists q; reflexivity| destruct HH as [q Hq]; discriminate]. }
  split; [exact N|]. split; [exact AL|]. split; [unfold user_band; ulia| unfold user_band; ulia].
Qed.

Lemma twin_container : forall W aw LB m mo b v, aw_holds_w W aw LB m mo -> In b (w_T W) -> In v LB ->
  (forall a, in_iv (twin_iv b) a -> in_iv v a) -> v = twin_iv b.
Proof.
  intros W aw LB m mo b v HW HbT Hv SUB. destruct (twin_T_facts W aw LB m mo b HW HbT) as (_ & _ & _ & HTW & _).
  destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  assert (WNE : in_iv (twin_iv b) (shad (ab_addr b))) by (unfold in_iv, twin_iv; cbn [fst snd]; ulia).
  destruct v as [Av nv]. destruct (Z.eq_dec Av (shad (ab_addr b))) as [->|NA].
  - unfold twin_iv. f_equal. exact (LB_same_addr W aw LB m mo _ _ _ HW Hv HTW).
  - exfalso. apply (aw_blocks_disj_asan aw LB m mo (Av, nv) (twin_iv b) (shad (ab_addr b)) (ex_intro _ W HW) Hv HTW); [cbn [fst twin_iv]; exact NA| exact (SUB _ WNE)| exact WNE].
Qed.

Lemma LB_classify : forall W aw LB m mo, aw_holds_w W aw LB m mo ->
     (forall v, In v LB -> user_band (fst v) -> 0 < snd v -> exists b, vis W b /\ v = user_iv b)
  /\ (forall v, In v LB -> ~ user_band (fst v) -> (exists b, In b (w_T W) /\ v = twin_iv b) \/ (exists b, visf W b /\ v = fsh_iv b)).
Proof.
  intros W aw LB m mo HW. split.
  - intros v Hv UB P. destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    + exists b. split; [exact Vb| reflexivity].
    + exfalso. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). unfold user_band, twin_iv in UB. cbn [fst] in UB. ulia.
    + exfalso. destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & T3 & _). unfold user_band, fsh_iv in UB. cbn [fst] in UB. ulia.
  - intros v Hv NUB. destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
    + exfalso. apply NUB. destruct (LB_user_facts W aw LB m mo b HW Vb) as (P & B1 & _). unfold user_band, user_iv. cbn [fst]. ulia.
    + left. exists b. split; [exact Hb| reflexivity].
    + right. exists b. split; [exact Vb| reflexivity].
Qed.

Lemma hb_unique : forall L RNG st LBa m b b' p, AHEAP AI L RNG st LBa m -> In b LBa -> In b' LBa ->
  ab_kind b = ABHeap p -> ab_kind b' = ABHeap p -> b = b'.
Proof.
  intros L RNG st LBa m b b' p AH Hb Hb' K K'. pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND. clear AH.
  induction LBa as [|x l IH]; [destruct Hb|]. cbn [hb_ids flat_map] in ND.
  assert (INID : forall y, In y l -> ab_kind y = ABHeap p -> In p (hb_ids l)).
  { intros y Hy Ky. unfold hb_ids. apply in_flat_map. exists y. split; [exact Hy|]. rewrite Ky. left. reflexivity. }
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
  - reflexivity.
  - exfalso. rewrite K in ND. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID b' Hb' K')).
  - exfalso. rewrite K' in ND. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID b Hb K)).
  - apply IH; [exact Hb| exact Hb'|]. destruct (ab_kind x); cbn [app] in ND; [apply NoDup_cons_iff in ND as [_ ND]; exact ND| exact ND].
Qed.

Lemma lb_remove_In : forall L RNG st LBa m p A n b, AHEAP AI L RNG st LBa m -> In (HB p A n) LBa ->
  (In b (lb_remove p LBa) <-> (In b LBa /\ b <> HB p A n)).
Proof.
  intros L RNG st LBa m p A n b AH HP. rewrite AFreeRep.TwinB.In_lb_remove. split.
  - intros [Hb NK]. split; [exact Hb|]. intros ->. apply NK. reflexivity.
  - intros [Hb NE]. split; [exact Hb|]. intros K. apply NE. exact (hb_unique L RNG st LBa m b (HB p A n) p AH Hb HP K eq_refl).
Qed.

Definition LB_free (LB : blocks) (A n : Z) : blocks := List.remove iv_eq_dec (shad A, shlen (n + 7)) (List.remove iv_eq_dec (A, n) LB).

Lemma LB_free_In : forall LB A n v, In v (LB_free LB A n) <-> (In v LB /\ v <> (A, n) /\ v <> (shad A, shlen (n + 7))).
Proof.
  intros LB A n v. unfold LB_free. split.
  - intros H. apply in_remove in H as [H N2]. apply in_remove in H as [H N1]. auto.
  - intros (H & N1 & N2). apply in_in_remove; [exact N2|]. apply in_in_remove; [exact N1| exact H].
Qed.

Lemma lb_remove_fake : forall p LBa b, In b LBa -> is_fake b -> In b (lb_remove p LBa).
Proof. intros p LBa b Hb [c K]. apply AFreeRep.TwinB.In_lb_remove. split; [exact Hb|]. rewrite K. discriminate. Qed.

Lemma vfl_keep : forall W aw LB m mo (m' : amem), aw_realW aw LB m mo W ->
  (forall b x, visf W b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  forall b, visf W b -> exists flg, bytes_at bsegs m' (ab_addr b + ab_size b - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) b flg.
Proof.
  intros W aw LB m mo m' [HW EM] KEEPF. apply (vfl_agree W aw LB m mo m' HW). intros b x Vb Hx.
  pose proof HW as (AH & _). pose proof Vb as [[HbL _] HF]. destruct (AI_fake _ _ _ _ _ b AH HbL HF) as (_ & _ & _ & _ & N64 & _).
  rewrite EM. apply (KEEPF b x Vb). lia.
Qed.
Lemma pres_block : forall LBp sp (m m' : amem) b x, aheap_pres (aci AI) LBp sp m m' -> In b LBp -> 0 <= ab_addr b -> ab_addr b + ab_size b <= 2^64 ->
  ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x).
Proof.
  intros LBp sp m m' b x PRES Hb A0 AH Hx. apply (proj1 (PRES x ltac:(lia) ltac:(right; right; left; exists b; split; [exact Hb| lia]))).
Qed.

Lemma twin_keep : forall L RNG' st' LBa' (m m' : amem) LBx b,
  AHEAP AI L RNG' st' LBa' m' -> In b LBa' -> is_heap b -> twins_pres LBx m m' -> In b LBx ->
  (forall g, 0 <= g -> 8 * g < ab_size b -> m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g))) ->
  forall g, 0 <= g -> 8 * g < ab_size b -> m' (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof.
  intros L RNG' st' LBa' m m' LBx b AH' Hb' HH TW HbX OLD g G0 G1.
  destruct (is_primary (ab_size b)) eqn:PRIM; [| exact (twin_bytes_sec _ _ _ _ _ b g AH' Hb' HH PRIM G0 G1)].
  destruct b as [[p|c] A n]; [| destruct HH as [q Hq]; discriminate]. cbn [ab_addr ab_size] in *.
  rewrite (TW p A n HbX PRIM g); [exact (OLD g G0 G1)|].
  unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia.
Qed.

Lemma twins_pres_band : forall L RNG st LBa (m m' : amem), AHEAP AI L RNG st LBa m ->
  (forall a, 0x800be200 <= a < shad ATOP -> m' (wa a) = m (wa a)) -> twins_pres LBa m m'.
Proof.
  intros L RNG st LBa m m' AH OUT p A n Hin PR i Hi.
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH Hin ltac:(exists p; reflexivity)) as (N & (BK & N0 & HI & AL) & _). cbn [ab_addr ab_size] in *.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. apply OUT. lia.
Qed.

Lemma aw_real_malloc : forall aw aw' LB m mo W RNG' st' p A n m' mo' sp,
  aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) RNG' st' (HB p A n :: w_LBa W) m' -> ACCT aw' (w_L W) RNG' st' (HB p A n :: w_LBa W) mo' ->
  aheap_pres (aci AI) (w_LBa W) sp m m' ->
  twins_pres (w_LBa W) m m' -> ablock_shadow m' A n ->
  let W1 := mkWit (w_L W) RNG' st' (HB p A n :: w_LBa W) (w_T W) (w_FA W) m' (w_zc W) in
  aw_realW aw' ((A, n) :: LB) m' mo' W1 /\ vis W1 (HB p A n) /\ ~ In (HB p A n) (w_T W)
  /\ user_band A /\ (forall a, in_iv (A, n) a -> ~ in_user LB a) /\ (forall a, in_iv (shad A, shlen (n + 7)) a -> ~ in_user LB a).
Proof.
  intros aw aw' LB m mo W RNG' st' p A n m' mo' sp [HW EM] AH' AC' PRES TW PATN W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH' ltac:(left; reflexivity) ltac:(exists p; reflexivity)) as (NN & BRN & _). cbn [ab_addr ab_size] in NN, BRN.
  destruct (twin_band _ _ BRN NN) as (TN1 & TN2 & TN3 & _). pose proof BRN as (BKN & _ & HIN & ALN).
  destruct (user_app_band _ _ BKN ltac:(ulia)) as [BN1 BN2].
  assert (DISJ : forall b, In b (w_LBa W) -> A + n <= ab_addr b \/ ab_addr b + ab_size b <= A).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p A n) b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  assert (NT : ~ In (HB p A n) (w_T W)) by (intros X; exact (NIN (proj1 (HT _ X)))).
  assert (NFA : ~ In (HB p A n) (w_FA W)) by (intros X; exact (NIN (proj1 (HFA _ X)))).

  assert (HW1 : aw_holds_w W1 aw' ((A, n) :: LB) m' mo').
  { unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
    split; [exact AH'|]. split. { intros b Hb. destruct (HT b Hb) as [H1 H2]. split; [right; exact H1| exact H2]. }
    split; [exact ND|]. split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [right; exact H1| exact H2]. }
    split; [exact NDF|]. split.
    { intros v. cbn [In]. rewrite (HLB v). unfold vis, visf. cbn [w_LBa w_FA]. split.
      - intros [<-|[(b & [Hb NF] & ->)|[H|(b & [[Hb NF] HF] & ->)]]].
        + left. exists (HB p A n). split; [split; [left; reflexivity| exact NFA]| reflexivity].
        + left. exists b. split; [split; [right; exact Hb| exact NF]| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [split; [right; exact Hb| exact NF]| exact HF]| reflexivity].
      - intros [(b & [[<-|Hb] NF] & ->)|[H|(b & [[[<-|Hb] NF] HF] & ->)]].
        + left. reflexivity.
        + right. left. exists b. split; [split; assumption| reflexivity].
        + right. right. left. exact H.
        + exfalso. exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) HF).
        + right. right. right. exists b. split; [split; [split; assumption| exact HF]| reflexivity]. }
    split; [intros a _ _; reflexivity|].
    split.
    {
      intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT).
      destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
      pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(right; exact HbL) HbH (proj1 G) (proj2 G)) as P.
      replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
    split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [exfalso; exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) FK)| exact (CLS b Hb FK)]. }
    split.
    2:{
        intros b [[<-|HbL] NFAb] HHb NTb; [exact PATN|].
        apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(right; exact HbL) HHb TW HbL).
        intros g G0 G1. exact (INC b (conj HbL NFAb) HHb NTb g G0 G1). }

    intros b [[[<-|HbL] NFAb] FKb]; [exfalso; exact (heap_not_fake (HB p A n) ltac:(exists p; reflexivity) FKb)|].
    assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] _] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block (w_LBa W) sp m m' b0 x PRES Hb0); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [left; reflexivity| exact NFA]|]. split; [exact NT|].
  split; [unfold user_band; ulia|]. split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b (proj1 Vb)). ulia.
    + destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & _). ulia.
  -
    intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b HW Vb) as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj A n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b H1) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj A n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b H1) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
Qed.

Lemma aw_real_free : forall aw aw' LB m mo W RNG' st' p A n m' mo' sp,
  aw_realW aw LB m mo W -> In (HB p A n) (w_LBa W) ->
  AHEAP AI (w_L W) RNG' st' (lb_remove p (w_LBa W)) m' -> ACCT aw' (w_L W) RNG' st' (lb_remove p (w_LBa W)) mo' ->
  aheap_pres (aci AI) (lb_remove p (w_LBa W)) sp m m' ->
  twins_pres (lb_remove p (w_LBa W)) m m' ->
  let W1 := mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W))
                  (w_FA W) m' (w_zc W) in
  aw_realW aw' (LB_free LB A n) m' mo' W1.
Proof.
  intros aw aw' LB m mo W RNG' st' p A n m' mo' sp [HW EM] HP AH' AC' PRES TW W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A n)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A n b AH HP)).
  set (T' := List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W)) in *.
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A n).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A n)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH HP ltac:(exists p; reflexivity)) as (NP & BRP & _). cbn [ab_addr ab_size] in NP, BRP.
  destruct (twin_band _ _ BRP NP) as (TP1 & TP2 & TP3 & _). pose proof BRP as (BKP & _). destruct (user_app_band _ _ BKP ltac:(ulia)) as [BP1 BP2].
  assert (SAMESH : forall b, In b (w_LBa W) -> shad (ab_addr b) = shad A -> b = HB p A n).
  { intros b Hb E. apply (shadow_iv_inj _ _ _ _ _ b (HB p A n) AH Hb HP). exact E. }
  split; [| reflexivity].
  unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc]. fold T'.
  split; [exact AH'|].
  split. { intros b Hb. apply INT' in Hb as [Hb NE]. destruct (HT b Hb) as [H1 H2]. split; [apply RM; split; assumption| exact H2]. }
  split; [apply NoDup_filter; exact ND|].
  split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [exact (lb_remove_fake p _ b H1 H2)| exact H2]. }
  split; [exact NDF|]. split.
  { intros v. rewrite LB_free_In. unfold vis, visf. cbn [w_LBa w_FA]. split.
    - intros (Hv & N1 & N2). destruct (LB_cases W aw LB m mo v HW Hv) as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + left. exists b. split; [| reflexivity]. split; [| exact NF]. apply RM. split; [exact Hb|]. intros ->. apply N1. reflexivity.
      + right. left. exists b. split; [| reflexivity]. apply INT'. split; [exact Hb|]. intros ->. apply N2. reflexivity.
      + right. right. exists b. split; [| reflexivity]. split; [split; [exact (lb_remove_fake p _ b Hb HF)| exact NF]| exact HF].
    - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + apply RM in Hb as [Hb NE]. split; [apply HLB; left; exists b; split; [split; assumption| reflexivity]|].
        destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (NPb & B1 & B2 & _). split.
        * intros X. unfold user_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact Hb| rewrite X1; reflexivity].
        * intros X. unfold user_iv in X. injection X as X1 _. ulia.
      + apply INT' in Hb as [Hb NE]. split; [apply HLB; right; left; exists b; split; [exact Hb| reflexivity]|].
        destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). split.
        * intros X. unfold twin_iv in X. injection X as X1 _. ulia.
        * intros X. unfold twin_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact (proj1 (HT b Hb))| exact X1].
      + assert (HbL : In b (w_LBa W)) by (apply RM in Hb; tauto).
        split; [apply HLB; right; right; exists b; split; [split; [split; assumption| exact HF]| reflexivity]|].
        destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj HbL NF) HF)) as (T1 & T2 & T3 & _). split.
        * intros X. unfold fsh_iv in X. injection X as X1 _. ulia.
        * intros X. unfold fsh_iv in X. injection X as X1 _. pose proof (SAMESH b HbL X1) as ->. exact (heap_not_fake (HB p A n) (ex_intro _ p eq_refl) HF). }
  split; [intros a _ _; reflexivity|].
  split.
  { intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT). apply INT' in HbT as [HbT NE].
    destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
    unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
    assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
    { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
    pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(apply RM; split; assumption) HbH (proj1 G) (proj2 G)) as P.
    replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
  split. { intros b Hb FK. exact (CLS b (proj1 (proj1 (RM b) Hb)) FK). }
  split.
  2:{
      intros b [HbR NFAb] HHb NTb. pose proof (proj1 (RM b) HbR) as [HbL NEb].
      apply (twin_keep _ _ _ _ m m' (lb_remove p (w_LBa W)) b AH' HbR HHb TW HbR).
      intros g G0 G1. apply (INC b (conj HbL NFAb) HHb); [| exact G0| exact G1].
      intros X. apply NTb. apply INT'. split; [exact X| exact NEb]. }

  intros b [[HbR NFAb] FKb]. apply RM in HbR as [HbL _].
  assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
  apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] FK0] Hx.
  destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
  apply (pres_block (lb_remove p (w_LBa W)) sp m m' b0 x PRES (lb_remove_fake p _ b0 Hb0 FK0)); [ulia| ulia| exact Hx].
Qed.

Lemma LB_free_char : forall W aw LB m mo p A n, aw_holds_w W aw LB m mo -> In (HB p A n) (w_LBa W) ->
  let T' := List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W) in
  forall v, In v (LB_free LB A n) <->
       (exists b, (In b (lb_remove p (w_LBa W)) /\ ~ In b (w_FA W)) /\ v = user_iv b)
    \/ (exists b, In b T' /\ v = twin_iv b)
    \/ (exists b, ((In b (lb_remove p (w_LBa W)) /\ ~ In b (w_FA W)) /\ is_fake b) /\ v = fsh_iv b).
Proof.
  intros W aw LB m mo p A n HW HP T'.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A n)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A n b AH HP)).
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A n).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A n)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  destruct (heap_block_facts _ _ _ _ _ (HB p A n) AH HP ltac:(exists p; reflexivity)) as (NP & BRP & _). cbn [ab_addr ab_size] in NP, BRP.
  destruct (twin_band _ _ BRP NP) as (TP1 & TP2 & TP3 & _). pose proof BRP as (BKP & _). destruct (user_app_band _ _ BKP ltac:(ulia)) as [BP1 BP2].
  assert (SAMESH : forall b, In b (w_LBa W) -> shad (ab_addr b) = shad A -> b = HB p A n).
  { intros b Hb E. apply (shadow_iv_inj _ _ _ _ _ b (HB p A n) AH Hb HP). exact E. }
  intros v. rewrite LB_free_In. split.
  - intros (Hv & N1 & N2). destruct (LB_cases W aw LB m mo v HW Hv) as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + left. exists b. split; [| reflexivity]. split; [| exact NF]. apply RM. split; [exact Hb|]. intros ->. apply N1. reflexivity.
    + right. left. exists b. split; [| reflexivity]. apply INT'. split; [exact Hb|]. intros ->. apply N2. reflexivity.
    + right. right. exists b. split; [| reflexivity]. split; [split; [exact (lb_remove_fake p _ b Hb HF)| exact NF]| exact HF].
  - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + apply RM in Hb as [Hb NE]. split; [apply HLB; left; exists b; split; [split; assumption| reflexivity]|].
      destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (NPb & B1 & B2 & _). split.
      * intros X. unfold user_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact Hb| rewrite X1; reflexivity].
      * intros X. unfold user_iv in X. injection X as X1 _. ulia.
    + apply INT' in Hb as [Hb NE]. split; [apply HLB; right; left; exists b; split; [exact Hb| reflexivity]|].
      destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & T3). split.
      * intros X. unfold twin_iv in X. injection X as X1 _. ulia.
      * intros X. unfold twin_iv in X. injection X as X1 _. apply NE. apply SAMESH; [exact (proj1 (HT b Hb))| exact X1].
    + assert (HbL : In b (w_LBa W)) by (apply RM in Hb; tauto).
      split; [apply HLB; right; right; exists b; split; [split; [split; assumption| exact HF]| reflexivity]|].
      destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj HbL NF) HF)) as (T1 & T2 & T3 & _). split.
      * intros X. unfold fsh_iv in X. injection X as X1 _. ulia.
      * intros X. unfold fsh_iv in X. injection X as X1 _. pose proof (SAMESH b HbL X1) as ->. exact (heap_not_fake (HB p A n) (ex_intro _ p eq_refl) HF).
Qed.

Lemma aw_real_realloc : forall aw aw' LB m mo W RNG' st' p A nold q UB n m' mo' sp,
  aw_realW aw LB m mo W -> In (HB p A nold) (w_LBa W) ->
  AHEAP AI (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) m' -> ACCT aw' (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) mo' ->
  aheap_pres (aci AI) (lb_remove p (w_LBa W)) sp m m' ->
  twins_pres (lb_remove p (w_LBa W)) m m' -> ablock_shadow m' UB n ->
  let T' := List.filter (fun x => if ablock_eq_dec x (HB p A nold) then false else true) (w_T W) in
  let W1 := mkWit (w_L W) RNG' st' (HB q UB n :: lb_remove p (w_LBa W)) T' (w_FA W) m' (w_zc W) in
  aw_realW aw' ((UB, n) :: LB_free LB A nold) m' mo' W1 /\ vis W1 (HB q UB n) /\ ~ In (HB q UB n) T'
  /\ user_band UB /\ (forall a, in_iv (UB, n) a -> ~ in_user (LB_free LB A nold) a)
  /\ (forall a, in_iv (shad UB, shlen (n + 7)) a -> ~ in_user (LB_free LB A nold) a).
Proof.
  intros aw aw' LB m mo W RNG' st' p A nold q UB n m' mo' sp [HW EM] HP AH' AC' PRES TW PATN T' W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  assert (RM : forall b, In b (lb_remove p (w_LBa W)) <-> (In b (w_LBa W) /\ b <> HB p A nold)) by (intros b; exact (lb_remove_In _ _ _ _ _ p A nold b AH HP)).
  assert (INT' : forall x, In x T' <-> In x (w_T W) /\ x <> HB p A nold).
  { intros x. unfold T'. rewrite filter_In. destruct (ablock_eq_dec x (HB p A nold)); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  pose proof (LB_free_char W aw LB m mo p A nold HW HP) as CHAR. cbv zeta in CHAR. fold T' in CHAR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  destruct (heap_block_facts _ _ _ _ _ (HB q UB n) AH' ltac:(left; reflexivity) ltac:(exists q; reflexivity)) as (NN & BRN & _). cbn [ab_addr ab_size] in NN, BRN.
  destruct (twin_band _ _ BRN NN) as (TN1 & TN2 & TN3 & _). pose proof BRN as (BKN & _ & HIN & ALN).
  destruct (user_app_band _ _ BKN ltac:(ulia)) as [BN1 BN2].
  assert (DISJ : forall b, In b (lb_remove p (w_LBa W)) -> UB + n <= ab_addr b \/ ab_addr b + ab_size b <= UB).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB q UB n) b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  assert (NT : ~ In (HB q UB n) T').
  { intros X. apply INT' in X as [X NE]. apply NIN. apply RM. split; [exact (proj1 (HT _ X))| exact NE]. }
  assert (NFA : ~ In (HB q UB n) (w_FA W)) by (intros X; exact (heap_not_fake (HB q UB n) (ex_intro _ q eq_refl) (proj2 (HFA _ X)))).
  assert (HW1 : aw_holds_w W1 aw' ((UB, n) :: LB_free LB A nold) m' mo').
  { unfold aw_holds_w, W1. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
    split; [exact AH'|].
    split. { intros b Hb. apply INT' in Hb as [Hb NE]. destruct (HT b Hb) as [H1 H2]. split; [right; apply RM; split; assumption| exact H2]. }
    split; [apply NoDup_filter; exact ND|].
    split. { intros b Hb. destruct (HFA b Hb) as [H1 H2]. split; [right; exact (lb_remove_fake p _ b H1 H2)| exact H2]. }
    split; [exact NDF|]. split.
    { intros v. cbn [In]. rewrite (CHAR v). unfold vis, visf. cbn [w_LBa w_FA]. split.
      - intros [<-|[(b & [Hb NF] & ->)|[H|(b & [[Hb NF] HF] & ->)]]].
        + left. exists (HB q UB n). split; [split; [left; reflexivity| exact NFA]| reflexivity].
        + left. exists b. split; [split; [right; exact Hb| exact NF]| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [split; [right; exact Hb| exact NF]| exact HF]| reflexivity].
      - intros [(b & [[<-|Hb] NF] & ->)|[H|(b & [[[<-|Hb] NF] HF] & ->)]].
        + left. reflexivity.
        + right. left. exists b. split; [split; assumption| reflexivity].
        + right. right. left. exact H.
        + exfalso. exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) HF).
        + right. right. right. exists b. split; [split; [split; assumption| exact HF]| reflexivity]. }
    split; [intros a _ _; reflexivity|].
    split.
    { intros a Ha. apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT). apply INT' in HbT as [HbT NE].
      destruct (HT b HbT) as [HbL HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
      unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
      pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' ltac:(right; apply RM; split; assumption) HbH (proj1 G) (proj2 G)) as P.
      replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P. }
    split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [exfalso; exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) FK)| exact (CLS b (proj1 (proj1 (RM b) Hb)) FK)]. }
    split.
    2:{
        intros b [[<-|HbR] NFAb] HHb NTb; [exact PATN|]. pose proof (proj1 (RM b) HbR) as [HbL NEb].
        apply (twin_keep _ _ _ _ m m' (lb_remove p (w_LBa W)) b AH' ltac:(right; exact HbR) HHb TW HbR).
        intros g G0 G1. apply (INC b (conj HbL NFAb) HHb); [| exact G0| exact G1].
        intros X. apply NTb. apply INT'. split; [exact X| exact NEb]. }
    intros b [[[<-|HbR] NFAb] FKb]; [exfalso; exact (heap_not_fake (HB q UB n) ltac:(exists q; reflexivity) FKb)|].
    apply RM in HbR as [HbL _].
    assert (Vb : visf W b) by (split; [split; assumption| exact FKb]).
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| exact Vb]. intros b0 x [[Hb0 _] FK0] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH Hb0) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block (lb_remove p (w_LBa W)) sp m m' b0 x PRES (lb_remove_fake p _ b0 Hb0 FK0)); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [left; reflexivity| exact NFA]|]. split; [exact NT|].
  split; [unfold user_band; ulia|]. split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b Hb). ulia.
    + apply INT' in Hb as [Hb _]. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + apply RM in Hb as [Hb _]. destruct (LB_fsh_facts W aw LB m mo b HW (conj (conj Hb NF) HF)) as (T1 & T2 & _). ulia.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + apply RM in Hb as [Hb _]. destruct (LB_user_facts W aw LB m mo b HW (conj Hb NF)) as (_ & B1 & _). ulia.
    + apply INT' in Hb as [Hb NE]. destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj UB n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b ltac:(apply RM; split; assumption)) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha Hva).
    + pose proof Hb as HbR. apply RM in Hb as [Hb _]. destruct (LB_shadow_hull W aw LB m mo b HW (or_intror (conj (conj Hb NF) HF))) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj UB n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b HbR) ltac:(clear -ALN; Z.div_mod_to_equations; ulia) H4 Ha ltac:(ulia)).
Qed.

Lemma twin_same : forall L RNG st LBa RNG' st' LBa' (m m' : amem) LBt b g,
  AHEAP AI L RNG st LBa m -> AHEAP AI L RNG' st' LBa' m' -> In b LBa -> In b LBa' -> is_heap b -> twins_pres LBt m m' -> In b LBt ->
  0 <= g -> 8 * g < ab_size b -> m' (wa (shad (ab_addr b) + g)) = m (wa (shad (ab_addr b) + g)).
Proof.
  intros L RNG st LBa RNG' st' LBa' m m' LBt b g AH AH' Hb Hb' HH TW HbT G0 G1.
  destruct (is_primary (ab_size b)) eqn:PRIM.
  - destruct b as [[p|c] A n]; [| destruct HH as [q Hq]; discriminate]. cbn [ab_addr ab_size] in *.
    apply (TW p A n HbT PRIM g). unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia.
  - rewrite (twin_bytes_sec _ _ _ _ _ b g AH Hb HH PRIM G0 G1), (twin_bytes_sec _ _ _ _ _ b g AH' Hb' HH PRIM G0 G1). reflexivity.
Qed.

Lemma aw_real_stable : forall aw LB m mo W RNG' st' LBa' m' LBp LBk sp LBt,
  twins_pres LBt m m' -> (forall b, In b (w_LBa W) -> In b LBa' -> In (twin_iv b) LBk -> In b LBt) ->
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' LBa' m' -> aheap_pres (aci AI) LBp sp m m' ->
  (forall v, In v LBk -> user_band (fst v) -> 0 < snd v -> exists b, In b LBp /\ v = user_iv b) ->
  (forall v, In v LBk -> ~ user_band (fst v) ->
        (exists b, In b (w_LBa W) /\ In b LBa' /\ is_heap b /\ v = twin_iv b)
     \/ (exists b, In b (w_LBa W) /\ In b LBp /\ is_fake b /\ v = fsh_iv b)) ->
  forall a, 0 <= a < 2 ^ 64 -> (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a -> m' (wa a) = m (wa a).
Proof.
  intros aw LB m mo W RNG' st' LBa' m' LBp LBk sp LBt TW TWIN [HW EM] AH' PRES KU KT a Ha ST.
  pose proof HW as (AH & _). rewrite EM in AH.
  assert (CL : aclient_addr (aci AI) LBp sp a -> m' (wa a) = m (wa a)) by (intros C; exact (proj1 (PRES a Ha C))).
  destruct ST as [S|[S|S]]; [apply CL; left; exact S| apply CL; right; left; exact S|].
  apply in_ivs_In in S as (v & Hv & Hin).
  destruct (Z_lt_dec (fst v) 0x7fff8000) as [LT|GE]; [| destruct (Z_le_dec 0x10007fff8000 (fst v)) as [GE2|LT2]].
  - destruct (KU v Hv ltac:(left; exact LT) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL. right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
  - destruct (KU v Hv ltac:(right; exact GE2) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL. right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
  - destruct (KT v Hv ltac:(unfold user_band; ulia)) as [(b & Hb & Hb' & HH & ->)|(b & Hb & HbP & HF & ->)].
    + destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (Nb & BRb & _).
      destruct (twin_band _ _ BRb Nb) as (T1 & T2 & T3 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
      { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. clear - Hin Nb. Z.div_mod_to_equations. ulia. }
      replace a with (shad (ab_addr b) + (a - shad (ab_addr b))) by ulia.
      exact (twin_same _ _ _ _ _ _ _ m m' LBt b (a - shad (ab_addr b)) AH AH' Hb Hb' HH TW (TWIN b Hb Hb' Hv) (proj1 G) (proj2 G)).
    +
      destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
      destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (F1 & F2 & F3 & E1 & E2).
      unfold in_iv, fsh_iv in Hin. cbn [fst snd] in Hin.
      apply CL. right; right; right. exists (8 * (a - ASHOFF)). split.
      * right. right. destruct b as [[q|c] F k]; [destruct HF as [d HF]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size] in *. split; [exact HbP| ulia].
      * unfold shad. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by ulia. ulia.
Qed.

Lemma aw_real_stable_x : forall aw LB m mo W RNG' st' LBa' m' LBp LBk sp (X : Z -> Prop) LBt,
  twins_pres LBt m m' -> (forall b, In b (w_LBa W) -> In b LBa' -> In (twin_iv b) LBk -> In b LBt) ->
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' LBa' m' ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBp sp a -> ~ X a -> m' (wa a) = m (wa a)) ->
  (forall a, X a -> shad ATOP <= a < shad (2 ^ 47)) -> ATOP <= sp -> (forall v, In v LBk -> In v LB) ->
  (forall v, In v LBk -> user_band (fst v) -> 0 < snd v -> exists b, In b LBp /\ v = user_iv b) ->
  (forall v, In v LBk -> ~ user_band (fst v) ->
        (exists b, In b (w_LBa W) /\ In b LBa' /\ is_heap b /\ v = twin_iv b)
     \/ (exists b, In b (w_LBa W) /\ In b LBp /\ is_fake b /\ v = fsh_iv b)) ->
  forall a, 0 <= a < 2 ^ 64 -> (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a -> m' (wa a) = m (wa a).
Proof.
  intros aw LB m mo W RNG' st' LBa' m' LBp LBk sp X LBt TW TWIN [HW EM] AH' PRES XB SPA SUB KU KT a Ha ST.
  pose proof HW as (AH & _). rewrite EM in AH. pose proof atop_range as AR.
  assert (XZ : X a -> 0x7fff8000 + 0x7fff7f800000 / 8 <= a < 0x10007fff8000).
  { intros Xa. apply XB in Xa. unfold shad, ASHOFF in Xa. rewrite !Z.shiftr_div_pow2 in Xa by lia. change (2^3) with 8 in Xa.
    clear - Xa AR. Z.div_mod_to_equations. lia. }
  assert (CL : aclient_addr (aci AI) LBp sp a -> ~ X a -> m' (wa a) = m (wa a)) by (intros C NX; exact (PRES a Ha C NX)).
  destruct ST as [S|[S|S]].
  - apply CL; [left; exact S|]. intros Xa. apply XZ in Xa. clear - Xa S SPA AR. lia.
  - apply CL; [right; left; exact S|]. intros Xa. apply XZ in Xa. destruct S as (r & Hr & Hin).
    pose proof (AI_aci_img AI r Hr) as HI. unfold AIMG_HI in HI. clear - Xa Hin HI. lia.
  - apply in_ivs_In in S as (v & Hv & Hin).
    destruct (Z_lt_dec (fst v) 0x7fff8000) as [LT|GE]; [| destruct (Z_le_dec 0x10007fff8000 (fst v)) as [GE2|LT2]].
    + destruct (KU v Hv ltac:(left; exact LT) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL.
      * right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
      * intros Xa. apply XZ in Xa. unfold in_iv in Hin.

        destruct (LB_cases W aw LB m mo _ HW (SUB _ Hv)) as [(b0 & Vb & E)|[(b0 & Hb0 & E)|(b0 & Vb & E)]]; rewrite E in Hin, LT.
        -- destruct (LB_user_facts W aw LB m mo b0 HW Vb) as (_ & BD & _). cbn [fst snd user_iv] in Hin, LT. clear - Xa Hin LT BD. ulia.
        -- destruct (LB_twin_facts W aw LB m mo b0 HW Hb0) as (T1 & _). cbn [fst twin_iv] in LT. clear - LT T1. lia.
        -- destruct (LB_fsh_facts W aw LB m mo b0 HW Vb) as (T1 & _). cbn [fst fsh_iv] in LT. clear - LT T1. lia.
    + destruct (KU v Hv ltac:(right; exact GE2) ltac:(unfold in_iv in Hin; ulia)) as (b & Hb & ->). apply CL.
      * right; right; left. exists b. split; [exact Hb| unfold in_iv, user_iv in Hin; cbn [fst snd] in Hin; ulia].
      * intros Xa. apply XZ in Xa. unfold in_iv in Hin. clear - Xa Hin GE2. lia.
    + destruct (KT v Hv ltac:(unfold user_band; ulia)) as [(b & Hb & Hb' & HH & ->)|(b & Hb & HbP & HF & ->)].
      * destruct (heap_block_facts _ _ _ _ _ b AH Hb HH) as (Nb & BRb & _).
        destruct (twin_band _ _ BRb Nb) as (T1 & T2 & T3 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
        assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
        { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. clear - Hin Nb. Z.div_mod_to_equations. ulia. }
        replace a with (shad (ab_addr b) + (a - shad (ab_addr b))) by ulia.
        exact (twin_same _ _ _ _ _ _ _ m m' LBt b (a - shad (ab_addr b)) AH AH' Hb Hb' HH TW (TWIN b Hb Hb' Hv) (proj1 G) (proj2 G)).
      * destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _).
        destruct (fsh_band _ _ BK HI A8 N8 ltac:(ulia)) as (F1 & F2 & F3 & E1 & E2).
        unfold in_iv, fsh_iv in Hin. cbn [fst snd] in Hin.
        apply CL.
        -- right; right; right. exists (8 * (a - ASHOFF)). split.
           ++ right. right. destruct b as [[q|c] F k]; [destruct HF as [d HF]; discriminate|]. exists c, F, k. cbn [ab_addr ab_size] in *. split; [exact HbP| ulia].
           ++ unfold shad. rewrite Z.shiftr_div_pow2 by ulia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by ulia. ulia.
        -- intros Xa. apply XB in Xa. unfold shad, ASHOFF in Xa, E1, Hin. rewrite !Z.shiftr_div_pow2 in Xa by lia. change (2^3) with 8 in Xa.
           clear - Xa Hin E1 E2 HI. unfold ASHOFF in *. Z.div_mod_to_equations. ulia.
Qed.

Lemma freed_apart : forall aw LB m mo W A n a,
  aw_realW aw LB m mo W -> In (A, n) LB -> In (shad A, shlen (n + 7)) LB ->
  in_iv (A, n) a \/ in_iv (shad A, shlen (n + 7)) a -> ~ in_user (LB_free LB A n) a.
Proof.
  intros aw LB m mo W A n a AR H0 HT Ha U. pose proof (aw_real_holds _ _ _ _ _ AR) as AWH. destruct AR as [HW _].
  apply in_ivs_In in U as (b' & Hb' & Hin). apply LB_free_In in Hb' as (Hb' & N1 & N2). destruct b' as [A' n'].
  destruct Ha as [Ha|Ha].
  - apply (aw_blocks_disj_asan aw LB m mo (A, n) (A', n') a AWH H0 Hb'); [| exact Ha| exact Hin].
    cbn [fst]. intros <-. apply N1. f_equal. exact (LB_same_addr W aw LB m mo A n' n HW Hb' H0).
  - apply (aw_blocks_disj_asan aw LB m mo (shad A, shlen (n + 7)) (A', n') a AWH HT Hb'); [| exact Ha| exact Hin].
    cbn [fst]. intros <-. apply N2. f_equal. exact (LB_same_addr W aw LB m mo (shad A) n' _ HW Hb' HT).
Qed.

Variable Cw : client_world.
Definition K_FRAMEz : Z := 7.
Definition K_FTWINz : Z := 8.
Definition K_TWINz : Z := 9.

Definition ZC_BASE : Z := 2^47.
Definition ZC_BAND : Z := 2^47 + 2^46.

Definition PRIST_BASE : Z := 2^47 + 2^46.
Definition prist_win : window := Win PRIST_BASE 0 K_STACK.
Definition aprist (st : astate) : Prop := APristLaw.TwinB.aprist st.

Lemma prist_tied : aw_tied prist_win.
Proof. left. split; [reflexivity|]. unfold prist_win, PRIST_BASE, AW_BAND. cbn [w_lo]. lia. Qed.
Definition zc_win (zc : Z) : window := Win (ZC_BASE + zc) 0 K_STACK.
Definition c24inv (W : wit) (ws : list window) : Prop :=
  forall b, vis W b -> is_heap b -> c24 (ab_size b) ->
    exists w, In w ws /\ heap_kind w /\ 0 < w_len w /\ in_iv (user_iv b) (w_lo w).
Definition ties (W : wit) (ws : list window) : Prop :=
     (forall b, In b (w_T W) -> In (Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) ws)
  /\ (forall w, In w ws -> w_kind w = K_TWINz -> exists b, In b (w_T W) /\ w_iv w = twin_iv b)
  /\ (forall b, visf W b -> In (Win (ab_addr b) (ab_size b - 8) K_FRAMEz) ws /\ In (Win (shad (ab_addr b)) (shlen (ab_size b)) K_FTWINz) ws)
  /\ (forall w, In w ws -> w_kind w = K_FRAMEz -> exists b, visf W b /\ w_iv w = user_iv b)
  /\ (forall w, In w ws -> w_kind w = K_FTWINz -> exists b, visf W b /\ w_iv w = fsh_iv b)

  /\ (forall w, In w ws -> w_kind w = K_STACK -> w_len w = 0 -> w_lo w < ZC_BAND -> w = zc_win (w_zc W)) /\ In (zc_win (w_zc W)) ws

  /\ (forall w, In w ws -> w_kind w = K_STACK -> w_lo w < ZC_BASE -> w_lo w = ATOP + 4096)

  /\ c24inv W ws /\ ghost_apart ws

  /\ (In prist_win ws -> aprist (w_st W)).
Lemma window_eq_dec : forall x y : window, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma ghost_apart_sub : forall ws ws', ghost_apart ws -> (forall w, In w ws' -> In w ws) -> ghost_apart ws'.
Proof. intros ws ws' GA I w w' Hw Hw' K K' a Ha. exact (GA w w' (I w Hw) (I w' Hw') K K' a Ha). Qed.

Lemma ghost_apart_new_ghosts : forall ws ws' LB ceil, windows_wf ws LB ceil -> ghost_apart ws ->
  (forall w, In w ws' -> In w ws \/ (w_kind w <> K_BLOCK /\ (K_GHOST <= w_kind w -> forall a, in_iv (w_iv w) a -> ~ in_user LB a))) ->
  ghost_apart ws'.
Proof.
  intros ws ws' LB ceil WF GA NEW w w' Hw Hw' K K' a Ha Ha'.
  destruct (NEW w' Hw') as [Hw0'|[NB _]]; [| exact (NB K')].
  destruct (NEW w Hw) as [Hw0|[_ FR]]; [exact (GA w w' Hw0 Hw0' K K' a Ha Ha')|].
  apply (FR K a Ha). pose proof (proj1 (Forall_forall _ _) WF w' Hw0') as (_ & _ & _ & [[KS _]|[[_ B]|[KS _]]]);
    [rewrite K' in KS; unfold K_BLOCK, K_STACK in KS; lia| | rewrite K' in KS; unfold K_BLOCK, K_SUB in KS; lia].
  unfold in_user. apply in_ivs_In. exists (w_iv w'). split; [exact B| exact Ha'].
Qed.

Lemma ghost_apart_new_block : forall ws LB ceil A n, windows_wf ws LB ceil -> ghost_apart ws ->
  (forall a, in_iv (A, n) a -> ~ in_user LB a) -> ghost_apart (ws ++ [Win A n K_BLOCK]).
Proof.
  intros ws LB ceil A n WF GA FR w w' Hw Hw' K K' a Ha Ha'.
  apply in_app_or in Hw as [Hw|[<-|[]]]; [| cbn [w_kind] in K; unfold K_BLOCK, K_GHOST in K; lia].
  apply in_app_or in Hw' as [Hw'|[<-|[]]]; [exact (GA w w' Hw Hw' K K' a Ha Ha')|].
  apply (FR a Ha'). pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & [[KS _]|[[KB _]|[_ (b & Hb & SUB)]]]);
    [rewrite KS in K; unfold K_STACK, K_GHOST in K; lia| rewrite KB in K; unfold K_BLOCK, K_GHOST in K; lia|].
  unfold in_user. apply in_ivs_In. exists b. split; [exact Hb| exact (SUB a Ha)].
Qed.

Lemma ties_set_ms : forall W ms ws, ties (set_ms W ms) ws <-> ties W ws.
Proof. intros W ms ws. unfold ties, c24inv, set_ms, visf, vis. cbn [w_T w_LBa w_FA w_zc w_st]. tauto. Qed.
Lemma ties_ext : forall W W' ws, w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W -> ties W ws ->
  (forall b, is_heap b -> vis W' b -> vis W b) -> (aprist (w_st W) -> aprist (w_st W')) -> ties W' ws.
Proof.
  intros W W' ws ET EV EZ (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HV PS. unfold ties. rewrite ET, EZ.
  split; [exact T1|]. split; [exact T2|]. split; [intros b Hb; apply T3; apply EV; exact Hb|].
  split; [intros w Hw K; destruct (T4 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [intros w Hw K; destruct (T5 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [exact T6| split; [exact T7| split; [exact T8|]]].
  split; [intros b Vb HH CC; exact (C24 b (HV b HH Vb) HH CC)| split; [exact GA| intros IP; exact (PS (PR IP))]].
Qed.

Lemma ties_burn : forall W W' ws ws' c,
  ties W ws -> w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W - c -> c <= w_zc W ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win (w_zc W)) \/ w = zc_win (w_zc W - c)) ->
  (forall b, is_heap b -> vis W' b -> vis W b) ->
  ZC_BASE + (w_zc W - c) < ZC_BAND -> (aprist (w_st W) -> aprist (w_st W')) ->
  ties W' ws'.
Proof.
  intros W W' ws ws' c (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EV EZ CZ WS HV ZB PS. unfold ties. rewrite ET, EZ.
  assert (KEEP : forall w, In w ws -> w_kind w <> K_STACK -> In w ws').
  { intros w Hw NK. apply WS. left. split; [exact Hw|]. intros ->. apply NK. reflexivity. }
  assert (OLD : forall w, In w ws' -> w_kind w <> K_STACK -> In w ws).
  { intros w Hw NK. apply WS in Hw as [[Hw _]| ->]; [exact Hw| exfalso; apply NK; reflexivity]. }
  split. { intros b Hb. apply KEEP; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_STACK; ulia]. }
  split. { intros w Hw K. apply T2; [apply OLD; [exact Hw| rewrite K; unfold K_TWINz, K_STACK; ulia]| exact K]. }
  split. { intros b Vb. apply EV in Vb. destruct (T3 b Vb) as [X Y]. split; apply KEEP; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_STACK; ulia. }
  split. { intros w Hw K. destruct (T4 w (OLD w Hw ltac:(rewrite K; unfold K_FRAMEz, K_STACK; ulia)) K) as (b & Vb & E). exists b. split; [apply EV; exact Vb| exact E]. }
  split. { intros w Hw K. destruct (T5 w (OLD w Hw ltac:(rewrite K; unfold K_FTWINz, K_STACK; ulia)) K) as (b & Vb & E). exists b. split; [apply EV; exact Vb| exact E]. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [[Hw NE]| ->]; [exfalso; exact (NE (T6 w Hw K Z0 B0))| reflexivity]. }
  split; [apply WS; right; reflexivity|].
  split. { intros w Hw K P. apply WS in Hw as [[Hw _]| ->]; [exact (T8 w Hw K P)| unfold zc_win in P; cbn [w_lo] in P; lia]. }
  split.
  - intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto].
    apply KEEP; [exact Hw|]. unfold heap_kind, K_BLOCK, K_STACK in *. lia.
  - split.
    + intros w w' Hw Hw' K K' a Ha. apply (GA w w'); [apply OLD; [exact Hw| unfold K_GHOST, K_STACK in *; lia]| apply OLD; [exact Hw'| rewrite K'; unfold K_BLOCK, K_STACK; lia]| exact K| exact K'| exact Ha].
    + intros IP. apply PS, PR. apply WS in IP as [[IP _]|E]; [exact IP| exfalso].
      unfold prist_win, zc_win, PRIST_BASE, ZC_BAND in *. injection E as E. lia.
Qed.

Lemma ties_grow_heap : forall W ws L' RNG' st' ms' b,
  ties W ws -> is_heap b -> 0 < ab_size b ->
  ghost_apart ((ws ++ [Win (ab_addr b) (ab_size b) K_BLOCK]) ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]) ->
  (In prist_win ws -> aprist st') ->
  ties (mkWit L' RNG' st' (b :: w_LBa W) (b :: w_T W) (w_FA W) ms' (w_zc W))
       ((ws ++ [Win (ab_addr b) (ab_size b) K_BLOCK]) ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]).
Proof.
  intros W ws L' RNG' st' ms' b (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HH POS GAN PS.
  set (WB := Win (ab_addr b) (ab_size b) K_BLOCK). set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz).
  assert (INC : forall w, In w ws -> In w ((ws ++ [WB]) ++ [WT])) by (intros w Hw; apply in_or_app; left; apply in_or_app; left; exact Hw).
  assert (CASES : forall w, In w ((ws ++ [WB]) ++ [WT]) -> In w ws \/ w = WB \/ w = WT).
  { intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [| right; right; reflexivity]. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right; left; reflexivity]. }
  assert (VF : forall b', visf (mkWit L' RNG' st' (b :: w_LBa W) (b :: w_T W) (w_FA W) ms' (w_zc W)) b' <-> visf W b').
  { intros b'. unfold visf, vis. cbn [w_LBa w_FA In]. split.
    - intros [[[<-|Hb] NF] FK]; [exfalso; exact (heap_not_fake _ HH FK)| auto].
    - intros [[Hb NF] FK]. auto. }
  unfold ties. cbn [w_T w_zc].
  split. { intros b' [<-|Hb']; [apply in_or_app; right; left; reflexivity| exact (INC _ (T1 b' Hb'))]. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [right; exact Hb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_TWINz in K. ulia.
           - exists b. split; [left; reflexivity| reflexivity]. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y]. split; apply INC; assumption. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_FRAMEz in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FRAMEz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_FTWINz in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FTWINz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0|[->| ->]].
           - exact (T6 w Hw0 K).
           - exfalso. cbn [w_kind WB] in K. unfold K_BLOCK, K_STACK in K. ulia.
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [exact (INC _ T7)|].
  split. { intros w Hw K P. destruct (CASES w Hw) as [Hw0|[->| ->]]; [exact (T8 w Hw0 K P)| |]; exfalso; cbn [w_kind WB WT] in K; unfold K_BLOCK, K_TWINz, K_STACK in K; ulia. }
  split; [| split; [exact GAN| cbn [w_st]; intros IP; destruct (CASES _ IP) as [IP0|[E|E]]; [exact (PS IP0)| |]; exfalso; unfold prist_win, WB, WT in E; injection E as _ _ E; unfold K_STACK, K_BLOCK, K_TWINz in E; ulia]].
  intros b' [[<-|Hb'] NF] HH' CC.
  - exists WB. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    split; [unfold heap_kind, WB; cbn [w_kind]; unfold K_BLOCK, K_GHOST; lia|]. split; [exact POS|].
    unfold in_iv, user_iv, WB. cbn [w_lo fst snd]. rewrite (usz_heap b HH). lia.
  - destruct (C24 b' (conj Hb' NF) HH' CC) as (w & Hw & X). exists w. split; [exact (INC _ Hw)| exact X].
Qed.

Lemma ties_free : forall W aw LB m mo ws ws1 ws2 p A n RNG' st' ms',
  aw_holds_w W aw LB m mo -> ties W ws -> In (HB p A n) (w_T W) ->
  (forall w, In w ws1 <-> In w ws /\ w <> Win A n K_BLOCK) ->
  (forall w, In w ws2 <-> In w ws1 /\ w <> Win (shad A) (shlen (n + 7)) K_TWINz) ->
  (In prist_win ws -> aprist st') ->
  ties (mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x (HB p A n) then false else true) (w_T W))
              (w_FA W) ms' (w_zc W)) ws2.
Proof.
  intros W aw LB m mo ws ws1 ws2 p A n RNG' st' ms' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HbT IN1 IN2 PS.
  pose proof HW as (AH & HT & _ & HFA & _). destruct (HT _ HbT) as [HbL HbH].
  set (b := HB p A n) in *. set (WB := Win A n K_BLOCK) in *. set (WT := Win (shad A) (shlen (n + 7)) K_TWINz) in *.
  assert (INT' : forall x, In x (List.filter (fun x => if ablock_eq_dec x b then false else true) (w_T W)) <-> In x (w_T W) /\ x <> b).
  { intros x. rewrite filter_In. destruct (ablock_eq_dec x b); split; intros [H1 H2]; try discriminate; try contradiction; auto. }
  assert (KEEP : forall w, In w ws -> w <> WB -> w <> WT -> In w ws2) by (intros w Hw N1 N2; apply IN2; split; [apply IN1; split; assumption| exact N2]).
  assert (OLD : forall w, In w ws2 -> In w ws /\ w <> WT) by (intros w Hw; apply IN2 in Hw as [Hw N2]; apply IN1 in Hw as [Hw _]; auto).
  assert (VF : forall b', visf (mkWit (w_L W) RNG' st' (lb_remove p (w_LBa W)) (List.filter (fun x => if ablock_eq_dec x b then false else true) (w_T W))
                                      (w_FA W) ms' (w_zc W)) b' <-> visf W b').
  { intros b'. unfold visf, vis. cbn [w_LBa w_FA]. rewrite (lb_remove_In _ _ _ _ _ p A n b' AH HbL). fold b. split.
    - intros [[[Hb' _] NF] FK]. auto.
    - intros [[Hb' NF] FK]. split; [split; [split; [exact Hb'| intros ->; exact (heap_not_fake b HbH FK)]| exact NF]| exact FK]. }
  unfold ties. cbn [w_T w_zc].
  split. { intros b' Hb'. apply INT' in Hb' as [Hb' NE]. apply KEEP; [exact (T1 b' Hb')| unfold WB; intros X; injection X as _ _ X; unfold K_TWINz, K_BLOCK in X; ulia|].
           unfold WT. intros X. injection X as X1 X2. apply NE. apply (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 (HT b' Hb')) HbL). unfold b. cbn [ab_addr]. exact X1. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 NWT]. destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [| exact E]. apply INT'. split; [exact Hb'|].
           intros ->. apply NWT. destruct w as [wl wn wk]. unfold w_iv, twin_iv, b in E. cbn [w_lo w_len w_kind ab_addr ab_size] in E, K. injection E as -> ->. subst wk. reflexivity. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y].
           split; apply KEEP; try assumption; unfold WB, WT; intros Z; injection Z as _ _ Z; unfold K_FRAMEz, K_FTWINz, K_TWINz, K_BLOCK in Z; ulia. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K Z0 B0. destruct (OLD w Hw) as [Hw0 _]. exact (T6 w Hw0 K Z0 B0). }
  split; [apply KEEP; [exact T7| |]; unfold zc_win, WB, WT; intros Z; injection Z as _ _ Z; unfold K_STACK, K_BLOCK, K_TWINz in Z; ulia|].
  split. { intros w Hw K P. destruct (OLD w Hw) as [Hw0 _]. exact (T8 w Hw0 K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (OLD w Hw))]| cbn [w_st]; intros IP; exact (PS (proj1 (OLD _ IP)))]].
  intros b' [Hb' NF'] HH' CC. cbn [w_LBa w_FA] in Hb', NF'. apply (lb_remove_In _ _ _ _ _ p A n b' AH HbL) in Hb' as [Hb' NEb]. fold b in NEb.
  destruct (C24 b' (conj Hb' NF') HH' CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto]. apply KEEP; [exact Hw| |].
  - intros ->. unfold WB in HI. cbn [w_lo] in HI.
    destruct (AI_blocks_disjoint AI _ _ _ _ _ b' b AH Hb' HbL NEb) as [D|D]; unfold in_iv, user_iv in HI; cbn [fst snd] in HI;
      rewrite (usz_heap b' HH') in HI; unfold b in D; cbn [ab_addr ab_size] in D;
      destruct (AI_block AI _ _ _ _ _ p A n AH HbL) as (NR & _); lia.
  - intros ->. unfold heap_kind, WT in HK. cbn [w_kind] in HK. unfold K_TWINz, K_GHOST in HK. lia.
Qed.

Lemma ties_twin_out : forall W ws b,
  ties W ws ->
  ghost_apart (ws ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]) ->
  ties (set_T W (b :: w_T W)) (ws ++ [Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz]).
Proof.
  intros W ws b (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) GAN.
  set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) in *.
  assert (INC : forall w, In w ws -> In w (ws ++ [WT])) by (intros w Hw; apply in_or_app; left; exact Hw).
  assert (CASES : forall w, In w (ws ++ [WT]) -> In w ws \/ w = WT) by (intros w Hw; apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right; reflexivity]).
  assert (VF : forall b', visf (set_T W (b :: w_T W)) b' <-> visf W b') by (intros b'; unfold visf, vis, set_T; cbn [w_LBa w_FA]; reflexivity).
  unfold ties. cbn [w_T w_zc set_T].
  split. { intros b' [<-|Hb']; [apply in_or_app; right; left; reflexivity| exact (INC _ (T1 b' Hb'))]. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [right; exact Hb'| exact E].
           - exists b. split; [left; reflexivity| reflexivity]. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y]. split; apply INC; assumption. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FRAMEz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E].
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_FTWINz in K. ulia. }
  split. { intros w Hw K. destruct (CASES w Hw) as [Hw0| ->].
           - exact (T6 w Hw0 K).
           - exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [exact (INC _ T7)|].
  split. { intros w Hw K P. destruct (CASES w Hw) as [Hw0| ->]; [exact (T8 w Hw0 K P)|]. exfalso. cbn [w_kind WT] in K. unfold K_TWINz, K_STACK in K. ulia. }
  split; [| split; [exact GAN| cbn [w_st set_T]; intros IP; destruct (CASES _ IP) as [IP0|E]; [exact (PR IP0)|]; exfalso; unfold prist_win, WT in E; injection E as _ _ E; unfold K_STACK, K_TWINz in E; ulia]].
  intros b' Vb' HH' CC. destruct (C24 b' Vb' HH' CC) as (w & Hw & X). exists w. split; [exact (INC _ Hw)| exact X].
Qed.

Lemma ties_twin_in : forall W aw LB m mo ws ws' b (m1 : amem),
  aw_holds_w W aw LB m mo -> ties W ws -> In b (w_T W) ->
  (forall w, In w ws' <-> In w ws /\ w <> Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) ->
  ties (wit_twin_in W m1 b) ws'.
Proof.
  intros W aw LB m mo ws ws' b m1 HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HbT IN2.
  pose proof HW as (AH & HT & _). destruct (HT _ HbT) as [HbL HbH].
  set (WT := Win (shad (ab_addr b)) (shlen (ab_size b + 7)) K_TWINz) in *.
  assert (KEEP : forall w, In w ws -> w <> WT -> In w ws') by (intros w Hw N2; apply IN2; split; assumption).
  assert (OLD : forall w, In w ws' -> In w ws /\ w <> WT) by (intros w Hw; apply IN2 in Hw; exact Hw).
  assert (VF : forall b', visf (wit_twin_in W m1 b) b' <-> visf W b') by (intros b'; unfold visf, vis, wit_twin_in; cbn [w_LBa w_FA]; reflexivity).
  unfold ties. cbn [w_T w_zc wit_twin_in].
  split. { intros b' Hb'. apply lb_del_In in Hb' as [Hb' NE]. apply KEEP; [exact (T1 b' Hb')|].
           unfold WT. intros X. injection X as X1 X2. apply NE. exact (shadow_iv_inj _ _ _ _ _ b' b AH (proj1 (HT b' Hb')) HbL X1). }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 NWT]. destruct (T2 w Hw0 K) as (b' & Hb' & E). exists b'. split; [| exact E]. apply lb_del_In. split; [exact Hb'|].
           intros ->. apply NWT. destruct w as [wl wn wk]. unfold w_iv, twin_iv in E. cbn [w_lo w_len w_kind] in E, K. injection E as -> ->. subst wk. reflexivity. }
  split. { intros b' Vb'. apply VF in Vb'. destruct (T3 b' Vb') as [X Y].
           split; apply KEEP; try assumption; unfold WT; intros Z; injection Z as _ _ Z; unfold K_FRAMEz, K_FTWINz, K_TWINz in Z; ulia. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T4 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K. destruct (OLD w Hw) as [Hw0 _]. destruct (T5 w Hw0 K) as (b' & Vb' & E). exists b'. split; [apply VF; exact Vb'| exact E]. }
  split. { intros w Hw K Z0 B0. destruct (OLD w Hw) as [Hw0 _]. exact (T6 w Hw0 K Z0 B0). }
  split; [apply KEEP; [exact T7|]; unfold zc_win, WT; intros Z; injection Z as _ _ Z; unfold K_STACK, K_TWINz in Z; ulia|].
  split. { intros w Hw K P. destruct (OLD w Hw) as [Hw0 _]. exact (T8 w Hw0 K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (OLD w Hw))]| cbn [w_st wit_twin_in]; intros IP; exact (PR (proj1 (OLD _ IP)))]].
  intros b' Vb' HH' CC. destruct (C24 b' Vb' HH' CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto]. apply KEEP; [exact Hw|].
  intros ->. unfold heap_kind, WT in HK. cbn [w_kind] in HK. unfold K_TWINz, K_GHOST in HK. lia.
Qed.

Lemma ties_prist : forall W ws, ties W ws -> In prist_win ws -> aprist (w_st W).
Proof. intros W ws (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR) IP. exact (PR IP). Qed.

Lemma ties_prist_del : forall W aw LB m mo ws ws',
  aw_holds_w W aw LB m mo -> ties W ws ->
  (forall w, In w ws' -> In w ws) -> (forall w, In w ws -> w <> prist_win -> In w ws') ->
  ties W ws'.
Proof.
  intros W aw LB m mo ws ws' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) SUB SUP.
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & ZC0 & ZCB & _).
  assert (KEEPK : forall w, In w ws -> w_kind w <> K_STACK -> In w ws').
  { intros w Hw NK. apply SUP; [exact Hw|]. intros ->. apply NK. reflexivity. }
  unfold ties.
  split. { intros b Hb. apply KEEPK; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_STACK; lia]. }
  split. { intros w Hw K. exact (T2 w (SUB w Hw) K). }
  split. { intros b Vb. destruct (T3 b Vb) as [X Y]. split; apply KEEPK; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_STACK; lia. }
  split. { intros w Hw K. exact (T4 w (SUB w Hw) K). }
  split. { intros w Hw K. exact (T5 w (SUB w Hw) K). }
  split. { intros w Hw K Z0 B0. exact (T6 w (SUB w Hw) K Z0 B0). }
  split. { apply SUP; [exact T7|]. unfold zc_win, prist_win, PRIST_BASE, ZC_BASE, ZTOTAL in *. intros E. injection E as E. lia. }
  split. { intros w Hw K P. exact (T8 w (SUB w Hw) K P). }
  split. { intros b Vb HH CC. destruct (C24 b Vb HH CC) as (w & Hw & HK & HL & HI). exists w. split; [| auto].
           apply SUP; [exact Hw|]. intros ->. unfold prist_win in HL. cbn [w_len] in HL. lia. }
  split; [apply (ghost_apart_sub ws); [exact GA| exact SUB]|].
  intros IP. exact (PR (SUB _ IP)).
Qed.

Hypothesis AI_prist : APristLaw.TwinB.prist_det_law (AHEAP AI).
Lemma aprist_heap : forall W aw LB m mo L RNG sta LBa,
  aw_holds_w W aw LB m mo -> AHEAP AI L RNG sta LBa m -> aprist (w_st W) -> aprist sta.
Proof.
  intros W aw LB m mo L RNG sta LBa HW AH PR. pose proof HW as (AHw & HT & _ & _ & _ & _ & SAME & _).
  apply (AI_prist (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_ms W) L RNG sta LBa m AHw AH); [| exact PR].
  intros a Ha. symmetry. apply SAME; [unfold two64, AIMG_HI in *; lia|]. intros IN.
  apply in_ivs_In in IN as (v & Hv & Hin). apply in_map_iff in Hv as (b & <- & Hb).
  destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI in Ha. lia.
Qed.

Definition aw_holdsA (aw : word) (LB : blocks) (ws : list window) (m : amem) (mo : Model) : Prop :=
  exists W, aw_holds_w W aw LB m mo /\ ties W ws.
Lemma aw_holdsA_plain : forall aw LB ws m mo, aw_holdsA aw LB ws m mo -> aw_holds_asan aw LB m mo.
Proof. intros aw LB ws m mo (W & HW & _). exists W. exact HW. Qed.

Lemma aw_frameA : forall A LB ws m m' mo, aw_holdsA A LB ws m mo ->
  (forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsA A LB ws m' mo /\ (forall a, aw_dep_asan LB m' mo a <-> aw_dep_asan LB m mo a).
Proof.
  intros A LB ws m m' mo (W & HW & TI) AG DM. split; [| intros a; reflexivity].
  destruct (aw_frame_w W A LB m m' mo HW AG DM) as [ms2 H2]. exists (set_ms W ms2). split; [exact H2| apply ties_set_ms; exact TI].
Qed.

Lemma ties_keep : forall W aw LB m mo ws ws', aw_holds_w W aw LB m mo -> ties W ws -> wins_keep LB ws ws' -> ties W ws'.
Proof.
  intros W aw LB m mo ws ws' HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) (KA & KB & KC).
  pose proof HW as (AH & HT & _ & HFA & _ & HLB & _ & _ & ZC0 & ZCB & _).
  assert (TG : forall w, K_GHOST <= w_kind w -> aw_tied w) by (intros w H; right; exact H).
  assert (OLDG : forall w, In w ws' -> K_GHOST <= w_kind w -> In w ws) by (intros w Hw K; apply (KA w (TG w K)); exact Hw).
  assert (NEWG : forall w, In w ws -> K_GHOST <= w_kind w -> In w ws') by (intros w Hw K; apply (KA w (TG w K)); exact Hw).
  unfold ties.
  split. { intros b Hb. apply NEWG; [exact (T1 b Hb)| cbn [w_kind]; unfold K_TWINz, K_GHOST; lia]. }
  split. { intros w Hw K. apply T2; [apply OLDG; [exact Hw| rewrite K; unfold K_TWINz, K_GHOST; lia]| exact K]. }
  split. { intros b Vb. destruct (T3 b Vb) as [X Y]. split; apply NEWG; try assumption; cbn [w_kind]; unfold K_FRAMEz, K_FTWINz, K_GHOST; lia. }
  split. { intros w Hw K. apply T4; [apply OLDG; [exact Hw| rewrite K; unfold K_FRAMEz, K_GHOST; lia]| exact K]. }
  split. { intros w Hw K. apply T5; [apply OLDG; [exact Hw| rewrite K; unfold K_FTWINz, K_GHOST; lia]| exact K]. }
  split. { intros w Hw K Z0 B0. apply T6; [| exact K| exact Z0| exact B0]. apply (KA w); [left; split; [exact K| unfold ZC_BAND, AW_BAND in *; lia]| exact Hw]. }
  split. { apply (KA (zc_win (w_zc W))); [| exact T7]. left. split; [reflexivity|]. unfold zc_win, ZC_BASE, AW_BAND, ZTOTAL in *. cbn [w_lo]. lia. }
  split. { intros w Hw K P. apply T8; [| exact K| exact P]. apply (KA w); [left; split; [exact K| unfold ZC_BASE, AW_BAND in *; lia]| exact Hw]. }
  split.
  -
    intros b Vb HH CC. destruct (C24 b Vb HH CC) as (w & Hw & HK & HL & HI).
    destruct (in_dec window_eq_dec w ws') as [Hin|Hnin]; [exists w; auto|].
    destruct (KB w Hw Hnin HK HL) as (o & Ho & Io & ALT).
    assert (INB : In (user_iv b) LB) by (apply HLB; left; exists b; split; [exact Vb| reflexivity]).
    assert (EO : o = user_iv b).
    { destruct (iv_eq_dec o (user_iv b)) as [E|NE]; [exact E| exfalso].
      assert (HAa : aw_holds_asan aw LB m mo) by (exists W; exact HW).
      destruct (Z.eq_dec (fst o) (fst (user_iv b))) as [EF|NF]; [| exact (aw_blocks_disj_asan aw LB m mo o (user_iv b) (w_lo w) HAa Ho INB NF Io HI)].

      destruct o as [oa on]. unfold user_iv in *. cbn [fst] in EF. subst oa.
      apply NE. f_equal. exact (LB_same_addr W aw LB m mo _ _ _ HW Ho INB). }
    subst o. destruct ALT as [NC|(w' & Hw' & HK' & HL' & HI')]; [exfalso; apply NC; unfold user_iv; cbn [snd]; rewrite (usz_heap b HH); exact CC|].
    exists w'. auto.
  - split.
    +
      intros w w' Hw Hw' K K' a Ha. destruct (in_dec window_eq_dec w' ws) as [Hin|Hnin].
      * exact (GA w w' (OLDG w Hw K) Hin K K' a Ha).
      * exact (KC w' Hw' Hnin K' w Hw K a Ha).
    +
      intros IP. apply PR. exact (proj1 (KA prist_win prist_tied) IP).
Qed.

Lemma aw_keepA : forall A LB ws ws' m mo, aw_holdsA A LB ws m mo -> wins_keep LB ws ws' -> aw_holdsA A LB ws' m mo.
Proof. intros A LB ws ws' m mo (W & HW & TI) WK. exists W. split; [exact HW| exact (ties_keep W A LB m mo ws ws' HW TI WK)]. Qed.
Lemma aw_ghost_apartA : forall A LB ws m mo, aw_holdsA A LB ws m mo -> ghost_apart ws.
Proof. intros A LB ws m mo (W & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _)). exact GA. Qed.

Definition AWA : alloc_world bsegs IMGX :=
  AW bsegs IMGX aw_holdsA aw_dep_asan aw_ceiling_asan aw_frameA aw_keepA aw_ghost_apartA
     (fun A LB ws m mo a H => aw_dep_ok_asan A LB m mo a (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b H => aw_blocks_ok_asan A LB m mo b (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b a H => aw_user_ok_asan A LB m mo b a (aw_holdsA_plain A LB ws m mo H))
     (fun A LB ws m mo b b' a H => aw_blocks_disj_asan A LB m mo b b' a (aw_holdsA_plain A LB ws m mo H))
     aw_ceiling_small_asan
     (fun A LB ws m mo b H => aw_blocks_lo_asan A LB m mo b (aw_holdsA_plain A LB ws m mo H)).

Definition heap_holdsA (dargs : list word) (m : amem) (mo : Model) : Prop := heap_holds bsegs IMGX AWA Cw dargs m mo.
Definition heap_holdsX (dargs : list word) (m : amem) (mo : Model) : Prop :=
  exists md aw ws ca LB W, decode dargs = Some (md, aw, ws, ca) /\
    aw_holds_w W aw LB m mo /\ windows_wf ws LB (ATOP + 4096) /\ cw_holds Cw md ca LB ws m /\ ties W ws.
Lemma heap_holdsA_inv : forall dargs m mo, heap_holdsA dargs m mo -> heap_holdsX dargs m mo.
Proof. intros dargs m mo (md & aw & ws & ca & LB & D & (W & HA & TI) & WF & HC). exists md, aw, ws, ca, LB, W. auto. Qed.
Lemma heap_holdsA_intro : forall dargs m mo, heap_holdsX dargs m mo -> heap_holdsA dargs m mo.
Proof. intros dargs m mo (md & aw & ws & ca & LB & W & D & HA & WF & HC & TI). exists md, aw, ws, ca, LB. split; [exact D|]. split; [exists W; auto| auto]. Qed.
Lemma heap_holdsA_plain : forall dargs m mo, heap_holdsA dargs m mo -> heap_holds bsegs IMGX AWA Cw dargs m mo.
Proof. intros dargs m mo H. exact H. Qed.

Lemma heap_frameA_v : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono bsegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsA dargs m mo -> heap_holdsA dargs m' mo.
Proof.
  intros dargs m m' mo AG WM DM HH. apply heap_holdsA_inv in HH. destruct HH as (md & aw & ws & ca & LB & W & D & HA & WF & HC & TW).
  assert (HAa : aw_holds_asan aw LB m mo) by (exists W; exact HA).
  assert (INFP : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha I Wn. apply AG; [exact Ha|]. apply (proj2 (fp_spec IMGX dargs md aw ws ca a D)). tauto. }
  assert (NOTW : forall a, 0 <= a < ATOP + 4096 ->
            (forall w, In w ws -> w_kind w <> K_STACK -> ~ in_iv (w_iv w) a) -> ~ in_ws ws a).
  { intros a Ha H X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    - unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. ulia.
    - exact (H w Hw ltac:(rewrite K; discriminate) Hin).
    - exact (H w Hw ltac:(unfold K_SUB, K_STACK in *; ulia) Hin). }
  assert (DEPEQ : forall a, 0 <= a < two64 -> aw_dep_asan LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha Hd. destruct (aw_dep_ok_asan aw LB m mo a HAa Hd) as (C1 & NU & NI).
    apply INFP; [exact Ha| exact NI|]. apply NOTW; [exact C1|].
    intros w Hw NK Hin. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
    + exact (NK K).
    + apply NU. unfold in_user. apply in_ivs_In. exists (w_iv w). auto.
    + apply NU. unfold in_user. apply in_ivs_In. exists b. auto. }
  destruct (aw_frame_w_v W aw LB m m' mo HA DEPEQ WM DM) as [ms2 HA2].
  apply heap_holdsA_intro. exists md, aw, ws, ca, LB, (set_ms W ms2). split; [exact D|]. split; [exact HA2|]. split; [exact WF|]. split; [| apply ties_set_ms; exact TW].
  apply (cw_frame Cw md ca LB ws m m' HC).
  intros a Ha U NH. apply in_ivs_In in U as (b & Hb & Hin).
  destruct (aw_blocks_ok_asan aw LB m mo b HAa Hb) as (B1 & B2 & B3 & B4 & B5).
  apply INFP; [exact Ha| exact (B5 a Hin)|]. apply NOTW; [unfold in_iv, aw_ceiling_asan in *; ulia|].
  intros w Hw NK Hw'. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [|exact Hw'].
  apply in_map. apply filter_In. split; [exact Hw|]. destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity].
Qed.

Lemma heap_frameA : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsA dargs m mo -> heap_holdsA dargs m' mo.
Proof.
  intros dargs m m' mo AG DM HH. apply (heap_frameA_v dargs m m' mo AG (wmono_of m m' DM)); [| exact HH].
  intros a Ha. apply DM. unfold AIMG_HI in Ha. lia.
Qed.

Lemma heap_frameX_v : forall dargs m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono bsegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  heap_holdsX dargs m mo -> heap_holdsX dargs m' mo.
Proof. intros dargs m m' mo AG WM DM HH. apply heap_holdsA_inv. apply (heap_frameA_v dargs m m' mo AG WM DM). apply heap_holdsA_intro. exact HH. Qed.

Definition C0 (a : Z) : Prop := (0x10000 <= a < AIMG_HI) \/ (ATOP <= a < two64).

Definition cov1 (id : int) (dargs : list word) (z : Z) : Prop :=
  PrimInt63.eqb id OPID = true /\
  exists md aw ws ca, decode dargs = Some (md, aw, ws, ca) /\ (in_ws (heap_ws ws) z \/ sh_cov z).

Definition holdsA (id : int) (dargs : list word) (m : amem) (mo : Model) : Prop :=
  if PrimInt63.eqb id OPID then heap_holdsA dargs m mo else False.
Definition fpA (id : int) (dargs : list word) : list (Z * Z) := if PrimInt63.eqb id OPID then heap_fp IMGX dargs else [].
Lemma frameA : forall id args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (fpA id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  holdsA id args m model -> holdsA id args m' model.
Proof.
  intros id args m m' model AG DM H. unfold holdsA, fpA in *.
  destruct (PrimInt63.eqb id OPID); [| exact H]. exact (heap_frameA args m m' model AG DM H).
Qed.

Lemma H_ledA : forall id args m mo, PrimInt63.eqb id OPID = true -> holdsA id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Proof.
  intros id args m mo E H. unfold holdsA in H. rewrite E in H. apply heap_holdsA_inv in H.
  destruct H as (md & aw & ws & ca & LB & W & _ & HA & _). destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  exact (ACCT_led _ _ _ _ _ _ AC).
Qed.

Lemma LB_byte_cov : forall W aw LB m mo v z, aw_holds_w W aw LB m mo -> In v LB -> in_iv v z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Proof.
  intros W aw LB m mo v z HW Hv Hz. pose proof HW as (AH & HT & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 Vb)). left. unfold in_iv, user_iv in Hz. cbn [fst snd] in Hz. ulia.
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 (HT b Hb))). right. exact Hz.
  - eapply (ACCT_cov aw _ _ _ _ _ mo b z AC AH (proj1 (proj1 Vb))). right.
    destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (_ & _ & NP & _). pose proof (shlen_le7 (ab_size b) ltac:(ulia)).
    unfold in_iv, fsh_iv in Hz. cbn [fst snd] in Hz. ulia.
Qed.

Lemma H_covA : forall id args m mo z, holdsA id args m mo -> cov1 id args z ->
  PrimInt63.eqb id OPID = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H (E & md' & aw' & ws' & ca' & D' & HWs). split; [exact E|].
  unfold holdsA in H. rewrite E in H. apply heap_holdsA_inv in H. destruct H as (md & aw & ws & ca & LB & W & D & HA & WF & _).
  rewrite D in D'. injection D' as <- <- <- <-.
  destruct HWs as [HWs|SHC]; [| destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & _); exact (ACCT_cov_sh _ _ _ _ _ _ z AC SHC)].

  assert (INB : exists v, In v LB /\ in_iv v z).
  { unfold in_ws, heap_ws in HWs. apply in_ivs_In in HWs as (v & Hv & Hz). apply in_map_iff in Hv as (w & <- & Hw).
    apply filter_In in Hw as [Hw NK]. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & KD).
    destruct KD as [[K _]|[[_ HB]|[_ (b & Hb & SUB)]]].
    - rewrite K in NK. cbn in NK. discriminate.
    - exists (w_iv w). split; assumption.
    - exists b. split; [exact Hb| apply SUB; exact Hz]. }
  destruct INB as (v & Hv & Hz). exact (LB_byte_cov W aw LB m mo v z HA Hv Hz).
Qed.

Lemma H_matA : forall id args m mo mo', holdsA id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holdsA id args m mo'.
Proof.
  intros id args m mo mo' H SB ND NEW. unfold holdsA in *. destruct (PrimInt63.eqb id OPID); [| exact H].
  apply heap_holdsA_inv in H. destruct H as (md & aw & ws & ca & LB & W & D & HA & WF & HC & TW).
  apply heap_holdsA_intro. exists md, aw, ws, ca, LB, W. split; [exact D|]. split; [| split; [exact WF| split; [exact HC| exact TW]]].
  destruct HA as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & AC & HU & CLS & VFL & INC).
  repeat (split; [assumption|]). split; [eapply ACCT_mat; eassumption| split; [exact HU| split; [exact CLS| split; [exact VFL| exact INC]]]].
Qed.

Definition asan_heap_optable : St.optable :=
  asan_optable holdsA fpA frameA C0 cov1 COVP NMAX (fun id => PrimInt63.eqb id OPID) H_ledA H_covA H_matA.

Definition semvA (id : int) (dargs : list word) (m : amem) (mo : Model) (z : Z) : Prop :=
  PrimInt63.eqb id OPID = true /\
  exists md aw ws ca LB, decode dargs = Some (md, aw, ws, ca) /\ aw_holds_asan aw LB m mo /\
    exists v, In v LB /\ (in_iv v z \/ (user_band (fst v) /\ exists z0, in_iv v z0 /\ z = shad z0)).

Lemma H_semA : forall id args m mo z, holdsA id args m mo -> semvA id args m mo z ->
  PrimInt63.eqb id OPID = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z _ (E & md & aw & ws & ca & LB & D & [W HA] & v & Hv & CASE). split; [exact E|].
  destruct CASE as [Hz|(UB & z0 & Hz0 & ->)]; [exact (LB_byte_cov W aw LB m mo v z HA Hv Hz)|].
  pose proof HA as (AH & HT & _ & _ & _ & _ & _ & _ & _ & _ & AC & _).
  destruct (LB_cases W aw LB m mo v HA Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - eapply (ACCT_cov aw _ _ _ _ _ mo b _ AC AH (proj1 Vb)). right.
    destruct (blk_facts _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & HI & A8 & _). destruct (user_app_band _ _ BK NP) as [_ B2].
    unfold in_iv, user_iv in Hz0. cbn [fst snd] in Hz0.
    unfold shad, shlen. rewrite !Z.shiftr_div_pow2 by ulia. change (2 ^ 3) with 8. clear - Hz0 A8 NP B2. Z.div_mod_to_equations. ulia.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b HA Hb) as (T1 & T2 & T3). unfold twin_iv, user_band in UB. cbn [fst] in UB. ulia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b HA Vb) as (T1 & T2 & T3 & _). unfold fsh_iv, user_band in UB. cbn [fst] in UB. ulia.
Qed.

Lemma asan_heap_acc_user : forall (os : list St.oinst) (m : amem) (mo : Model) (acc : list (word * nat)),
  St.op_minv asan_heap_optable mo ->
  Forall (fun o => St.op_holds asan_heap_optable (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n ->
     St.op_cov asan_heap_optable os (bv_unsigned a + j) \/ Exists (fun o => semvA (fst o) (snd o) m mo (bv_unsigned a + j)) os) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ St.op_minv asan_heap_optable mo' /\
              Forall (fun o => St.op_holds asan_heap_optable (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  exact (asan_acc_user holdsA C0 cov1 COVP NMAX (fun id => PrimInt63.eqb id OPID) H_ledA H_covA H_matA semvA H_semA os m mo acc MI HO HC).
Qed.

Lemma twins_mapped : forall W aw LB m mo L' RNG' st' LBa' m', aw_holds_w W aw LB m mo -> AHEAP AI L' RNG' st' LBa' m' ->
  (forall b, In b (w_T W) -> In b LBa') ->
  forall a, in_ivs (map twin_iv (w_T W)) a -> m' (wa a) <> None.
Proof.
  intros W aw LB m mo L' RNG' st' LBa' m' HW AH' SUB a Ha. pose proof HW as (_ & HT & _).
  apply in_ivs_In in Ha as (w & Hw & Hin). apply in_map_iff in Hw as (b & <- & HbT).
  destruct (HT b HbT) as [_ HbH]. destruct (LB_twin_facts W aw LB m mo b HW HbT) as (T1 & T2 & T3).
  unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
  assert (G : 0 <= a - shad (ab_addr b) /\ 8 * (a - shad (ab_addr b)) < ab_size b).
  { unfold shlen in Hin. rewrite Z.shiftr_div_pow2 in Hin by ulia. change (2^3) with 8 in Hin. Z.div_mod_to_equations. ulia. }
  pose proof (twin_mapped_ms _ _ _ _ _ b _ AH' (SUB b HbT) HbH (proj1 G) (proj2 G)) as P.
  replace (shad (ab_addr b) + (a - shad (ab_addr b))) with a in P by ulia. exact P.
Qed.

Lemma aw_real_nodelta : forall aw aw' LB m mo W RNG' st' m' mo',
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' (w_LBa W) m' -> ACCT aw' (w_L W) RNG' st' (w_LBa W) mo' ->
  (forall b x, In b (w_LBa W) -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  twins_pres (w_LBa W) m m' ->
  aw_realW aw' LB m' mo' (mkWit (w_L W) RNG' st' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
Proof.
  intros aw aw' LB m mo W RNG' st' m' mo' [HW EM] AH' AC' KEEPF TW.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  split; [| reflexivity]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|].
  split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' (fun b Hb => proj1 (HT b Hb)))|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'| split; [exact HU| split; [exact CLS| split]]].
  - apply (vfl_keep W aw LB m mo m' (conj HW EM)). intros b x [[Hb _] FK] Hx. exact (KEEPF b x Hb FK Hx).
  - intros b [HbL NFAb] HHb NTb. apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' HbL HHb TW HbL).
    intros g G0 G1. exact (INC b (conj HbL NFAb) HHb NTb g G0 G1).
Qed.

Lemma aw_real_twin_write : forall aw LB m mo W p A n (m' : amem) lo sp,
  aw_realW aw LB m mo W -> In (HB p A n) (w_T W) -> is_primary n = true ->
  ATOP + 4096 <= lo -> lo <= sp -> sp <= 2 ^ 47 ->
  munch [(lo, sp); (shad A, shad A + shlen (n + 7))] m m' -> wmono bsegs m m' ->
  (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
  aw_realW aw LB m' mo (set_ms W m').
Proof.
  intros aw LB m mo W p A n m' lo sp [HW EM] HbT PRIM LO1 LO2 SP47 MU WM RDM.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as ATR.
  rewrite EM in AH. destruct (HT _ HbT) as [HbL HbH].
  destruct (LB_twin_facts W aw LB m mo _ HW HbT) as (T1 & T2 & T3). cbn [ab_addr ab_size] in T1, T2, T3.
  set (intw := fun x : word => (shad A <=? bv_unsigned x) && (bv_unsigned x <? shad A + shlen (n + 7))).
  assert (INTW : forall x, intw x = true <-> shad A <= bv_unsigned x < shad A + shlen (n + 7)).
  { intros x. unfold intw. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  assert (OUTM : forall x : word, intw x = false -> ~ (lo <= bv_unsigned x < sp) -> m' x = m x).
  { intros x NI NS. apply MU. cbn [ALib.Frame.outside]. split; [lia|]. split; [| exact I].
    destruct (intw x) eqn:E; [discriminate|]. assert (X : ~ (shad A <= bv_unsigned x < shad A + shlen (n + 7))) by (rewrite <- INTW; congruence). lia. }
  set (m1 := fun x : word => if intw x then m x else m' x).
  assert (AH1 : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m1).
  { eapply (AI_frame AI _ _ _ _ m m1 [(lo, sp)]); [exact AH | | |].
    - intros x OUT. cbn [ALib.Frame.outside] in OUT. unfold m1. destruct (intw x) eqn:E; [reflexivity|]. apply OUTM; [exact E| lia].
    - intros x Hx. unfold m1. destruct (intw x) eqn:E.
      + rewrite (wview_ext1 (fun y => if intw y then m y else m' y) m x); [exact Hx| rewrite E; reflexivity].
      + rewrite (wview_ext1 (fun y => if intw y then m y else m' y) m' x); [exact (WM x Hx)| rewrite E; reflexivity].
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. left. lia. }
  assert (AH' : AHEAP AI (w_L W) (w_RNG W) (w_st W) (w_LBa W) m').
  { eapply (AI_frame_twin AI _ _ _ _ m1 m' p A n AH1 HbL PRIM).
    - intros x OUT. cbn [ALib.Frame.outside] in OUT. unfold m1. destruct (intw x) eqn:E; [| reflexivity]. apply INTW in E. lia.
    - intros x Hx. destruct (intw x) eqn:E.
      + apply INTW in E. unfold wview.
        assert (MP : m' x <> None).
        { replace x with (wa (shad A + (bv_unsigned x - shad A))); [apply RDM; lia|]. unfold wa. replace (shad A + (bv_unsigned x - shad A)) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
        destruct (m' x); [discriminate| contradiction].
      + rewrite <- (wview_ext1 m1 m' x); [exact Hx| unfold m1; rewrite E; reflexivity].
    - exact RDM. }
  assert (UWA : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply Z_to_bv_small; unfold bv_modulus; lia).

  assert (KEEPB : forall a, 0 <= a < ATOP + 4096 -> ~ (shad A <= a < shad A + shlen (n + 7)) -> m' (wa a) = m (wa a)).
  { intros a Ha NT. apply OUTM; [| rewrite UWA by lia; lia].
    destruct (intw (wa a)) eqn:E; [| reflexivity]. apply INTW in E. rewrite UWA in E by lia. contradiction. }
  split; [| reflexivity]. unfold aw_holds_w, set_ms. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [intros a _ _; reflexivity|].
  split.
  { intros a Ha. destruct (Z_le_dec (shad A) a) as [L1|]; [destruct (Z_lt_dec a (shad A + shlen (n + 7))) as [L2|]|].
    - replace a with (shad A + (a - shad A)) by lia. apply RDM. lia.
    - pose proof (MAP a Ha) as M0. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
      destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (U1 & U2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      rewrite KEEPB by lia. exact M0.
    - pose proof (MAP a Ha) as M0. apply in_ivs_In in Ha as (v & Hv & Hin). apply in_map_iff in Hv as (b' & <- & Hb').
      destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (U1 & U2 & _). unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin.
      rewrite KEEPB by lia. exact M0. }
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC| split; [exact HU| split; [exact CLS| split]]].
  -
    apply (vfl_agree W aw LB m mo m' HW). intros b x [[Hb NFA] HF] Hx. rewrite EM.
    destruct (AI_fake _ _ _ _ _ b AH Hb HF) as (BK & HI & A8 & N8 & NP & _). destruct (user_app_band _ _ BK ltac:(lia)) as [B1 B2].
    apply KEEPB; lia.
  -
    intros b Vb HH NT g G0 G1. rewrite <- (INC b Vb HH NT g G0 G1).
    destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (Nb & BRb & _).
    assert (INB : in_iv (twin_iv b) (shad (ab_addr b) + g)).
    { unfold in_iv, twin_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
    destruct (in_twin_clear W aw LB m mo b _ HW Vb HH NT INB) as (R1 & NU & _).
    apply KEEPB; [exact R1|]. intros X. apply NU. apply in_ivs_In. exists (twin_iv (HB p A n)).
    split; [apply HLB; right; left; exists (HB p A n); split; [exact HbT| reflexivity]| unfold in_iv, twin_iv; cbn [fst snd ab_addr ab_size]; exact X].
Qed.

Lemma aw_real_frame_in : forall aw aw' LB m mo W RNG' st' c F n LBk m' mo' sp,
  aw_realW aw LB m mo W ->
  AHEAP AI (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) m' -> ACCT aw' (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) mo' ->
  aheap_pres (aci AI) LBk sp m m' -> n <= FRAME_MAX ->
  (forall b, In b LBk -> In b (w_LBa W)) -> (forall b, vis W b -> In b LBk) ->
  (exists flg, bytes_at bsegs m' (F + n - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) (mkABlock (ABFake c) F n) flg) ->
  twins_pres (w_LBa W) m m' ->
  let fb := mkABlock (ABFake c) F n in
  let W1 := mkWit (w_L W) RNG' st' (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W) in
  aw_realW aw' ((F, n - 8) :: (shad F, shlen n) :: LB) m' mo' W1 /\ visf W1 fb
  /\ (forall a, in_iv (F, n - 8) a -> ~ in_user LB a) /\ (forall a, in_iv (shad F, shlen n) a -> ~ in_user LB a).
Proof.
  intros aw aw' LB m mo W RNG' st' c F n LBk m' mo' sp [HW EM] AH' AC' PRES NFM KEEP1 KEEP2 FLW TW fb W1.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC). pose proof atop_range as AR.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  assert (FF : is_fake fb) by (exists c; reflexivity).
  destruct (AI_fake _ _ _ _ _ fb AH' ltac:(left; reflexivity) FF) as (BKF & HIF & A8F & N8F & NPF & _). cbn [ab_addr ab_size fb] in BKF, HIF, A8F, N8F, NPF.
  destruct (fsh_band _ _ BKF HIF A8F N8F ltac:(ulia)) as (FS1 & FS2 & FS3 & _). destruct (user_app_band _ _ BKF ltac:(ulia)) as [BF1 BF2].
  set (FA' := List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) in *.
  assert (INFA' : forall b, In b FA' <-> In b (w_FA W) /\ In b LBk).
  { intros b. unfold FA'. rewrite filter_In. destruct (in_dec ablock_eq_dec b LBk); split; intros [H1 H2]; try discriminate; auto. }
  assert (VIS1 : forall b, vis W1 b <-> b = fb \/ vis W b).
  { intros b. unfold vis, W1. cbn [w_LBa w_FA]. fold FA'. split.
    - intros [[<-|Hb] NF]; [left; reflexivity| right]. split; [exact (KEEP1 b Hb)|]. intros X. apply NF. apply INFA'. split; assumption.
    - intros [->|[Hb NF]]; [split; [left; reflexivity| intros X; apply INFA' in X as [_ X]; exact (NIN X)]|].
      split; [right; apply KEEP2; split; assumption| intros X; apply INFA' in X as [X _]; exact (NF X)]. }
  assert (TK : forall b, In b (w_T W) -> In b LBk).
  { intros b Hb. destruct (HT b Hb) as [HbL HbH]. apply KEEP2. split; [exact HbL|]. intros X. exact (heap_not_fake b HbH (proj2 (HFA b X))). }
  assert (DISJ : forall b, In b LBk -> F + n <= ab_addr b \/ ab_addr b + ab_size b <= F).
  { intros b Hb. pose proof (AI_blocks_disjoint AI _ _ _ _ _ fb b AH' ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(intros <-; exact (NIN Hb))) as D.
    cbn [ab_addr ab_size fb] in D. exact D. }
  assert (HW1 : aw_holds_w W1 aw' ((F, n - 8) :: (shad F, shlen n) :: LB) m' mo').
  { unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc W1]. fold FA'.
    split; [exact AH'|]. split. { intros b Hb. split; [right; exact (TK b Hb)| exact (proj2 (HT b Hb))]. }
    split; [exact ND|]. split. { intros b Hb. apply INFA' in Hb as [Hb HbK]. split; [right; exact HbK| exact (proj2 (HFA b Hb))]. }
    split; [apply NoDup_filter; exact NDF|]. split.
    { intros v. cbn [In]. rewrite (HLB v). unfold visf. split.
      - intros [<-|[<-|[(b & Vb & ->)|[H|(b & [Vb HF] & ->)]]]].
        + left. exists fb. split; [apply VIS1; left; reflexivity| reflexivity].
        + right. right. exists fb. split; [split; [apply VIS1; left; reflexivity| exact FF]| reflexivity].
        + left. exists b. split; [apply VIS1; right; exact Vb| reflexivity].
        + right. left. exact H.
        + right. right. exists b. split; [split; [apply VIS1; right; exact Vb| exact HF]| reflexivity].
      - intros [(b & Vb & ->)|[H|(b & [Vb HF] & ->)]].
        + apply VIS1 in Vb as [->|Vb]; [left; reflexivity| right; right; left; exists b; split; [exact Vb| reflexivity]].
        + right. right. right. left. exact H.
        + apply VIS1 in Vb as [->|Vb]; [right; left; reflexivity| right; right; right; right; exists b; split; [split; assumption| reflexivity]]. }
    split; [intros a _ _; reflexivity|].
    split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' (fun b Hb => or_intror (TK b Hb)))|].
    split; [exact ZC0|]. split.
    { assert (LE : (length FA' <= length (w_FA W))%nat) by (unfold FA'; apply filter_length_le). ulia. }
    split; [exact AC'|]. split; [exact HU|].
    split. { intros b [<-|Hb] FK; [cbn [ab_size fb]; exact NFM| exact (CLS b (KEEP1 b Hb) FK)]. }
    split.
    2:{
        intros b Vb1 HHb NTb. apply VIS1 in Vb1 as [->|Vb]; [exfalso; exact (heap_not_fake fb HHb FF)|].
        apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(right; exact (KEEP2 b Vb)) HHb TW (proj1 Vb)).
        intros g G0 G1. exact (INC b Vb HHb NTb g G0 G1). }

    intros b [Vb1 FKb]. apply VIS1 in Vb1 as [->|Vb]; [cbn [ab_addr ab_size fb]; exact FLW|].
    apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| split; [exact Vb| exact FKb]]. intros b0 x [Vb0 _] Hx.
    destruct (blk_facts _ _ _ _ _ b0 AH (proj1 Vb0)) as (NP0 & BK0 & HI0 & _). destruct (user_app_band _ _ BK0 NP0) as [_ B20].
    apply (pres_block LBk sp m m' b0 x PRES (KEEP2 b0 Vb0)); [ulia| ulia| exact Hx]. }
  split; [split; [exact HW1| reflexivity]|].
  split; [split; [apply VIS1; left; reflexivity| exact FF]|].
  split.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + specialize (DISJ b (KEEP2 b Vb)). ulia.
    + destruct (LB_twin_facts W aw LB m mo b HW Hb) as (T1 & T2 & _). ulia.
    + destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (T1 & T2 & _). ulia.
  - intros a Ha U. apply in_ivs_In in U as (v & Hv & Hva). unfold in_iv in Ha, Hva. cbn [fst snd] in Ha.
    pose proof (shlen_le7 n ltac:(ulia)) as LEn.
    destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hva.
    + destruct (LB_user_facts W aw LB m mo b HW Vb) as (_ & B1 & _). ulia.
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_introl Hb)) as (H1 & H2 & H3 & H4).
      exact (gran_disj F n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b (TK b Hb)) A8F H4 ltac:(ulia) Hva).
    + destruct (LB_shadow_hull W aw LB m mo b HW (or_intror Vb)) as (H1 & H2 & H3 & H4).
      pose proof (shlen_le7 (ab_size b) ltac:(ulia)) as LE.
      exact (gran_disj F n (ab_addr b) (ab_size b) a ltac:(ulia) H2 ltac:(ulia) ltac:(ulia) (DISJ b (KEEP2 b (proj1 Vb))) A8F H4 ltac:(ulia) ltac:(ulia)).
Qed.

Lemma iv_origin : forall W aw LB m mo, aw_holds_w W aw LB m mo ->
     (forall b b', vis W b -> vis W b' -> user_iv b = user_iv b' -> b = b')
  /\ (forall b b', vis W b -> In b' (w_T W) -> user_iv b <> twin_iv b')
  /\ (forall b b', vis W b -> visf W b' -> user_iv b <> fsh_iv b')
  /\ (forall b b', In b (w_T W) -> In b' (w_T W) -> twin_iv b = twin_iv b' -> b = b')
  /\ (forall b b', In b (w_T W) -> visf W b' -> twin_iv b <> fsh_iv b')
  /\ (forall b b', visf W b -> visf W b' -> fsh_iv b = fsh_iv b' -> b = b').
Proof.
  intros W aw LB m mo HW. pose proof HW as (AH & HT & _).
  repeat split.
  - intros b b' Vb Vb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) (proj1 Vb')). unfold user_iv in E. injection E as E1 _. rewrite E1. reflexivity.
  - intros b b' Vb Hb' E. destruct (LB_user_facts W aw LB m mo b HW Vb) as (NP & B1 & _). destruct (LB_twin_facts W aw LB m mo b' HW Hb') as (T1 & T2 & T3).
    unfold user_iv, twin_iv in E. injection E as E1 _. ulia.
  - intros b b' Vb Vb' E. destruct (LB_user_facts W aw LB m mo b HW Vb) as (NP & B1 & _). destruct (LB_fsh_facts W aw LB m mo b' HW Vb') as (T1 & T2 & T3 & _).
    unfold user_iv, fsh_iv in E. injection E as E1 _. ulia.
  - intros b b' Hb Hb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (HT b' Hb'))). unfold twin_iv in E. injection E as E1 _. exact E1.
  - intros b b' Hb Vb' E. assert (b = b') as <-.
    { apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (HT b Hb)) (proj1 (proj1 Vb'))). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1. }
    exact (heap_not_fake b (proj2 (HT b Hb)) (proj2 Vb')).
  - intros b b' Vb Vb' E. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 (proj1 Vb)) (proj1 (proj1 Vb'))). unfold fsh_iv in E. injection E as E1 _. exact E1.
Qed.

Lemma aw_real_frame_out : forall aw aw' LB m mo W RNG' st' fb LBk m' mo',
  aw_realW aw LB m mo W -> visf W fb ->
  AHEAP AI (w_L W) RNG' st' LBk m' -> ACCT aw' (w_L W) RNG' st' LBk mo' ->
  (forall b, In b LBk <-> In b (w_LBa W) /\ b <> fb) ->
  (forall b x, In b (w_LBa W) -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (wa x) = m (wa x)) ->
  twins_pres (w_LBa W) m m' ->
  aw_realW aw' (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m' mo'
          (mkWit (w_L W) RNG' st' LBk (w_T W) (w_FA W) m' (w_zc W)).
Proof.
  intros aw aw' LB m mo W RNG' st' fb LBk m' mo' [HW EM] VF AH' AC' RM KEEPF TW.
  pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  destruct (iv_origin W aw LB m mo HW) as (O1 & O2 & O3 & O5 & O6 & O8).
  destruct VF as [[HfL NfA] FF].
  set (W1 := mkWit (w_L W) RNG' st' LBk (w_T W) (w_FA W) m' (w_zc W)).
  assert (VIS1 : forall b, vis W1 b <-> vis W b /\ b <> fb).
  { intros b. unfold vis, W1. cbn [w_LBa w_FA]. rewrite RM. tauto. }
  assert (TK : forall b, In b (w_T W) -> In b LBk).
  { intros b Hb. destruct (HT b Hb) as [HbL HbH]. apply RM. split; [exact HbL|]. intros ->. exact (heap_not_fake fb HbH FF). }
  split; [| reflexivity]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH'|]. split. { intros b Hb. split; [exact (TK b Hb)| exact (proj2 (HT b Hb))]. }
  split; [exact ND|]. split. { intros b Hb. destruct (HFA b Hb) as [HbL HF]. split; [apply RM; split; [exact HbL| intros ->; exact (NfA Hb)]| exact HF]. }
  split; [exact NDF|]. split.
  { intros v. fold W1. split.
    - intros Hv. apply in_remove in Hv as [Hv N2]. apply in_remove in Hv as [Hv N1].
      destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
      + left. exists b. split; [apply VIS1; split; [exact Vb| intros ->; apply N1; reflexivity]| reflexivity].
      + right. left. exists b. split; [exact Hb| reflexivity].
      + right. right. exists b. split; [split; [apply VIS1; split; [exact (proj1 Vb)| intros ->; apply N2; reflexivity]| exact (proj2 Vb)]| reflexivity].
    - intros Hv. assert (VFB : visf W fb) by (split; [split; assumption| exact FF]).
      destruct Hv as [(b & Vb & ->)|[(b & Hb & ->)|(b & [Vb HF] & ->)]].
      + apply VIS1 in Vb as [Vb NE]. apply in_in_remove; [exact (O3 b fb Vb VFB)|]. apply in_in_remove; [intros E; exact (NE (O1 b fb Vb (proj1 VFB) E))|].
        apply HLB. left. exists b. split; [exact Vb| reflexivity].
      + apply in_in_remove; [exact (O6 b fb Hb VFB)|]. apply in_in_remove; [intros E; exact (O2 fb b (proj1 VFB) Hb (eq_sym E))|].
        apply HLB. right. left. exists b. split; [exact Hb| reflexivity].
      + apply VIS1 in Vb as [Vb NE]. apply in_in_remove; [intros E; exact (NE (O8 b fb (conj Vb HF) VFB E))|].
        apply in_in_remove; [intros E; exact (O3 fb b (proj1 VFB) (conj Vb HF) (eq_sym E))|].
        apply HLB. right. right. exists b. split; [split; assumption| reflexivity]. }
  split; [intros a _ _; reflexivity|].
  split; [exact (twins_mapped W aw LB m mo _ _ _ _ m' HW AH' TK)|].
  split; [exact ZC0|]. split; [exact ZCB|]. split; [exact AC'|]. split; [exact HU|].
  split. { intros b Hb FK. exact (CLS b (proj1 (proj1 (RM b) Hb)) FK). }
  split.
  2:{ intros b Vb1 HHb NTb. apply VIS1 in Vb1 as [Vb NEb].
      apply (twin_keep _ _ _ _ m m' (w_LBa W) b AH' ltac:(apply RM; split; [exact (proj1 Vb)| exact NEb]) HHb TW (proj1 Vb)).
      intros g G0 G1. exact (INC b Vb HHb NTb g G0 G1). }
  intros b [Vb1 FKb]. apply VIS1 in Vb1 as [Vb NEb].
  apply (vfl_keep W aw LB m mo m' (conj HW EM)); [| split; [exact Vb| exact FKb]]. intros b0 x [[Hb0 _] FK0] Hx. exact (KEEPF b0 x Hb0 FK0 Hx).
Qed.

Lemma aw_real_flag : forall aw LB m mo W fb, aw_realW aw LB m mo W -> visf W fb ->
  exists flg, bytes_at bsegs m (ab_addr fb + ab_size fb - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) fb flg.
Proof.
  intros aw LB m mo W fb [HW EM] VF. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VFL & _).
  rewrite <- EM. exact (VFL fb VF).
Qed.

Lemma aw_real_flag_rng : forall aw LB m mo W fb, aw_realW aw LB m mo W -> visf W fb ->
  exists flg, bytes_at bsegs m (ab_addr fb + ab_size fb - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AI (w_L W) fb flg
    /\ 0 <= flg < 2 ^ 64 /\ forall RNG', FRNG AI AI_fake (w_L W) RNG' -> rng RNG' flg 1.
Proof.
  intros aw LB m mo W fb AR VF. destruct (aw_real_flag aw LB m mo W fb AR VF) as (flg & BA & FL). exists flg. split; [exact BA|]. split; [exact FL|].
  destruct AR as [HW EM]. pose proof HW as (AH & _). rewrite EM in AH.
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH (proj1 (proj1 VF))) as (_ & _ & BAND & _ & A1 & A2). pose proof atop_range as ATR.
  split; [unfold AIMG_HI, KLS in BAND; lia|].
  intros RNG' FR. apply (rng_sub' RNG' (al_fake (w_L W)) 11571200 flg 1 (fk_area AI AI_fake _ _ FR)). lia.
Qed.
Lemma aw_real_fake_free : forall aw aw' LB m mo W fb flg mo',
  aw_realW aw LB m mo W -> visf W fb -> flag_law AI (w_L W) fb flg ->
  ACCT aw' (w_L W) (w_RNG W) (w_st W) (lb_del fb (w_LBa W)) mo' ->
  let m' := write_to_mem m (wa flg) [Z_to_bv 8 0] in
  aw_realW aw' (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m' mo'
          (mkWit (w_L W) (w_RNG W) (w_st W) (lb_del fb (w_LBa W)) (w_T W) (w_FA W) m' (w_zc W))
  /\ wr_at bsegs m flg 1
  /\ (forall x : word, bv_unsigned x <> flg -> m' x = m x).
Proof.
  intros aw aw' LB m mo W fb flg mo' AR VF FL AC' m'. pose proof AR as [HW EM]. pose proof HW as (AH & _).
  destruct VF as [[HfL NfA] FF]. rewrite EM in AH.
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH HfL) as (AH' & WR & BAND & NOBLK & _).
  assert (F0 : 0 <= flg /\ flg + 1 <= 2^64) by (pose proof atop_range as AR'; unfold AIMG_HI, KLS in BAND; lia).
  assert (OUT : forall x : word, bv_unsigned x <> flg -> m' x = m x).
  { intros x NE. unfold m'. rewrite (write_to_mem_spec [Z_to_bv 8 0] m flg x (proj1 F0) ltac:(cbn [length]; lia)). cbn [length].
    destruct (Z.leb_spec0 flg (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (flg + Z.of_nat 1)); cbn [andb]; try reflexivity. exfalso. lia. }
  split; [| split; [exact WR| exact OUT]].
  apply (aw_real_frame_out aw aw' LB m mo W (w_RNG W) (w_st W) fb (lb_del fb (w_LBa W)) m' mo' AR (conj (conj HfL NfA) FF) AH' AC').
  - intros b. apply lb_del_In.
  - intros b x Hb _ Hx. apply OUT. intros E.
    assert (UX : bv_unsigned (wa x) = x).
    { unfold wa. apply Z_to_bv_small. destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & BK & HI & _). destruct (user_app_band _ _ BK NP) as [_ B2].
      pose proof atop_range as AR'. unfold bv_modulus. lia. }
    rewrite UX in E. subst x. exact (NOBLK b Hb Hx).
  -
    intros p0 A0 n0 Hin PR i Hi. apply OUT.
    destruct (heap_block_facts _ _ _ _ _ (HB p0 A0 n0) AH Hin ltac:(exists p0; reflexivity)) as (N0 & BR0 & _). cbn [ab_addr ab_size] in N0, BR0.
    destruct (twin_band _ _ BR0 N0) as (T1 & T2 & _). pose proof atop_range as AR'. unfold AIMG_HI, KLS in BAND.
    unfold wa. rewrite Z_to_bv_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma aw_real_burn : forall aw LB m mo W c,
  aw_realW aw LB m mo W -> 0 <= c <= w_zc W ->
  aw_realW aw LB m mo (mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (w_FA W) (w_ms W) (w_zc W - c)).
Proof.
  intros aw LB m mo W c [HW EM] C. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  split; [| exact EM]. unfold aw_holds_w, vis, visf. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split; [exact HT|]. split; [exact ND|]. split; [exact HFA|]. split; [exact NDF|]. split; [exact HLB|].
  split; [exact EQ|]. split; [exact MAP|]. split; [ulia|]. split; [ulia|]. split; [exact AC| split; [exact HU| split; [exact CLS| split; [exact VFL| exact INC]]]].
Qed.

Lemma aw_real_abandon : forall aw LB m mo W fb c,
  aw_realW aw LB m mo W -> visf W fb -> 1 <= c <= w_zc W ->
  aw_realW aw (remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB)) m mo
          (mkWit (w_L W) (w_RNG W) (w_st W) (w_LBa W) (w_T W) (fb :: w_FA W) (w_ms W) (w_zc W - c)).
Proof.
  intros aw LB m mo W fb c [HW EM] VFB C. pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  destruct (iv_origin W aw LB m mo HW) as (O1 & O2 & O3 & O5 & O6 & O8).
  pose proof VFB as [[HfL NfA] FF].
  split; [| exact EM]. unfold aw_holds_w. cbn [w_L w_RNG w_st w_LBa w_T w_FA w_ms w_zc].
  split; [exact AH|]. split; [exact HT|]. split; [exact ND|].
  split. { intros b [<-|Hb]; [split; assumption| exact (HFA b Hb)]. }
  split; [constructor; assumption|]. split.
  { intros v. unfold vis, visf. cbn [In w_LBa w_FA]. split.
    - intros Hv. apply in_remove in Hv as [Hv N2]. apply in_remove in Hv as [Hv N1].
      destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
      + left. exists b. split; [| reflexivity]. split; [exact (proj1 Vb)|]. intros [<-|X]; [apply N1; reflexivity| exact (proj2 Vb X)].
      + right. left. exists b. split; [exact Hb| reflexivity].
      + right. right. exists b. split; [| reflexivity]. split; [| exact (proj2 Vb)]. split; [exact (proj1 (proj1 Vb))|].
        intros [<-|X]; [apply N2; reflexivity| exact (proj2 (proj1 Vb) X)].
    - intros [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
      + assert (Vb : vis W b) by (split; [exact Hb| intros X; apply NF; right; exact X]).
        assert (NE : b <> fb) by (intros ->; apply NF; left; reflexivity).
        apply in_in_remove; [exact (O3 b fb Vb VFB)|]. apply in_in_remove; [intros E; exact (NE (O1 b fb Vb (proj1 VFB) E))|].
        apply HLB. left. exists b. split; [exact Vb| reflexivity].
      + apply in_in_remove; [exact (O6 b fb Hb VFB)|].
        apply in_in_remove; [intros E; exact (O2 fb b (proj1 VFB) Hb (eq_sym E))|]. apply HLB. right. left. exists b. split; [exact Hb| reflexivity].
      + assert (Vb : visf W b) by (split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact HF]).
        assert (NE : b <> fb) by (intros ->; apply NF; left; reflexivity).
        apply in_in_remove; [intros E; exact (NE (O8 b fb Vb VFB E))|].
        apply in_in_remove; [intros E; exact (O3 fb b (proj1 VFB) Vb (eq_sym E))|]. apply HLB. right. right. exists b. split; [exact Vb| reflexivity]. }
  split; [exact EQ|]. split; [exact MAP|].
  split; [ulia|]. split; [cbn [length]; ulia|]. split; [exact AC| split; [exact HU| split; [exact CLS| split]]].
  - intros b [[Hb NF] FK]. apply VFL. split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact FK].
  - intros b [Hb NF] HHb NTb. apply (INC b); [split; [exact Hb| intros X; apply NF; right; exact X]| exact HHb| exact NTb].
Qed.

Lemma aw_real_cls : forall aw LB m mo W c F n, aw_realW aw LB m mo W -> In (mkABlock (ABFake c) F n) (w_LBa W) -> c <= 2.
Proof.
  intros aw LB m mo W c F n [HW EM] Hb. pose proof HW as (AH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLS & _).
  assert (FK : is_fake (mkABlock (ABFake c) F n)) by (exists c; reflexivity).
  pose proof (CLS _ Hb FK) as SZ. destruct (fk_class AI AI_fake _ _ _ _ _ _ AH Hb FK) as (c' & K & C0 & EN).
  cbn [ab_kind ab_size] in K, EN, SZ. injection K as <-. unfold FRAME_MAX in SZ.
  destruct (Z_le_gt_dec c 2) as [LE|GT]; [exact LE| exfalso].
  pose proof (Z.pow_le_mono_r 2 3 c ltac:(lia) ltac:(lia)) as P. change (2 ^ 3) with 8 in P. lia.
Qed.

Lemma filter_length_split : forall {T} (f p : T -> bool) (l : list T),
  length (List.filter f l) = (length (List.filter (fun x => f x && p x) l) + length (List.filter (fun x => f x && negb (p x)) l))%nat.
Proof. intros T f p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (f x), (p x); cbn [andb negb length]; lia. Qed.

Lemma aw_real_fake_count : forall aw LB m mo W ws, aw_realW aw LB m mo W -> ties W ws ->
  Z.of_nat (length (List.filter fakeb (w_LBa W))) <= Z.of_nat (length ws) + ZTOTAL.
Proof.
  intros aw LB m mo W ws [HW EM] (T1 & T2 & T3 & _). pose proof HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & _).
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as NDL.
  set (inFA := fun b : ablock => if in_dec ablock_eq_dec b (w_FA W) then true else false).
  rewrite (filter_length_split fakeb inFA (w_LBa W)).
  assert (L1 : (length (List.filter (fun x => fakeb x && inFA x) (w_LBa W)) <= length (w_FA W))%nat).
  { apply NoDup_incl_length; [apply NoDup_filter; exact NDL|]. intros b Hb. apply filter_In in Hb as [_ Hb]. apply andb_prop in Hb as [_ Hb].
    unfold inFA in Hb. destruct (in_dec ablock_eq_dec b (w_FA W)); [assumption| discriminate]. }
  assert (L2 : (length (List.filter (fun x => fakeb x && negb (inFA x)) (w_LBa W)) <= length ws)%nat).
  { set (fw := fun b : ablock => Win (ab_addr b) (ab_size b - 8) K_FRAMEz).
    rewrite <- (length_map fw). apply NoDup_incl_length.
    - apply Finite.Injective_map_NoDup_in; [| apply NoDup_filter; exact NDL].
      intros b b' Hb Hb' E. apply filter_In in Hb as [Hb _]. apply filter_In in Hb' as [Hb' _]. unfold fw in E. injection E as E1 E2.
      destruct (ablock_eq_dec b b') as [->|NE]; [reflexivity| exfalso].
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH Hb Hb' NE) as D.
      destruct (blk_facts _ _ _ _ _ b AH Hb) as (NP & _). destruct (blk_facts _ _ _ _ _ b' AH Hb') as (NP' & _). lia.
    - intros w Hw. apply in_map_iff in Hw as (b & <- & Hb). apply filter_In in Hb as [HbL Hb]. apply andb_prop in Hb as [FK NF].
      apply fakeb_spec in FK. unfold inFA in NF. destruct (in_dec ablock_eq_dec b (w_FA W)) as [|NI]; [discriminate|].
      exact (proj1 (T3 b (conj (conj HbL NI) FK))). }
  lia.
Qed.

Lemma frame_in_visf : forall aw LB m mo W RNG' st' c F n LBk (m' : amem),
  aw_realW aw LB m mo W -> AHEAP AI (w_L W) RNG' st' (mkABlock (ABFake c) F n :: LBk) m' ->
  (forall b, In b LBk -> In b (w_LBa W)) -> (forall b, vis W b -> In b LBk) ->
  let fb := mkABlock (ABFake c) F n in
  let W1 := mkWit (w_L W) RNG' st' (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W) in
  forall b, visf W1 b <-> b = fb \/ visf W b.
Proof.
  intros aw LB m mo W RNG' st' c F n LBk m' [HW EM] AH' KEEP1 KEEP2 fb W1 b.
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _].
  assert (FF : is_fake fb) by (exists c; reflexivity).
  unfold visf, vis, W1. cbn [w_LBa w_FA]. rewrite filter_In. split.
  - intros [[[<-|Hb] NF] FK]; [left; reflexivity| right]. split; [split; [exact (KEEP1 b Hb)|]| exact FK].
    intros X. apply NF. split; [exact X|]. destruct (in_dec ablock_eq_dec b LBk); [reflexivity| contradiction].
  - intros [->|[[Hb NF] FK]].
    + split; [split; [left; reflexivity|]| exact FF]. intros [_ X]. destruct (in_dec ablock_eq_dec fb LBk) as [I|]; [exact (NIN I)| discriminate].
    + split; [split; [right; apply KEEP2; split; assumption|]| exact FK]. intros [X _]. exact (NF X).
Qed.

Lemma ties_frame_in : forall W W1 ws ws' fb,
  ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W -> is_fake fb -> (forall b, visf W1 b <-> b = fb \/ visf W b) ->
  (forall w, In w ws' <-> In w ws \/ w = Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz \/ w = Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) -> ghost_apart ws' ->
  (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 ws ws' fb (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EZ FF EV WS HV GAN PS. unfold ties. rewrite ET, EZ.
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb FF); reflexivity).
  split. { intros b Hb. apply WS. left. exact (T1 b Hb). }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]]; [exact (T2 w Hw K)| |]; cbn [w_kind] in K; unfold K_TWINz, K_FRAMEz, K_FTWINz in K; lia. }
  split. { intros b Vb. apply EV in Vb as [->|Vb]; [split; apply WS; [right; left| right; right]; reflexivity|].
           destruct (T3 b Vb) as [X Y]. split; apply WS; left; assumption. }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]].
           - destruct (T4 w Hw K) as (b & Vb & E). exists b. split; [apply EV; right; exact Vb| exact E].
           - exists fb. split; [apply EV; left; reflexivity|]. unfold w_iv. cbn [w_lo w_len]. symmetry. exact UF.
           - cbn [w_kind] in K. unfold K_FRAMEz, K_FTWINz in K. lia. }
  split. { intros w Hw K. apply WS in Hw as [Hw|[->| ->]].
           - destruct (T5 w Hw K) as (b & Vb & E). exists b. split; [apply EV; right; exact Vb| exact E].
           - cbn [w_kind] in K. unfold K_FRAMEz, K_FTWINz in K. lia.
           - exists fb. split; [apply EV; left; reflexivity| reflexivity]. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [Hw|[->| ->]]; [exact (T6 w Hw K Z0 B0)| |]; cbn [w_kind] in K; unfold K_STACK, K_FRAMEz, K_FTWINz in K; lia. }
  split; [apply WS; left; exact T7|].
  split. { intros w Hw K P. apply WS in Hw as [Hw|[->| ->]]; [exact (T8 w Hw K P)| |]; cbn [w_kind] in K; unfold K_STACK, K_FRAMEz, K_FTWINz in K; lia. }
  split; [| split; [exact GAN| intros IP; apply PS, PR; apply WS in IP as [IP|[E|E]]; [exact IP| |]; exfalso; unfold prist_win in E; injection E as _ _ E; unfold K_STACK, K_FRAMEz, K_FTWINz in E; lia]].
  intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & X). exists w. split; [apply WS; left; exact Hw| exact X].
Qed.

Lemma frame_windows_inj : forall W aw LB m mo b fb, aw_holds_w W aw LB m mo -> visf W b -> visf W fb ->
  (Win (ab_addr b) (ab_size b - 8) K_FRAMEz = Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz
   \/ Win (shad (ab_addr b)) (shlen (ab_size b)) K_FTWINz = Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) -> b = fb.
Proof.
  intros W aw LB m mo b fb HW Vb Vf E. pose proof HW as (AH & _).
  apply (shadow_iv_inj _ _ _ _ _ b fb AH (proj1 (proj1 Vb)) (proj1 (proj1 Vf))).
  destruct E as [E|E]; injection E as E1 _; [rewrite E1; reflexivity| exact E1].
Qed.
Lemma ties_frame_out : forall W W1 aw LB m mo ws ws' fb,
  aw_holds_w W aw LB m mo -> ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W -> visf W fb -> (forall b, visf W1 b <-> visf W b /\ b <> fb) ->
  (forall w, In w ws' <-> In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) ->
  (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 aw LB m mo ws ws' fb HW (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) ET EZ VF EV WS HV PS. unfold ties. rewrite ET, EZ.
  assert (KEEPK : forall w, In w ws -> w_kind w <> K_FRAMEz -> w_kind w <> K_FTWINz -> In w ws').
  { intros w Hw N1 N2. apply WS. split; [exact Hw|]. split; intros ->; [apply N1| apply N2]; reflexivity. }
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb (proj2 VF)); reflexivity).
  split. { intros b Hb. apply KEEPK; [exact (T1 b Hb)| |]; cbn [w_kind]; unfold K_TWINz, K_FRAMEz, K_FTWINz; lia. }
  split. { intros w Hw K. apply WS in Hw as [Hw _]. exact (T2 w Hw K). }
  split. { intros b Vb. apply EV in Vb as [Vb NE]. destruct (T3 b Vb) as [X Y].
           split; apply WS; (split; [assumption|]); split; intros E;
             try (apply NE; apply (frame_windows_inj W aw LB m mo b fb HW Vb VF); (left; exact E) || (right; exact E)); discriminate E. }
  split. { intros w Hw K. apply WS in Hw as (Hw & N1 & _). destruct (T4 w Hw K) as (b & Vb & E). exists b. split; [| exact E]. apply EV. split; [exact Vb|].
           intros ->. apply N1. destruct w as [lo len kd]. unfold w_iv in E. cbn [w_lo w_len w_kind] in E, K. rewrite UF in E. injection E as -> ->. rewrite K. reflexivity. }
  split. { intros w Hw K. apply WS in Hw as (Hw & _ & N2). destruct (T5 w Hw K) as (b & Vb & E). exists b. split; [| exact E]. apply EV. split; [exact Vb|].
           intros ->. apply N2. destruct w as [lo len kd]. unfold w_iv, fsh_iv in E. cbn [w_lo w_len w_kind] in E, K. injection E as -> ->. rewrite K. reflexivity. }
  split. { intros w Hw K Z0 B0. apply WS in Hw as [Hw _]. exact (T6 w Hw K Z0 B0). }
  split; [apply KEEPK; [exact T7| |]; unfold zc_win; cbn [w_kind]; unfold K_STACK, K_FRAMEz, K_FTWINz; lia|].
  split. { intros w Hw K P. apply WS in Hw as [Hw _]. exact (T8 w Hw K P). }
  split; [| split; [apply (ghost_apart_sub ws); [exact GA| intros w Hw; exact (proj1 (proj1 (WS w) Hw))]| intros IP; exact (PS (PR (proj1 (proj1 (WS _) IP))))]].
  intros b Vb HH CC. destruct (C24 b (HV b HH Vb) HH CC) as (w & Hw & HK & X). exists w. split; [| split; [exact HK| exact X]].
  apply KEEPK; [exact Hw| |]; unfold heap_kind, K_GHOST, K_FRAMEz, K_FTWINz in *; lia.
Qed.

Lemma ties_abandon : forall W W1 aw LB m mo ws ws' fb c,
  aw_holds_w W aw LB m mo -> ties W ws -> w_T W1 = w_T W -> w_zc W1 = w_zc W - c -> c <= w_zc W -> visf W fb -> (forall b, visf W1 b <-> visf W b /\ b <> fb) ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz
                           /\ w <> zc_win (w_zc W)) \/ w = zc_win (w_zc W - c)) ->
  (forall b, is_heap b -> vis W1 b -> vis W b) ->
  ZC_BASE + (w_zc W - c) < ZC_BAND -> (aprist (w_st W) -> aprist (w_st W1)) ->
  ties W1 ws'.
Proof.
  intros W W1 aw LB m mo ws ws' fb c HW TI ET EZ CZ VF EV WS HV ZB PS.

  set (wsm := List.filter (fun w => if window_eq_dec w (Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz) then false
                                     else if window_eq_dec w (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz) then false else true) ws).
  assert (WSM : forall w, In w wsm <-> In w ws /\ w <> Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz /\ w <> Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz).
  { intros w. unfold wsm. rewrite filter_In.
    destruct (window_eq_dec w (Win (ab_addr fb) (ab_size fb - 8) K_FRAMEz)); [split; [intros [_ X]; discriminate| intros (_ & X & _); contradiction]|].
    destruct (window_eq_dec w (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz)); [split; [intros [_ X]; discriminate| intros (_ & _ & X); contradiction]|]. tauto. }
  set (Wm := mkWit (w_L W1) (w_RNG W1) (w_st W1) (w_LBa W1) (w_T W1) (w_FA W1) (w_ms W1) (w_zc W)).
  assert (TM : ties Wm wsm).
  { apply (ties_frame_out W Wm aw LB m mo ws wsm fb HW TI); [exact ET| reflexivity| exact VF| | exact WSM| exact HV| exact PS].
    intros b. unfold Wm, visf, vis. cbn [w_LBa w_FA]. exact (EV b). }
  apply (ties_burn Wm W1 wsm ws' c TM); [reflexivity| intros b; unfold Wm, visf, vis; cbn [w_LBa w_FA]; reflexivity| exact EZ| exact CZ| | intros b _ V; exact V| exact ZB| intros P; exact P].
  intros w. rewrite (WS w). unfold Wm. cbn [w_zc]. rewrite (WSM w). tauto.
Qed.

Lemma ghost_window_entry : forall W aw LB m mo ws w, aw_holds_w W aw LB m mo -> ties W ws -> In w ws ->
  (w_kind w = K_TWINz \/ w_kind w = K_FRAMEz \/ w_kind w = K_FTWINz) ->
  In (w_iv w) LB /\ forall b, In b LB -> b <> w_iv w -> forall a, in_iv (w_iv w) a -> ~ in_iv b a.
Proof.
  intros W aw LB m mo ws w HW (T1 & T2 & T3 & T4 & T5 & _) Hw K. pose proof HW as (_ & _ & _ & _ & _ & HLB & _).
  assert (INW : In (w_iv w) LB).
  { apply HLB. destruct K as [K|[K|K]].
    - destruct (T2 w Hw K) as (b & Hb & E). right. left. exists b. split; [exact Hb| exact E].
    - destruct (T4 w Hw K) as (b & Vb & E). left. exists b. split; [exact (proj1 Vb)| exact E].
    - destruct (T5 w Hw K) as (b & Vb & E). right. right. exists b. split; [exact Vb| exact E]. }
  split; [exact INW|]. intros b Hb NE a Ha.
  destruct (Z.eq_dec (fst (w_iv w)) (fst b)) as [EA|NA].
  - exfalso. apply NE. destruct b as [A0 n0]. destruct (w_iv w) as [A1 n1] eqn:EW. cbn [fst] in EA. subst A1.
    rewrite (LB_same_addr W aw LB m mo A0 n1 n0 HW INW Hb). reflexivity.
  - exact (aw_blocks_disj_asan aw LB m mo (w_iv w) b a (ex_intro _ W HW) INW Hb NA Ha).
Qed.

Lemma shadow_in_law_w : forall W aw LB m mo b g, aw_holds_w W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  0 <= g -> 8 * g < ab_size b ->
  m (wa (shad (ab_addr b) + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? ab_size b then 0 else ab_size b - 8 * g)).
Proof. intros W aw LB m mo b g HW Vb HH NT G0 G1. exact (proj2 (proj2 (twin_out_w W aw LB m mo b HW Vb HH NT)) g G0 G1). Qed.

Lemma LB_entry_heap : forall W aw LB m mo ws v, aw_holds_w W aw LB m mo -> ties W ws -> In v LB -> user_band (fst v) ->
  (forall w, In w ws -> w_kind w = K_FRAMEz -> w_iv w <> v) ->
  exists b, vis W b /\ is_heap b /\ v = user_iv b /\ (In b (w_T W) <-> In (twin_iv b) LB).
Proof.
  intros W aw LB m mo ws v HW (T1 & T2 & T3 & _) Hv UB NF. pose proof HW as (AH & HT & _ & _ & _ & HLB & _).
  destruct (LB_cases W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - exists b. split; [exact Vb|]. destruct (kind_cases b) as [HH|HF].
    + split; [exact HH|]. split; [reflexivity|]. split.
      * intros HbT. apply HLB. right. left. exists b. split; [exact HbT| reflexivity].
      * intros IN. destruct (LB_cases W aw LB m mo _ HW IN) as [(b' & Vb' & E)|[(b' & Hb' & E)|(b' & Vb' & E)]].
        -- exfalso. destruct (LB_user_facts W aw LB m mo b' HW Vb') as (NP' & B1 & _). pose proof (usz_le b') as UL.
           destruct (heap_block_facts _ _ _ _ _ b AH (proj1 Vb) HH) as (N & BR & _). destruct (twin_band _ _ BR N) as (TB1 & TB2 & TB3 & _).
           unfold twin_iv, user_iv in E. injection E as E1 _. lia.
        -- replace b with b'; [exact Hb'|]. symmetry. apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) (proj1 (HT b' Hb'))).
           unfold twin_iv in E. injection E as E1 _. exact E1.
        -- exfalso. destruct Vb' as [[Hb'L _] HF']. assert (b = b') as <-; [| exact (heap_not_fake b HH HF')].
           apply (shadow_iv_inj _ _ _ _ _ b b' AH (proj1 Vb) Hb'L). unfold twin_iv, fsh_iv in E. injection E as E1 _. exact E1.
    + exfalso. destruct (T3 b (conj Vb HF)) as [WF0 _]. apply (NF _ WF0 eq_refl). unfold w_iv, user_iv. cbn [w_lo w_len]. rewrite (usz_fake b HF). reflexivity.
  - exfalso. destruct (LB_twin_facts W aw LB m mo b HW Hb) as (X1 & X2 & X3). unfold user_band, twin_iv in UB. cbn [fst] in UB. lia.
  - exfalso. destruct (LB_fsh_facts W aw LB m mo b HW Vb) as (X1 & X2 & X3 & _). unfold user_band, fsh_iv in UB. cbn [fst] in UB. lia.
Qed.

Lemma stk0_sp_bound : forall W ws w L RNG st LBa (m : amem) sp, ties W ws -> In w ws -> w_kind w = K_STACK -> w_lo w < ZC_BASE ->
  AHEAP AI L RNG st LBa m -> sp - w_lo w <= 8384352 -> sp <= al_top L.
Proof.
  intros W ws w L RNG st LBa m sp (_ & _ & _ & _ & _ & _ & _ & T8 & _) Hw K P AH D. rewrite (T8 w Hw K P) in D.
  destruct (AI_layout AI _ _ _ _ _ AH) as (S1 & _ & S2 & S3 & _). lia.
Qed.

End AsanWorld.
End TwinB.
