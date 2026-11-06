(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the node-shape algebra of parse_items' half-built container for the image-B walk (lane
   PItemsB of a Theorem Labs lane's image-B walk list): the slot blocks pis_slots, the open container pis_open, its transfer
   along a memory change (frame, grow, snoc), its close into a node, and the freeable shapes (pj_fdR) a refusal
   leaves, all over the kit's R representation predicates (lib/A/PRH_Reader.v).
   PROVENANCE: ported BY PATH, with a Theorem Labs lane's explicit approval (00:1xZ), from
     a working branch, sha 7fb5ff296a0c,
     file proofs/omx-clap-core/fuzz_preset/lib/B/Prog/parse_items_shape.v (1,300 lines).
   CHANGES against that donor file (every lemma not named keeps its statement and proof script but for the renames):
   (1) IMPORTS, donor lines 1-9: lib/B/Reusable/YP09 -> lib/Reusable/YP09 (this tree has no lib/B/Reusable);
       lib/Lib (PropExec MState Mem Frame), lib/Prog/PjStruct and lib/B/Prog/ReaderRes DROPPED; added lib/Reusable
       YI04 (val_mem) and YI00 (garr8), and the kit's lib/A/PRH_Reader and lib/A/PRH_Base (prh_lin). No lib/Lib import
       remains. The Zify Euclidean-division flag line is added after the imports (a Theorem Labs lane 23:38Z).
   (2) RENAMES, everywhere (the kit's R twins, PRH_Reader.v :80-206; and the lane owner PItemsB's ruling of 01:2xZ to
       use kids_blkR / keys_blkR / cap2R where a statement meets the walk's pres): pj_hdr -> pj_hdrR, pj_node ->
       pj_nodeR, pj_fd -> pj_fdR, pj_items -> pj_itemsR, pj_mems -> pj_memsR, pj_cstr -> pj_cstrR, pj_apart ->
       pj_apartR, pj_holds -> pj_holdsR, pj_foot -> pj_footR, pj_key -> pj_keyR, pf_items -> pf_itemsR, pj_fshape ->
       pj_fshapeR, pj_slots_at -> pj_slots_atR, pj_rw -> pj_rwR, pj_u64 -> rd_u64, ReaderRes kids_blk / keys_blk /
       cap2 -> kids_blkR / keys_blkR / cap2R (same bodies), ReaderRes lin -> PRH_Base.prh_lin (same body),
       ReaderRes jr_strtod -> PRH_Reader.prh_jr_strtod (pis_depth_snoc, donor lines 1285-1292).
   (3) R TWINS of the lib/Prog/PjStruct.v lemmas the donor cites (that file states them over the plain predicates):
       pis_r_combine_len, pis_r_apart_app, pis_r_items_mono, pis_r_mems_mono, pis_r_pf_mono, pis_r_pf_snoc,
       pis_r_fshape_mono, pis_r_fd_succ, pis_r_fd_mono, pis_r_items_pf, pis_r_mems_pf, pis_r_node_fd (proof scripts
       copied from PjStruct.v :148-150, 259-303, 412-572 with the renames of (2)), and pis_r_zero_u64 (PjStruct.v
       :594-596 restated: 56 zero bytes as the kit's garr8 (repeat 0 56) give rd_u64 0 at offsets 0..48).
   (4) MEMORY LEMMAS restated over the kit's mapping of the plain byte predicates (PRH_Reader.v :9-11: bytes_at m a
       (le8 v) -> val_mem m a 8 v, le4 -> val_mem m a 4, a byte list -> garr8, stk / wr_at -> writable on every
       byte, i.e. rd_rw), proofs re-derived from the kit definitions (these predicates have no address bounds):
       donor 154-161 pis_bytes_mv (garr8; drops the bounds premises 0 <= a', a' + len <= 2 ^ 64), 163-172
       pis_bytes_some (garr8), 174-186 pis_stk_mv (stk m lo (lo + n) -> rd_rw m lo n; drops 0 <= lo',
       lo' + n <= 2 ^ 64), 188-197 pis_stk_pt (stk m lo hi -> rd_rw m lo (hi - lo)), 199-207 pis_u64_mv (drops
       0 <= a', a' + 8 <= 2 ^ 64), 216-237 pis_hdr_mv (drops 0 <= p', p' + 56 <= 2 ^ 64), 250-268 pis_hdr_ty (the
       plain pj_zero m v is pj_rw m v /\ 56 zero bytes, restated as pj_rwR m v /\ pj_zeroR m v, the kit's pj_zeroR being
       the bytes only; bytes_at le4 -> val_mem 4), 270-297 pis_hdr_n (bytes_at le8 -> val_mem 8), 299-310
       pis_cstr_frame. Every DROPPED premise is an address bound the plain stk / bytes_at carried and the kit's
       predicates do not, unused by every R proof: dropping it STRENGTHENS the lemma, and it is forced, because no
       caller in this file can derive it from the kit's predicates.
   (5) BOUNDS PREMISES dropped for the same reason (strengthening): donor 361-445 pis_node_xfer (0 <= p',
       p' + 56 <= 2 ^ 64, and the matching `lia` steps of its proof), 447-461 pis_node_frame (proof steps only);
       donor 634-705 pis_items_xfer and pis_xfer: the premise ((0 < length ts) -> k' mod 8 = 0 /\ 0 <= k' /\
       k' + 56 * len <= 2 ^ 64) keeps only k' mod 8 = 0, and (o = true -> moved keys /\ (0 < length ts -> 0 <= y' /\
       y' + 8 * len <= 2 ^ 64)) keeps only the move; the proofs of pis_frame, pis_grow_arr, pis_grow_obj,
       pis_grow_kept and pis_grow_half_fd pass the shorter premises (their own statements are unchanged).
   (6) NEW: pis_items_mod8 (kids mod 8 = 0 for a non-empty pis_items): the part of the dropped pis_items_bounds
       that the kit's predicates carry; pis_frame and pis_grow_kept use it where the donor used pis_items_bounds.
   (7) pis_close (donor 926-938): its donor proof went through plain pj_open_n / PjStruct.pj_open_obj /
       pj_open_arr; the statement is unchanged but for (2), and the proof is the direct unfolding those two
       PjStruct lemmas perform (PjStruct.v :645-673), over pj_nodeR.
   (8) DROPPED (each with its reason):
       - donor 151-152 pis_mrd: it equates lib/Lib/Mem.v's mrd / wa with YP09.mbyte, the plain engine's read;
         nothing in the kit's vocabulary uses mrd.
       - donor 510-519 pis_items_bnd, 521-534 pis_mems_bnd, 536-548 pis_items_bounds: their conclusions are the
         address bounds (0 <= a, a + 56 * len <= 2 ^ 64, the same for the keys) that plain pj_rw / pj_u64 carry
         through stk / bytes_at and the kit's pj_rwR / rd_u64 do not; restating only the provable part would weaken the
         statement (its mod-8 part is pis_items_mod8, item 6).
       - donor 587-598 pis_open_n, 600-614 pj_open_n_pis, 906-924 pj_open_n_snoc, 940-951 pj_open_n_close: they
         relate pis_open to plain PjStruct.pj_open_n, which the kit's PRH_Reader has no twin of.
       - donor 772-778 pis_place_item: it concludes plain PjStruct.pj_place; the kit's node placement is the different
         predicate prhReader_at (PRH_FnReader / PRH_FnParse rd_node_okR), so there is no twin to restate it over.
   (9) FIX after the port (lane PItemsB, 2026-10-29, found by PItemsValue's PvAftv prover): donor 735-756
       pis_frame_v, 1123-1154 pis_fd_next_store and 1267-1281 pis_exit_item took the premise
       (forall x, ~ (v <= x < v + 56) -> pis_same m m' x), which is FALSE after any store into the node, because
       mbyte reads at Z_to_bv 64 x (x = v + 40 + 2 ^ 64 lies outside [v, v + 56) but reads the byte at v + 40). It
       is replaced by pis_frame's own form, over the bytes the lemma reads: pis_frame_v takes
       (forall x, pis_ifoot o kids keys (Z.of_nat (length ts)) Di x -> pis_same m m' x), and pis_fd_next_store /
       pis_exit_item take (forall x, pis_ifoot o kids keys (Z.of_nat (length ts) + 1) (Di ++ Dt) x ->
       pis_same m m' x). The new premises follow from the old ones by the new pis_ifoot_apart, so each lemma is
       STRONGER than the donor's. pis_frame_v also loses the premise Z.of_nat (length ts) <= cap, which only the
       old proof used. pis_ifoot_apart is the old proofs' apartness argument, made a lemma for the callers.
   No lemma of a released proof is cited: the lemmas used are the Stdlib's, PjTree's / PjGrammar's (lib/Spec, the
   pure model), the cgif core's YI00.garr8_mbyte, and this file's own. No Admitted, Axiom, Parameter or sorry. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_Base.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition pis_oz (o : bool) : Z := if o then 1 else 0.

Definition pis_slots (o : bool) (kids keys cap : Z) : list (Z * Z) :=
  kids_blkR kids cap ++ keys_blkR (5 + pis_oz o) keys cap.

Definition pis_apart_n (D : list (Z * Z)) (a n : Z) : Prop :=
  forall b x, In b D -> pj_holdsR b x -> ~ (a <= x < a + n).

Definition pis_ifoot (o : bool) (kids keys len : Z) (Di : list (Z * Z)) (x : Z) : Prop :=
  kids <= x < kids + 56 * len \/ (o = true /\ keys <= x < keys + 8 * len) \/
  exists b, In b Di /\ pj_holdsR b x.

Lemma pis_maxd : forall d, (d < MAXD)%nat -> (MAXD - d = S (MAXD - S d))%nat.
Proof. intros d H. lia. Qed.

Lemma pis_combine_map : forall (A B : Type) (l : list (A * B)), combine (map fst l) (map snd l) = l.
Proof. intros A B l. induction l as [|[a b] l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pis_combine_snoc : forall (A B : Type) (l1 : list A) (l2 : list B) a b, length l1 = length l2 ->
  combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  intros A B l1. induction l1 as [|x l1 IH]; intros [|y l2] a b H; cbn in *; try lia.
  - reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

Lemma pis_nodup_app_disj : forall (A : Type) (l l' : list A) a, NoDup (l ++ l') -> In a l -> In a l' -> False.
Proof.
  intros A l l' a H. apply NoDup_ListNoDup in H. revert l' a H.
  induction l as [|x l IH]; intros l' a H H1 H2; [destruct H1|].
  cbn [app] in H. inversion H as [|y r Hx Hr]; subst.
  destruct H1 as [<-|H1]; [apply Hx; apply in_or_app; right; exact H2 | exact (IH l' a Hr H1 H2)].
Qed.

Lemma pis_nodup_app : forall (A : Type) (l l' : list A), NoDup l -> NoDup l' ->
  (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
  intros A l l' H H' Hd. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup in H'.
  revert l' H H' Hd. induction l as [|x l IH]; intros l' H H' Hd; [exact H'|].
  cbn [app]. inversion H as [|y r Hx Hr]; subst. constructor.
  - intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (Hx Hin) | exact (Hd x (or_introl eq_refl) Hin)].
  - apply IH; [exact Hr | exact H' | intros a Ha; apply Hd; right; exact Ha].
Qed.

Lemma pis_nodup_l : forall (A : Type) (l l' : list A), NoDup (l ++ l') -> NoDup l.
Proof.
  intros A l l' H. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H. revert l' H.
  induction l as [|x l IH]; intros l' H; [constructor|].
  cbn [app] in H. inversion H as [|y r Hx Hr]; subst. constructor.
  - intros Hin. apply Hx. apply in_or_app. left. exact Hin.
  - exact (IH l' Hr).
Qed.

Lemma pis_nodup_r : forall (A : Type) (l l' : list A), NoDup (l ++ l') -> NoDup l'.
Proof.
  intros A l l' H. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H. revert l' H.
  induction l as [|x l IH]; intros l' H; [exact H|].
  cbn [app] in H. inversion H as [|y r Hx Hr]; subst. exact (IH l' Hr).
Qed.

Lemma pis_rest : forall (S Di Lam Lam0 : list (Z * Z)), NoDup (S ++ Di) -> incl (S ++ Di) Lam ->
  Permutation Lam (S ++ Lam0) -> incl Di Lam0.
Proof.
  intros S Di Lam Lam0 HN HI HP b Hb.
  assert (H1 : In b (S ++ Lam0)) by (apply (Permutation_in _ HP); apply HI; apply in_or_app; right; exact Hb).
  apply in_app_or in H1. destruct H1 as [H1|H1]; [|exact H1].
  exfalso. exact (pis_nodup_app_disj _ S Di b HN H1 Hb).
Qed.

Lemma pis_nodup_new : forall (S' Di Lam' Lam0 : list (Z * Z)), NoDup (map fst Lam') ->
  Permutation Lam' (S' ++ Lam0) -> incl Di Lam0 -> NoDup Di -> NoDup (S' ++ Di).
Proof.
  intros S' Di Lam' Lam0 HN HP HI HD.
  assert (H : NoDup (S' ++ Lam0)).
  { apply NoDup_ListNoDup. apply (Permutation_NoDup HP). apply (NoDup_map_inv fst). apply NoDup_ListNoDup. exact HN. }
  apply pis_nodup_app; [exact (pis_nodup_l _ _ _ H) | exact HD |].
  intros a Ha Hb. exact (pis_nodup_app_disj _ _ _ a H Ha (HI a Hb)).
Qed.

(* ---- R twins of three lib/Prog/PjStruct.v lemmas the donor cites (pj_combine_len, pj_apart_app, pj_items_mono),
   their proof scripts copied from that file and stated over the kit's pj_apartR / pj_itemsR ---- *)
Lemma pis_r_combine_len : forall (A B : Type) (l1 : list A) (l2 : list B), length l1 = length l2 ->
  length (combine l1 l2) = length l2.
Proof. intros A B l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try lia. f_equal. apply IH. lia. Qed.

Lemma pis_r_apart_app : forall A B p, pj_apartR A p -> pj_apartR B p -> pj_apartR (A ++ B) p.
Proof.
  intros A B p HA HB b x Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HA b x Hb) | exact (HB b x Hb)].
Qed.

Lemma pis_r_items_mono : forall (P Q : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall i u D1, (i < length l)%nat -> In u l -> incl D1 D ->
     P (a + 56 * Z.of_nat i) u D1 -> Q (a + 56 * Z.of_nat i) u D1) ->
  pj_itemsR P a l D -> pj_itemsR Q a l D.
Proof.
  intros P Q l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2. split; [exact E|]. split.
    + specialize (H 0%nat u D1). replace (a + 56 * Z.of_nat 0) with a in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact HP].
    + apply (IH (a + 56) D2); [|exact HR].
      intros i v D3 Hi Hv Hinc HP3.
      replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
      apply H; [cbn; lia | right; exact Hv | subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb | exact HP3].
Qed.

Lemma pis_items_shift : forall (P Q : Z -> jv -> list (Z * Z) -> Prop) l a a' D,
  (forall i u D1, (i < length l)%nat -> In u l -> incl D1 D ->
     P (a + 56 * Z.of_nat i) u D1 -> Q (a' + 56 * Z.of_nat i) u D1) ->
  pj_itemsR P a l D -> pj_itemsR Q a' l D.
Proof.
  intros P Q l. induction l as [|u r IH]; intros a a' D H Hl; cbn [pj_itemsR] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2. split; [exact E|]. split.
    + specialize (H 0%nat u D1).
      replace (a + 56 * Z.of_nat 0) with a in H by lia. replace (a' + 56 * Z.of_nat 0) with a' in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact HP].
    + apply (IH (a + 56) (a' + 56) D2); [|exact HR].
      intros i v D3 Hi Hv Hinc HP3.
      replace (a' + 56 + 56 * Z.of_nat i) with (a' + 56 * Z.of_nat (S i)) by lia.
      replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 by lia.
      apply H; [cbn; lia | right; exact Hv | subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb | exact HP3].
Qed.

Lemma pis_items_in : forall (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a D,
  (forall a u D1, In u l -> P a u D1 -> forall b, In b D1 -> Q b) ->
  pj_itemsR P a l D -> forall b, In b D -> Q b.
Proof.
  intros P Q l. induction l as [|u r IH]; intros a D H Hl b Hb; cbn [pj_itemsR] in Hl.
  - subst D. destruct Hb.
  - destruct Hl as (D1 & D2 & E & HP & HR). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + exact (H a u D1 (or_introl eq_refl) HP b Hb).
    + apply (IH (a + 56) D2); [|exact HR|exact Hb]. intros a' u' D3 Hu. apply H. right. exact Hu.
Qed.

Lemma pis_items_snoc : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D t Dt,
  pj_itemsR P a l D -> P (a + 56 * Z.of_nat (length l)) t Dt -> pj_itemsR P a (l ++ [t]) (D ++ Dt).
Proof.
  intros P l. induction l as [|u r IH]; intros a D t Dt H HP; cbn [pj_itemsR app length] in *.
  - subst D. exists Dt, []. replace (a + 56 * Z.of_nat 0) with a in HP by lia.
    split; [rewrite app_nil_r; reflexivity|]. split; [exact HP | reflexivity].
  - destruct H as (D1 & D2 & E & H1 & H2). exists D1, (D2 ++ Dt).
    split; [subst D; rewrite <- app_assoc; reflexivity|]. split; [exact H1|].
    apply IH; [exact H2|].
    replace (a + 56 + 56 * Z.of_nat (length r)) with (a + 56 * Z.of_nat (S (length r))) by lia. exact HP.
Qed.

Section S.
Variable segs : list Segment.

Definition pis_same (m m' : word -> option byte) (x : Z) : Prop :=
  mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x).

Definition pis_moved (m m' : word -> option byte) (src dst n : Z) : Prop :=
  forall i, 0 <= i < n -> mbyte segs m' (dst + i) = mbyte segs m (src + i).

Definition pis_items (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : bool) (kids keys : Z)
    (ts : list jv) (ns : list (list Z)) (Di : list (Z * Z)) : Prop :=
  if o then length ns = length ts /\ pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys (combine ns ts) Di
  else pj_itemsR (pj_nodeR segs m lblk) kids ts Di.

Definition pis_open (m : word -> option byte) (lblk : Z -> Z -> Prop) (v : Z) (o : bool)
    (num kids keys cap nf : Z) (ts : list jv) (ns : list (list Z)) (Di : list (Z * Z)) : Prop :=
  NoDup (pis_slots o kids keys cap ++ Di) /\ pj_apartR (pis_slots o kids keys cap ++ Di) v /\
  pj_hdrR segs m v (5 + pis_oz o) num 0 kids keys nf cap /\ pj_slots_atR lblk (5 + pis_oz o) kids keys nf cap /\
  (o = false -> keys = 0) /\ pis_items m lblk o kids keys ts ns Di.

(* ---- R twins of the lib/Prog/PjStruct.v lemmas the donor cites over segs (pj_mems_mono, pf_items_mono,
   pf_items_snoc, pj_fshape_mono, pj_fd_succ, pj_fd_mono, pj_items_pf, pj_mems_pf, pj_node_fd, pj_zero_u64), their
   proof scripts copied from that file and stated over the kit's R predicates ---- *)
Lemma pis_r_mems_mono : forall m lblk m' lblk' (P Q : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall i nm u x k D1, (i < length l)%nat -> In (nm, u) l -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk' x k nm /\ Q (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m' lblk' Q a ka l D.
Proof.
  intros m lblk m' lblk' P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
    assert (G : rd_u64 segs m' ka x /\ pj_cstrR segs m' lblk' x k nm /\ Q a u D1).
    { specialize (H 0%nat nm u x k D1).
      replace (ka + 8 * Z.of_nat 0) with ka in H by lia. replace (a + 56 * Z.of_nat 0) with a in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; left; reflexivity
               | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hx | exact Hc | exact HP]. }
    destruct G as (Hx' & Hc' & HQ).
    exists x, k, D1, D2. split; [exact E|]. split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HQ|].
    apply (IH (a + 56) (ka + 8) D2); [|exact HR].
    intros i nm' v x' k' D3 Hi Hv Hxk Hinc Hx3 Hc3 HP3.
    replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx3 |- * by lia.
    replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
    apply H; [cbn; lia | right; exact Hv | subst D; right; apply in_or_app; right; exact Hxk
             | subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb
             | exact Hx3 | exact Hc3 | exact HP3].
Qed.

Lemma pis_r_pf_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
  intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *.
  - exact Hp.
  - destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
    split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.

Lemma pis_r_pf_snoc : forall m lblk (P : Z -> list (Z * Z) -> Prop) ks n a ka D1 Dk Dt,
  pf_itemsR segs m lblk P ks a ka n D1 -> pj_keyR segs m lblk ks (ka + 8 * Z.of_nat n) Dk ->
  P (a + 56 * Z.of_nat n) Dt -> pf_itemsR segs m lblk P ks a ka (S n) (D1 ++ Dk ++ Dt).
Proof.
  intros m lblk P ks n. induction n as [|n IH]; intros a ka D1 Dk Dt H Hk HP.
  - cbn [pf_itemsR] in H |- *. subst D1. exists Dk, Dt, [].
    replace (ka + 8 * Z.of_nat 0) with ka in Hk by lia. replace (a + 56 * Z.of_nat 0) with a in HP by lia.
    split; [rewrite app_nil_r; reflexivity|]. split; [exact Hk|]. split; [exact HP | reflexivity].
  - cbn [pf_itemsR] in H. destruct H as (Dk0 & D10 & D20 & E & Hk0 & HP0 & HR).
    cbn [pf_itemsR]. exists Dk0, D10, (D20 ++ Dk ++ Dt).
    split; [subst D1; rewrite <- !app_assoc; reflexivity|]. split; [exact Hk0|]. split; [exact HP0|].
    apply (IH (a + 56) (ka + 8) D20 Dk Dt HR).
    + replace (ka + 8 + 8 * Z.of_nat n) with (ka + 8 * Z.of_nat (S n)) by lia. exact Hk.
    + replace (a + 56 + 56 * Z.of_nat n) with (a + 56 * Z.of_nat (S n)) by lia. exact HP.
Qed.

Lemma pis_r_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
  intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  exact (H _ _ _ _ _ H6).
Qed.

Lemma pis_r_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
  intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
  - eapply (pis_r_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
  - eapply (pis_r_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di Hi. cbv beta in Hi |- *.
    apply (pis_r_pf_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi].
    intros a D1 H1. exact (IH a D1 H1).
Qed.

Lemma pis_r_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
  intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|].
  apply pis_r_fd_succ. apply IH. exact H.
Qed.

Lemma pis_r_items_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
    split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pis_r_mems_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
    split; [exact E|].
    split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
    split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pis_r_node_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (depth t) p D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H;
    cbn [pj_nodeR] in H.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fdR]. unfold pj_fshapeR.
    split; [exact Hn|]. split; [exact Ha|].
    assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
    { rewrite En, Nat2Z.id. apply (pis_r_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
      intros a u D1 Hu HP. rewrite Forall_forall in IH.
      apply (pis_r_fd_mono m lblk (depth u)); [|exact (IH u Hu m lblk a D1 HP)].
      pose proof (depth_item items u Hu). lia. }
    destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
    + subst cap.
      exists (tag (JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|]. exact HI.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fdR]. unfold pj_fshapeR.
    split; [exact Hn|]. split; [exact Ha|].
    destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
    + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia].
      cbn [pj_memsR] in Hi.
      exists (tag (JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|].
      cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
      split; [subst D; cbn [app]; apply Permutation_refl|].
      cbv beta. rewrite En, Nat2Z.id. apply (pis_r_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
      intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (pis_r_fd_mono m lblk (depth u)); [|exact (IH m lblk a D1 HP)].
      pose proof (depth_member members nm u Hu). lia.
Qed.

Lemma pis_r_zero_u64 : forall m p off, garr8 segs m p (repeat 0 56) -> 0 <= off <= 48 ->
  rd_u64 segs m (p + off) 0.
Proof.
  intros m p off H Ho. split; [lia|]. intros k Hk.
  assert (Hj : (Z.to_nat off + k < length (repeat 0 56))%nat) by (rewrite repeat_length; lia).
  pose proof (garr8_mbyte segs m p (repeat 0 56) (Z.to_nat off + k) H Hj) as R.
  rewrite nth_repeat in R.
  replace (p + off + Z.of_nat k) with (p + Z.of_nat (Z.to_nat off + k)) by lia. rewrite R.
  unfold YO0f.le_byte. change (0 mod 2 ^ (8 * Z.of_nat 8)) with 0. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma pis_bytes_mv : forall m m' a a' bs,
  garr8 segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a' + i) = mbyte segs m (a + i)) ->
  garr8 segs m' a' bs.
Proof.
  intros m m' a a' bs H E j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
  intros k Hk. replace (a' + Z.of_nat j + Z.of_nat k) with (a' + (Z.of_nat j + Z.of_nat k)) by lia.
  rewrite E by lia. replace (a + (Z.of_nat j + Z.of_nat k)) with (a + Z.of_nat j + Z.of_nat k) by lia.
  exact (Hv k Hk).
Qed.

Lemma pis_bytes_some : forall m a bs x, garr8 segs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mbyte segs m x = Some b.
Proof.
  intros m a bs x H Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (garr8_mbyte segs m a bs _ H Hi) as R. replace (a + Z.of_nat (Z.to_nat (x - a))) with x in R by lia.
  exists (Z_to_bv 8 (nth (Z.to_nat (x - a)) bs 0)). exact R.
Qed.

Lemma pis_stk_mv : forall m m' lo lo' n,
  rd_rw segs m lo n ->
  (forall i, 0 <= i < n -> mbyte segs m' (lo' + i) = mbyte segs m (lo + i)) ->
  (forall i, 0 <= i < n -> writable_at segs m (lo + i) -> writable_at segs m' (lo' + i)) ->
  rd_rw segs m' lo' n.
Proof.
  intros m m' lo lo' n H E W a Ha.
  pose proof (W (a - lo') ltac:(lia) (H (lo + (a - lo')) ltac:(lia))) as W1.
  replace (lo' + (a - lo')) with a in W1 by lia. exact W1.
Qed.

Lemma pis_stk_pt : forall m m' lo hi, rd_rw segs m lo (hi - lo) ->
  (forall a, lo <= a < hi -> (writable_at segs m a -> writable_at segs m' a) /\
     (mbyte segs m' a = mbyte segs m a \/ exists b, mbyte segs m' a = Some b)) ->
  rd_rw segs m' lo (hi - lo).
Proof.
  intros m m' lo hi H E a Ha. destruct (E a ltac:(lia)) as [W _]. exact (W (H a Ha)).
Qed.

Lemma pis_u64_mv : forall m m' a a' v,
  rd_u64 segs m a v ->
  (forall i, 0 <= i < 8 -> mbyte segs m' (a' + i) = mbyte segs m (a + i)) ->
  rd_u64 segs m' a' v.
Proof.
  intros m m' a a' v (Hv & B) E. split; [exact Hv|].
  intros k Hk. rewrite E by lia. exact (B k Hk).
Qed.

Lemma pis_u64_frame : forall m m' a v, rd_u64 segs m a v ->
  (forall x, a <= x < a + 8 -> mbyte segs m' x = mbyte segs m x) -> rd_u64 segs m' a v.
Proof.
  intros m m' a v H E. apply (pis_u64_mv m m' a a); [exact H|]. intros i Hi. apply E. lia.
Qed.

Lemma pis_hdr_mv : forall m m' p p' ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap -> p' mod 8 = 0 ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (p' + i) = mbyte segs m (p + i)) ->
  (forall i, 0 <= i < 56 -> writable_at segs m (p + i) -> writable_at segs m' (p' + i)) ->
  pj_hdrR segs m' p' ty num str kids keys n cap.
Proof.
  intros m m' p p' ty num str kids keys n cap
    ((Ha & Hs) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) Ha' E W.
  assert (F : forall off nb w, val_mem segs m (p + off) nb w -> 0 <= off -> off + Z.of_nat nb <= 56 ->
    val_mem segs m' (p' + off) nb w).
  { intros off nb w B Ho Hc k Hk. replace (p' + off + Z.of_nat k) with (p' + (off + Z.of_nat k)) by lia.
    rewrite E by lia. replace (p + (off + Z.of_nat k)) with (p + off + Z.of_nat k) by lia. exact (B k Hk). }
  split; [split; [exact Ha' | exact (pis_stk_mv m m' p p' 56 Hs E W)]|].
  split; [split; [exact T0 | rewrite <- (Z.add_0_r p'); apply F; [rewrite Z.add_0_r; exact T1 | lia | lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | lia]].
Qed.

Lemma pis_hdr_frame : forall m m' p ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> pis_same m m' x) ->
  pj_hdrR segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap H E. pose proof H as ((Ha & _) & _).
  apply (pis_hdr_mv m m' p p); [exact H | exact Ha | |].
  - intros i Hi. exact (proj1 (E (p + i) ltac:(lia))).
  - intros i Hi. exact (proj2 (E (p + i) ltac:(lia))).
Qed.

Lemma pis_hdr_ty : forall m m' v ty,
  pj_rwR segs m v /\ pj_zeroR segs m v -> 0 <= ty < 2 ^ 32 -> val_mem segs m' v 4 ty ->
  (forall x, v + 4 <= x < v + 56 -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, v <= x < v + 56 -> writable_at segs m x -> writable_at segs m' x) ->
  pj_hdrR segs m' v ty 0 0 0 0 0 0.
Proof.
  intros m m' v ty ((Ha & Hs) & Hz) Ht B E W.
  assert (F : forall off, 8 <= off <= 48 -> rd_u64 segs m' (v + off) 0).
  { intros off Ho. apply (pis_u64_frame m m'); [apply (pis_r_zero_u64 m v off Hz); lia|].
    intros x Hx. apply E. lia. }
  split.
  { split; [exact Ha|]. intros a Haa. apply W; [lia|]. apply Hs. exact Haa. }
  split; [split; [exact Ht | exact B]|].
  split; [apply F; lia|]. split; [apply F; lia|]. split; [apply F; lia|].
  split; [apply F; lia|]. split; [apply F; lia|]. apply F; lia.
Qed.

Lemma pis_hdr_n : forall m m' v ty num str kids keys n cap n',
  pj_hdrR segs m v ty num str kids keys n cap -> 0 <= n' < 2 ^ 64 ->
  val_mem segs m' (v + 40) 8 n' ->
  (forall x, v <= x < v + 56 -> ~ (v + 40 <= x < v + 48) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, v <= x < v + 56 -> writable_at segs m x -> writable_at segs m' x) ->
  pj_hdrR segs m' v ty num str kids keys n' cap.
Proof.
  intros m m' v ty num str kids keys n cap n' ((Ha & Hs) & (T0 & T1) & HN & HS & HK & HY & _ & HC) Hn B E W.
  assert (F : forall off w, rd_u64 segs m (v + off) w -> 0 <= off -> off + 8 <= 40 \/ 48 <= off ->
    off + 8 <= 56 -> rd_u64 segs m' (v + off) w).
  { intros off w Hw Ho Ho1 Ho2. apply (pis_u64_frame m m'); [exact Hw|]. intros x Hx. apply E; lia. }
  split.
  { split; [exact Ha|]. intros a Haa. apply W; [lia|]. apply Hs. exact Haa. }
  split.
  { split; [exact T0|]. intros k Hk. rewrite E by lia. exact (T1 k Hk). }
  split; [apply F; [exact HN | lia | lia | lia]|].
  split; [apply F; [exact HS | lia | lia | lia]|].
  split; [apply F; [exact HK | lia | lia | lia]|].
  split; [apply F; [exact HY | lia | lia | lia]|].
  split; [split; [exact Hn | exact B]|].
  apply F; [exact HC | lia | lia | lia].
Qed.

Lemma pis_cstr_frame : forall m lblk m' lblk' a k s,
  pj_cstrR segs m lblk a k s -> lblk' a k ->
  (forall x, pj_holdsR (a, k) x -> mbyte segs m' x = mbyte segs m x) ->
  pj_cstrR segs m' lblk' a k s.
Proof.
  intros m lblk m' lblk' a k s (Hl & Hk & Hn & Hf & Hb) Hl' E.
  split; [exact Hl'|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Hf|].
  apply (pis_bytes_mv m m' a a); [exact Hb |].
  intros i Hi. apply E. unfold pj_holdsR; cbn [fst snd].
  rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Lemma pis_node_rw : forall m lblk p t D, pj_nodeR segs m lblk p t D -> pj_rwR segs m p.
Proof.
  intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _); exact (proj1 Hh).
Qed.

Lemma pis_node_apart : forall m lblk p t D, pj_nodeR segs m lblk p t D -> pj_apartR D p.
Proof. intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H; exact (proj1 (proj2 H)). Qed.

Lemma pis_mems_in : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> forall b, In b D1 -> Q b) ->
  (forall x k nm, pj_cstrR segs m lblk x k nm -> Q (x, k)) ->
  pj_memsR segs m lblk P a ka l D -> forall b, In b D -> Q b.
Proof.
  intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H HC Hl b Hb; cbn [pj_memsR] in Hl.
  - subst D. destruct Hb.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR). subst D. destruct Hb as [Hb|Hb].
    + subst b. exact (HC x k nm Hc).
    + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * exact (H a u D1 (ex_intro _ nm (or_introl eq_refl)) HP b Hb).
      * apply (IH (a + 56) (ka + 8) D2); [|exact HC|exact HR|exact Hb].
        intros a' u' D3 (nm' & Hu). apply H. exists nm'. right. exact Hu.
Qed.

Lemma pis_node_lblk : forall t m lblk p D, pj_nodeR segs m lblk p t D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H b Hb;
    cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb').
  - destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
  - destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
  - destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
  - destruct Hb' as (_ & _ & _ & _ & _ & k & (Hl & _) & ED). subst D. destruct Hb as [<-|[]]. exact Hl.
  - destruct Hb' as (_ & _ & _ & _ & k & (Hl & _) & ED). subst D. destruct Hb as [<-|[]]. exact Hl.
  - destruct Hb' as (_ & _ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec. destruct Hb as [<-|[]].
      destruct Hcap as [(Hc0 & _)|(_ & Hl)]; [lia | exact Hl].
    + apply (pis_items_in (pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) items kids Di); [|exact Hi|exact Hb].
      intros a u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. exact (IH u Hu m lblk a D1 HP b' Hb').
  - destruct Hb' as (_ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
      destruct Hcap as [(Hc0 & _)|(_ & L0 & L1)]; [lia|].
      destruct Hb as [<-|[<-|[]]]; [exact L0 | exact L1].
    + apply (pis_mems_in m lblk (pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) members kids keys Di);
        [| |exact Hi|exact Hb].
      * intros a u D1 (nm & Hu) HP b' Hb'. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu).
        cbn [snd] in IH. exact (IH m lblk a D1 HP b' Hb').
      * intros x k nm (Hl & _). exact Hl.
Qed.

Lemma pis_node_xfer : forall t m lblk m' lblk' p p' D,
  pj_nodeR segs m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> pis_same m m' x) ->
  p' mod 8 = 0 ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (p' + i) = mbyte segs m (p + i)) ->
  (forall i, 0 <= i < 56 -> writable_at segs m (p + i) -> writable_at segs m' (p' + i)) ->
  pj_apartR D p' ->
  pj_nodeR segs m' lblk' p' t D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m lblk m' lblk' p p' D H HL HM Ha' E W Hap; cbn [pj_nodeR] in H |- *;
    destruct H as (Hn & _ & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Hap|]); exists num, str, kids, keys, n, cap;
    (split; [exact (pis_hdr_mv m m' p p' _ num str kids keys n cap Hh Ha' E W)|]);
    assert (HM1 : forall y, (exists b, In b D /\ pj_holdsR b y) -> mbyte segs m' y = mbyte segs m y)
      by (intros y Hy; exact (proj1 (HM y Hy)));
    assert (HM2 : forall y, (exists b, In b D /\ pj_holdsR b y) -> writable_at segs m y -> writable_at segs m' y)
      by (intros y Hy; exact (proj2 (HM y Hy))).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pis_cstr_frame m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx. apply HM1. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pis_cstr_frame m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx. apply HM1. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0)]; [left; exact Hcap | right; split; [exact Hp | apply HL; apply (Hin Hp)]]|].
    exists Di. split; [exact ED|].
    apply (pis_r_items_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk')); [|exact Hi].
    intros i u D1 Hil Hu Hinc HP.
    assert (Hp : 0 < cap) by lia.
    pose proof (pis_node_rw m lblk _ u D1 HP) as (Har & _).
    rewrite Forall_forall in IH.
    apply (IH u Hu m lblk m' lblk' _ _ D1 HP).
    + intros a k Hak. apply HL. apply HDi. apply Hinc. exact Hak.
    + intros x (b & Hb & Hx). apply HM. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
    + exact Har.
    + intros j Hj. apply HM1. exists (kids, 56 * cap).
      split; [apply (Hin Hp) | unfold pj_holdsR; cbn [fst snd]; lia].
    + intros j Hj Hw. apply HM2; [|exact Hw]. exists (kids, 56 * cap).
      split; [apply (Hin Hp) | unfold pj_holdsR; cbn [fst snd]; lia].
    + exact (pis_node_apart m lblk _ u D1 HP).
  - destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0 & L1)];
            [left; exact Hcap | right; split; [exact Hp|]; split; [apply HL; apply (proj1 (Hin Hp)) | apply HL; apply (proj2 (Hin Hp))]]|].
    exists Di. split; [exact ED|].
    apply (pis_r_mems_mono m lblk m' lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk')); [|exact Hi].
    intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
    assert (Hp : 0 < cap) by lia.
    split; [|split].
    + apply (pis_u64_frame m m'); [exact Hx|]. intros y Hy. apply HM1. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holdsR; cbn [fst snd]; lia].
    + apply (pis_cstr_frame m lblk m' lblk'); [exact Hcs | apply HL; apply HDi; exact Hxk |].
      intros y Hy. apply HM1. exists (x, k). split; [apply HDi; exact Hxk | exact Hy].
    + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      pose proof (pis_node_rw m lblk _ u D1 HP) as (Har & _).
      apply (IH m lblk m' lblk' _ _ D1 HP).
      * intros a k' Hak. apply HL. apply HDi. apply Hinc. exact Hak.
      * intros y (b & Hb & Hy). apply HM. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
      * exact Har.
      * intros j Hj. apply HM1. exists (kids, 56 * cap).
        split; [apply (proj1 (Hin Hp)) | unfold pj_holdsR; cbn [fst snd]; lia].
      * intros j Hj Hw. apply HM2; [|exact Hw]. exists (kids, 56 * cap).
        split; [apply (proj1 (Hin Hp)) | unfold pj_holdsR; cbn [fst snd]; lia].
      * exact (pis_node_apart m lblk _ u D1 HP).
Qed.

Lemma pis_node_frame : forall t m lblk m' lblk' p D,
  pj_nodeR segs m lblk p t D -> (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x, pj_footR p D x -> pis_same m m' x) -> pj_nodeR segs m' lblk' p t D.
Proof.
  intros t m lblk m' lblk' p D H HL HM.
  pose proof (pis_node_rw m lblk p t D H) as (Ha & _).
  apply (pis_node_xfer t m lblk m' lblk' p p D H HL).
  - intros x Hx. apply HM. right. exact Hx.
  - exact Ha.
  - intros i Hi. refine (proj1 (HM (p + i) _)). left. lia.
  - intros i Hi. refine (proj2 (HM (p + i) _)). left. lia.
  - exact (pis_node_apart m lblk p t D H).
Qed.

Lemma pis_mems_shift : forall m lblk m' lblk' (P Q : Z -> jv -> list (Z * Z) -> Prop) l a ka a' ka' D,
  (forall i nm u x k D1, (i < length l)%nat -> In (nm, u) l -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka' + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk' x k nm /\ Q (a' + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m' lblk' Q a' ka' l D.
Proof.
  intros m lblk m' lblk' P Q l. induction l as [|[nm u] r IH]; intros a ka a' ka' D H Hl; cbn [pj_memsR] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
    assert (G : rd_u64 segs m' ka' x /\ pj_cstrR segs m' lblk' x k nm /\ Q a' u D1).
    { specialize (H 0%nat nm u x k D1).
      replace (ka + 8 * Z.of_nat 0) with ka in H by lia. replace (a + 56 * Z.of_nat 0) with a in H by lia.
      replace (ka' + 8 * Z.of_nat 0) with ka' in H by lia. replace (a' + 56 * Z.of_nat 0) with a' in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; left; reflexivity
               | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hx | exact Hc | exact HP]. }
    destruct G as (Hx' & Hc' & HQ).
    exists x, k, D1, D2. split; [exact E|]. split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HQ|].
    apply (IH (a + 56) (ka + 8) (a' + 56) (ka' + 8) D2); [|exact HR].
    intros i nm' w x' k' D3 Hi Hv Hxk Hinc Hx3 Hc3 HP3.
    replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx3 by lia.
    replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 by lia.
    replace (ka' + 8 + 8 * Z.of_nat i) with (ka' + 8 * Z.of_nat (S i)) by lia.
    replace (a' + 56 + 56 * Z.of_nat i) with (a' + 56 * Z.of_nat (S i)) by lia.
    apply H; [cbn; lia | right; exact Hv | subst D; right; apply in_or_app; right; exact Hxk
             | subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb
             | exact Hx3 | exact Hc3 | exact HP3].
Qed.

Lemma pis_mems_snoc : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D nm t x k Dt,
  pj_memsR segs m lblk P a ka l D -> rd_u64 segs m (ka + 8 * Z.of_nat (length l)) x ->
  pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat (length l)) t Dt ->
  pj_memsR segs m lblk P a ka (l ++ [(nm, t)]) (D ++ (x, k) :: Dt).
Proof.
  intros m lblk P l. induction l as [|[nm0 u] r IH]; intros a ka D nm t x k Dt H Hx Hc HP;
    cbn [pj_memsR app length] in *.
  - subst D. replace (ka + 8 * Z.of_nat 0) with ka in Hx by lia.
    replace (a + 56 * Z.of_nat 0) with a in HP by lia.
    exists x, k, Dt, []. split; [rewrite app_nil_r; reflexivity|].
    split; [exact Hx|]. split; [exact Hc|]. split; [exact HP | reflexivity].
  - destruct H as (x0 & k0 & D1 & D2 & E & Hx0 & Hc0 & HP0 & HR). exists x0, k0, D1, (D2 ++ (x, k) :: Dt).
    split; [subst D; cbn [app]; rewrite <- app_assoc; reflexivity|].
    split; [exact Hx0|]. split; [exact Hc0|]. split; [exact HP0|].
    apply IH; [exact HR | | exact Hc |].
    + replace (ka + 8 + 8 * Z.of_nat (length r)) with (ka + 8 * Z.of_nat (S (length r))) by lia. exact Hx.
    + replace (a + 56 + 56 * Z.of_nat (length r)) with (a + 56 * Z.of_nat (S (length r))) by lia. exact HP.
Qed.

Lemma pis_items_mod8 : forall m lblk o kids keys ts ns Di,
  pis_items m lblk o kids keys ts ns Di -> (0 < length ts)%nat -> kids mod 8 = 0.
Proof.
  intros m lblk o kids keys ts ns Di H Hl. destruct ts as [|t ts']; [cbn in Hl; lia|].
  destruct o; unfold pis_items in H.
  - destruct H as (Hn & Hm). destruct ns as [|nm ns']; [cbn in Hn; lia|].
    cbn [combine pj_memsR] in Hm. destruct Hm as (x & k & D1 & D2 & _ & _ & _ & HP & _).
    exact (proj1 (pis_node_rw m lblk kids t D1 HP)).
  - cbn [pj_itemsR] in H. destruct H as (D1 & D2 & _ & HP & _).
    exact (proj1 (pis_node_rw m lblk kids t D1 HP)).
Qed.

Lemma pis_items_lblk : forall m lblk o kids keys ts ns Di,
  pis_items m lblk o kids keys ts ns Di -> forall a k, In (a, k) Di -> lblk a k.
Proof.
  intros m lblk o kids keys ts ns Di H a k Hak. destruct o; unfold pis_items in H.
  - destruct H as (_ & Hm).
    exact (pis_mems_in m lblk (pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) _ kids keys Di
      (fun a' u D1 _ HP b Hb => pis_node_lblk u m lblk a' D1 HP b Hb) (fun x k' nm Hc => proj1 Hc) Hm (a, k) Hak).
  - exact (pis_items_in (pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) ts kids Di
      (fun a' u D1 _ HP b Hb => pis_node_lblk u m lblk a' D1 HP b Hb) H (a, k) Hak).
Qed.

Lemma pis_slots_lblk : forall lblk o kids keys nf cap, 0 <= cap ->
  pj_slots_atR lblk (5 + pis_oz o) kids keys nf cap -> forall a k, In (a, k) (pis_slots o kids keys cap) -> lblk a k.
Proof.
  intros lblk o kids keys nf cap Hc (_ & _ & _ & Hcp) a k Hak. unfold pis_slots, kids_blkR, keys_blkR in Hak.
  destruct (Z.eq_dec cap 0) as [E0|E0]; [subst cap; cbn in Hak; destruct Hak|].
  destruct (Hcp ltac:(lia)) as (L0 & L1).
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; exact E0). rewrite Ec in Hak.
  destruct o; cbn in Hak.
  - destruct Hak as [Hq|[Hq|[]]]; injection Hq as <- <-; [exact L0 | apply L1; reflexivity].
  - destruct Hak as [Hq|[]]. injection Hq as <- <-. exact L0.
Qed.

Lemma pis_slots_at_mv : forall lblk lblk' o kids keys nf nf' cap,
  pj_slots_atR lblk (5 + pis_oz o) kids keys nf cap -> nf' <= cap -> 0 <= cap ->
  (forall a k, In (a, k) (pis_slots o kids keys cap) -> lblk' a k) ->
  pj_slots_atR lblk' (5 + pis_oz o) kids keys nf' cap.
Proof.
  intros lblk lblk' o kids keys nf nf' cap (Ht & (Hn & Hc) & Hc0 & Hcp) Hle Hc0' HL.
  split; [exact Ht|]. split; [lia|]. split; [exact Hc0|].
  intros Hp. assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split.
  - apply HL. unfold pis_slots, kids_blkR. rewrite Ec. left. reflexivity.
  - intros Ht6. apply HL. unfold pis_slots, kids_blkR, keys_blkR. rewrite Ec. destruct o; cbn [pis_oz] in Ht6; [|lia].
    cbn. right. left. reflexivity.
Qed.

Lemma pis_open_lblk : forall m lblk v o num kids keys cap nf ts ns Di,
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  forall a k, In (a, k) (pis_slots o kids keys cap ++ Di) -> lblk a k.
Proof.
  intros m lblk v o num kids keys cap nf ts ns Di (_ & _ & Hh & Hs & _ & Hi) a k Hak.
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hc0 & _)).
  apply in_app_or in Hak. destruct Hak as [Hak|Hak].
  - exact (pis_slots_lblk lblk o kids keys nf cap ltac:(lia) Hs a k Hak).
  - exact (pis_items_lblk m lblk o kids keys ts ns Di Hi a k Hak).
Qed.

Lemma pis_open_incl : forall m Lam v o num kids keys cap nf ts ns Di,
  pis_open m (prh_lin Lam) v o num kids keys cap nf ts ns Di -> incl (pis_slots o kids keys cap ++ Di) Lam.
Proof.
  intros m Lam v o num kids keys cap nf ts ns Di H [a k] Hb.
  exact (pis_open_lblk m (prh_lin Lam) v o num kids keys cap nf ts ns Di H a k Hb).
Qed.

Lemma pis_items_xfer : forall m lblk m' lblk' o kids keys k' y' ts ns Di,
  pis_items m lblk o kids keys ts ns Di ->
  (forall a k, In (a, k) Di -> lblk' a k) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_moved m m' kids k' (56 * Z.of_nat (length ts)) ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m (kids + i) -> writable_at segs m' (k' + i)) ->
  ((0 < length ts)%nat -> k' mod 8 = 0) ->
  (k' = kids \/ pis_apart_n Di k' (56 * Z.of_nat (length ts))) ->
  (o = true -> pis_moved m m' keys y' (8 * Z.of_nat (length ts))) ->
  pis_items m' lblk' o k' y' ts ns Di.
Proof.
  intros m lblk m' lblk' o kids keys k' y' ts ns Di H HL HM Hmv HW Hb Hap Hy.
  assert (G : forall i u D1, (i < length ts)%nat -> incl D1 Di ->
     pj_nodeR segs m lblk (kids + 56 * Z.of_nat i) u D1 -> pj_nodeR segs m' lblk' (k' + 56 * Z.of_nat i) u D1).
  { intros i u D1 Hi Hinc HP.
    pose proof (Hb ltac:(lia)) as Hk8.
    apply (pis_node_xfer u m lblk m' lblk' _ _ D1 HP).
    - intros a k Hak. apply HL. apply Hinc. exact Hak.
    - intros x (b & Hb' & Hx). apply HM. exists b. split; [apply Hinc; exact Hb' | exact Hx].
    - replace (k' + 56 * Z.of_nat i) with (k' + (7 * Z.of_nat i) * 8) by lia. rewrite Z_mod_plus_full. exact Hk8.
    - intros j Hj. replace (k' + 56 * Z.of_nat i + j) with (k' + (56 * Z.of_nat i + j)) by lia.
      replace (kids + 56 * Z.of_nat i + j) with (kids + (56 * Z.of_nat i + j)) by lia. apply Hmv. lia.
    - intros j Hj Hw. replace (k' + 56 * Z.of_nat i + j) with (k' + (56 * Z.of_nat i + j)) by lia.
      apply HW; [lia|]. replace (kids + (56 * Z.of_nat i + j)) with (kids + 56 * Z.of_nat i + j) by lia. exact Hw.
    - destruct Hap as [->|Hap].
      + exact (pis_node_apart m lblk _ u D1 HP).
      + intros b x Hb' Hx Hx'. apply (Hap b x (Hinc b Hb') Hx). lia. }
  destruct o; unfold pis_items in H |- *.
  - destruct H as (Hl & Hm). split; [exact Hl|].
    pose proof (Hy eq_refl) as Hym.
    apply (pis_mems_shift m lblk m' lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') _ kids keys k' y' Di);
      [|exact Hm].
    intros i nm u x k D1 Hi Hu Hxk Hinc Hx Hc HP.
    rewrite (pis_r_combine_len _ _ ns ts Hl) in Hi.
    split; [|split].
    + apply (pis_u64_mv m m' (keys + 8 * Z.of_nat i)); [exact Hx |].
      intros j Hj. replace (y' + 8 * Z.of_nat i + j) with (y' + (8 * Z.of_nat i + j)) by lia.
      replace (keys + 8 * Z.of_nat i + j) with (keys + (8 * Z.of_nat i + j)) by lia. apply Hym. lia.
    + apply (pis_cstr_frame m lblk m' lblk'); [exact Hc | apply HL; exact Hxk |].
      intros z Hz. exact (proj1 (HM z (ex_intro _ (x, k) (conj Hxk Hz)))).
    + exact (G i u D1 Hi Hinc HP).
  - apply (pis_items_shift (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') ts kids k' Di); [|exact H].
    intros i u D1 Hi Hu Hinc HP. exact (G i u D1 Hi Hinc HP).
Qed.

Lemma pis_xfer : forall m lblk m' lblk' v o num kids keys cap nf ts ns Di num' k' y' cap' nf',
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  pj_hdrR segs m' v (5 + pis_oz o) num' 0 k' y' nf' cap' ->
  pj_slots_atR lblk' (5 + pis_oz o) k' y' nf' cap' ->
  (o = false -> y' = 0) ->
  NoDup (pis_slots o k' y' cap' ++ Di) -> pj_apartR (pis_slots o k' y' cap') v ->
  (forall a k, In (a, k) Di -> lblk' a k) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_moved m m' kids k' (56 * Z.of_nat (length ts)) ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m (kids + i) -> writable_at segs m' (k' + i)) ->
  ((0 < length ts)%nat -> k' mod 8 = 0) ->
  (k' = kids \/ pis_apart_n Di k' (56 * Z.of_nat (length ts))) ->
  (o = true -> pis_moved m m' keys y' (8 * Z.of_nat (length ts))) ->
  pis_open m' lblk' v o num' k' y' cap' nf' ts ns Di.
Proof.
  intros m lblk m' lblk' v o num kids keys cap nf ts ns Di num' k' y' cap' nf'
    (HN & HA & Hh & Hs & Hk & Hi) Hh' Hs' Hk' HN' HA' HL HM Hmv HW Hb Hap Hy.
  split; [exact HN'|]. split.
  { apply pis_r_apart_app; [exact HA'|]. intros b x Hb'. apply (HA b x). apply in_or_app. right. exact Hb'. }
  split; [exact Hh'|]. split; [exact Hs'|]. split; [exact Hk'|].
  exact (pis_items_xfer m lblk m' lblk' o kids keys k' y' ts ns Di Hi HL HM Hmv HW Hb Hap Hy).
Qed.

Lemma pis_frame : forall m lblk m' lblk' v o num kids keys cap nf ts ns Di num' nf',
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  pj_hdrR segs m' v (5 + pis_oz o) num' 0 kids keys nf' cap -> nf' <= cap ->
  (forall a k, In (a, k) (pis_slots o kids keys cap ++ Di) -> lblk' a k) ->
  (forall x, pis_ifoot o kids keys (Z.of_nat (length ts)) Di x -> pis_same m m' x) ->
  pis_open m' lblk' v o num' kids keys cap nf' ts ns Di.
Proof.
  intros m lblk m' lblk' v o num kids keys cap nf ts ns Di num' nf' H Hh' Hle HL HM.
  pose proof H as (HN & HA & Hh & Hs & Hk & Hi).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hc0 & _)).
  apply (pis_xfer m lblk m' lblk' v o num kids keys cap nf ts ns Di num' kids keys cap nf' H Hh').
  - apply (pis_slots_at_mv lblk lblk' o kids keys nf nf' cap Hs Hle ltac:(lia)).
    intros a k Hak. apply HL. apply in_or_app. left. exact Hak.
  - exact Hk.
  - exact HN.
  - intros b x Hb. apply (HA b x). apply in_or_app. left. exact Hb.
  - intros a k Hak. apply HL. apply in_or_app. right. exact Hak.
  - intros x Hx. apply HM. right. right. exact Hx.
  - intros i Hi'. refine (proj1 (HM (kids + i) _)). left. lia.
  - intros i Hi' Hw. refine (proj2 (HM (kids + i) _) Hw). left. lia.
  - intros Hl. exact (pis_items_mod8 m lblk o kids keys ts ns Di Hi Hl).
  - left. reflexivity.
  - intros Eo i Hi'. refine (proj1 (HM (keys + i) _)). right. left. split; [exact Eo | lia].
Qed.

(* the bytes a pis_ifoot covers lie outside the node: the kids / keys ranges sit inside the slot blocks (n <= cap),
   and the blocks of D are apart from v by the caller's pj_apartR. A caller that knows only that the node changed
   discharges the pis_ifoot premise of pis_frame_v / pis_fd_next_store / pis_exit_item with this lemma and its own
   address bounds (mbyte reads at Z_to_bv 64 x, so x must be in [0, 2 ^ 64) for outside the node to mean unchanged). *)
Lemma pis_ifoot_apart : forall m lblk v o num kids keys cap nf ts ns Di n D x,
  pis_open m lblk v o num kids keys cap nf ts ns Di -> n <= cap -> pj_apartR D v ->
  pis_ifoot o kids keys n D x -> ~ (v <= x < v + 56).
Proof.
  intros m lblk v o num kids keys cap nf ts ns Di n D x (_ & HA & _) Hn HD Hx.
  destruct Hx as [Hx|[(Eo & Hx)|(b & Hb & Hx)]].
  - assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (HA (kids, 56 * cap) x).
    + apply in_or_app. left. unfold pis_slots, kids_blkR. rewrite Ec. left. reflexivity.
    + unfold pj_holdsR; cbn [fst snd]. lia.
  - subst o. assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (HA (keys, 8 * cap) x).
    + apply in_or_app. left. unfold pis_slots, kids_blkR, keys_blkR. rewrite Ec. cbn. right. left. reflexivity.
    + unfold pj_holdsR; cbn [fst snd]. lia.
  - exact (HD b x Hb Hx).
Qed.

Lemma pis_frame_v : forall m lblk m' v o num kids keys cap nf ts ns Di num' nf',
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  pj_hdrR segs m' v (5 + pis_oz o) num' 0 kids keys nf' cap -> nf' <= cap ->
  (forall x, pis_ifoot o kids keys (Z.of_nat (length ts)) Di x -> pis_same m m' x) ->
  pis_open m' lblk v o num' kids keys cap nf' ts ns Di.
Proof.
  intros m lblk m' v o num kids keys cap nf ts ns Di num' nf' H Hh' Hle HM.
  exact (pis_frame m lblk m' lblk v o num kids keys cap nf ts ns Di num' nf' H Hh' Hle
    (pis_open_lblk m lblk v o num kids keys cap nf ts ns Di H) HM).
Qed.

Lemma pis_init : forall m lblk v o, pj_hdrR segs m v (5 + pis_oz o) 0 0 0 0 0 0 ->
  pis_open m lblk v o 0 0 0 0 0 [] [] [].
Proof.
  intros m lblk v o Hh.
  assert (ES : pis_slots o 0 0 0 ++ [] = []) by (destruct o; reflexivity).
  unfold pis_open. rewrite ES.
  split; [constructor|]. split; [intros b x []|]. split; [exact Hh|].
  split.
  { split; [destruct o; cbn [pis_oz]; lia|]. split; [lia|].
    split; [intros _; split; [reflexivity | intros _; reflexivity] | intros Hp; lia]. }
  split; [intros _; reflexivity|].
  destruct o; cbn; [split; reflexivity | reflexivity].
Qed.

Lemma pis_grow_arr : forall m m' Lam Lam' Lam0 v num kids keys cap nf ts ns Di k',
  pis_open m (prh_lin Lam) v false num kids keys cap nf ts ns Di ->
  Permutation Lam (kids_blkR kids cap ++ Lam0) -> Permutation Lam' ((k', 56 * cap2R cap) :: Lam0) ->
  NoDup (map fst Lam') ->
  pis_moved m m' kids k' (56 * cap) ->
  pj_hdrR segs m' v 5 num 0 k' keys nf (cap2R cap) -> pj_slots_atR (prh_lin Lam') 5 k' keys nf (cap2R cap) ->
  Z.of_nat (length ts) <= cap ->
  k' mod 8 = 0 -> 0 <= k' -> k' + 56 * Z.of_nat (length ts) <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m' (k' + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_apart_n Di k' (56 * Z.of_nat (length ts)) ->
  pj_apartR [(k', 56 * cap2R cap)] v ->
  pis_open m' (prh_lin Lam') v false num k' keys (cap2R cap) nf ts ns Di.
Proof.
  intros m m' Lam Lam' Lam0 v num kids keys cap nf ts ns Di k' H HP HP' HN' Hmv Hh' Hs' Hlc Hk8 Hk0 Hk1 HW HM Hap Hav.
  pose proof H as (HN & HA & Hh & Hs & Hk & Hi).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  assert (Hc2 : 0 < cap2R cap) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
  assert (ES : pis_slots false kids keys cap = kids_blkR kids cap)
    by (unfold pis_slots, kids_blkR, keys_blkR; destruct (cap =? 0); reflexivity).
  assert (ES' : pis_slots false k' keys (cap2R cap) = [(k', 56 * cap2R cap)]).
  { unfold pis_slots, kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R cap) 0)) by lia. reflexivity. }
  assert (HR : incl Di Lam0).
  { apply (pis_rest (pis_slots false kids keys cap) Di Lam Lam0 HN
      (pis_open_incl m Lam v false num kids keys cap nf ts ns Di H)).
    rewrite ES. exact HP. }
  apply (pis_xfer m (prh_lin Lam) m' (prh_lin Lam') v false num kids keys cap nf ts ns Di num k' keys (cap2R cap) nf H Hh' Hs').
  - intros _. apply Hk. reflexivity.
  - rewrite ES'. exact (pis_nodup_new [(k', 56 * cap2R cap)] Di Lam' Lam0 HN' HP' HR (pis_nodup_r _ _ _ HN)).
  - rewrite ES'. exact Hav.
  - intros a k Hak. apply (Permutation_in _ (Permutation_sym HP')). right. exact (HR _ Hak).
  - exact HM.
  - intros i Hi'. exact (Hmv i ltac:(lia)).
  - intros i Hi' _. exact (HW i Hi').
  - intros _. exact Hk8.
  - right. exact Hap.
  - intros E. discriminate.
Qed.

Lemma pis_grow_obj : forall m m' Lam Lam' Lam0 v num kids keys cap nf ts ns Di k' y',
  pis_open m (prh_lin Lam) v true num kids keys cap nf ts ns Di ->
  Permutation Lam (kids_blkR kids cap ++ keys_blkR 6 keys cap ++ Lam0) ->
  Permutation Lam' ((y', 8 * cap2R cap) :: (k', 56 * cap2R cap) :: Lam0) ->
  NoDup (map fst Lam') ->
  pis_moved m m' kids k' (56 * cap) -> pis_moved m m' keys y' (8 * cap) ->
  pj_hdrR segs m' v 6 num 0 k' y' nf (cap2R cap) -> pj_slots_atR (prh_lin Lam') 6 k' y' nf (cap2R cap) ->
  Z.of_nat (length ts) <= cap ->
  k' mod 8 = 0 -> 0 <= k' -> k' + 56 * Z.of_nat (length ts) <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m' (k' + i)) ->
  0 <= y' -> y' + 8 * Z.of_nat (length ts) <= 2 ^ 64 ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_apart_n Di k' (56 * Z.of_nat (length ts)) ->
  pj_apartR [(k', 56 * cap2R cap); (y', 8 * cap2R cap)] v ->
  pis_open m' (prh_lin Lam') v true num k' y' (cap2R cap) nf ts ns Di.
Proof.
  intros m m' Lam Lam' Lam0 v num kids keys cap nf ts ns Di k' y' H HP HP' HN' Hmk Hmy Hh' Hs' Hlc Hk8 Hk0 Hk1 HW
    Hy0 Hy1 HM Hap Hav.
  pose proof H as (HN & HA & Hh & Hs & Hk & Hi).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  assert (Hc2 : 0 < cap2R cap) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
  assert (ES' : pis_slots true k' y' (cap2R cap) = [(k', 56 * cap2R cap); (y', 8 * cap2R cap)]).
  { unfold pis_slots, kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R cap) 0)) by lia. reflexivity. }
  assert (HR : incl Di Lam0).
  { apply (pis_rest (pis_slots true kids keys cap) Di Lam Lam0 HN
      (pis_open_incl m Lam v true num kids keys cap nf ts ns Di H)).
    unfold pis_slots. rewrite <- app_assoc. exact HP. }
  assert (HP2 : Permutation Lam' (pis_slots true k' y' (cap2R cap) ++ Lam0)).
  { rewrite ES'. cbn [app]. apply (Permutation_trans HP'). apply perm_swap. }
  apply (pis_xfer m (prh_lin Lam) m' (prh_lin Lam') v true num kids keys cap nf ts ns Di num k' y' (cap2R cap) nf H Hh' Hs').
  - intros E. discriminate.
  - exact (pis_nodup_new _ Di Lam' Lam0 HN' HP2 HR (pis_nodup_r _ _ _ HN)).
  - rewrite ES'. exact Hav.
  - intros a k Hak. apply (Permutation_in _ (Permutation_sym HP')). right. right. exact (HR _ Hak).
  - exact HM.
  - intros i Hi'. exact (Hmk i ltac:(lia)).
  - intros i Hi' _. exact (HW i Hi').
  - intros _. exact Hk8.
  - right. exact Hap.
  - intros _ i Hi'. exact (Hmy i ltac:(lia)).
Qed.

Lemma pis_grow_kept : forall m m' lblk v o num kids keys cap nf ts ns Di,
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys nf cap ->
  pis_moved m m' kids kids (56 * cap) -> (o = true -> pis_moved m m' keys keys (8 * cap)) ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m (kids + i) -> writable_at segs m' (kids + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  Z.of_nat (length ts) <= cap ->
  pis_open m' lblk v o num kids keys cap nf ts ns Di.
Proof.
  intros m m' lblk v o num kids keys cap nf ts ns Di H Hh' Hmk Hmy HW HM Hlc.
  pose proof H as (HN & HA & Hh & Hs & Hk & Hi).
  apply (pis_xfer m lblk m' lblk v o num kids keys cap nf ts ns Di num kids keys cap nf H Hh' Hs Hk HN).
  - intros b x Hb. apply (HA b x). apply in_or_app. left. exact Hb.
  - exact (pis_items_lblk m lblk o kids keys ts ns Di Hi).
  - exact HM.
  - intros i Hi'. exact (Hmk i ltac:(lia)).
  - exact HW.
  - intros Hl. exact (pis_items_mod8 m lblk o kids keys ts ns Di Hi Hl).
  - left. reflexivity.
  - intros Eo i Hi'. exact (Hmy Eo i ltac:(lia)).
Qed.

Lemma pis_snoc : forall m lblk v o num kids keys cap nf ts ns Di t nm Dn Dt,
  pis_open m lblk v o num kids keys cap nf ts ns Di ->
  pj_nodeR segs m lblk (kids + 56 * Z.of_nat (length ts)) t Dt ->
  (if o then exists x k, Dn = [(x, k)] /\ rd_u64 segs m (keys + 8 * Z.of_nat (length ts)) x /\
       pj_cstrR segs m lblk x k nm else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apartR (Dn ++ Dt) v ->
  pis_open m lblk v o num kids keys cap nf (ts ++ [t]) (ns ++ [nm]) (Di ++ Dn ++ Dt).
Proof.
  intros m lblk v o num kids keys cap nf ts ns Di t nm Dn Dt (HN & HA & Hh & Hs & Hk & Hi) HT Hn HN' HA'.
  split; [exact HN'|]. split; [rewrite app_assoc; exact (pis_r_apart_app _ _ v HA HA')|].
  split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|].
  destruct o; unfold pis_items in Hi |- *.
  - destruct Hn as (x & k & -> & Hx & Hc). destruct Hi as (Hl & Hm).
    split; [rewrite !length_app; cbn [length]; lia|].
    rewrite (pis_combine_snoc _ _ ns ts nm t Hl). cbn [app].
    apply pis_mems_snoc; [exact Hm | rewrite (pis_r_combine_len _ _ ns ts Hl); exact Hx | exact Hc
                         | rewrite (pis_r_combine_len _ _ ns ts Hl); exact HT].
  - subst Dn. cbn [app]. exact (pis_items_snoc (pj_nodeR segs m lblk) ts kids Di t Dt Hi HT).
Qed.

Lemma pis_close : forall m lblk v o num kids keys cap acc Di,
  pis_open m lblk v o num kids keys cap (Z.of_nat (length acc)) (map snd (rev acc)) (map fst (rev acc)) Di ->
  pj_nodeR segs m lblk v (mk o (rev acc)) (pis_slots o kids keys cap ++ Di).
Proof.
  intros m lblk v o num kids keys cap acc Di H.
  destruct H as (HN & HA & Hh & Hs & Hk & Hi).
  destruct Hs as (_ & Hkc & Hc0 & Hcp).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  assert (El : Z.of_nat (length acc) = Z.of_nat (length (map snd (rev acc))))
    by (rewrite length_map, length_rev; reflexivity).
  destruct o; cbn [mk]; unfold pis_items in Hi.
  - destruct Hi as (Hl & Hm). rewrite (pis_combine_map _ _ (rev acc)) in Hm.
    cbn [pj_nodeR]. split; [exact HN|]. split; [exact HA|].
    exists num, 0, kids, keys, (Z.of_nat (length acc)), cap. split; [exact Hh|].
    split; [reflexivity|]. split; [rewrite length_rev; reflexivity|]. split; [lia|].
    split; [destruct (Z.eq_dec cap 0) as [E0|E0];
            [left; destruct (Hc0 E0) as (K0 & K1); split; [exact E0|]; split; [exact K0 | apply K1; reflexivity]
            | right; destruct (Hcp ltac:(lia)) as (L0 & L1); split; [lia|]; split; [exact L0 | apply L1; reflexivity]]|].
    exists Di. split; [|exact Hm]. unfold pis_slots, kids_blkR, keys_blkR. destruct (cap =? 0); reflexivity.
  - cbn [pj_nodeR]. split; [exact HN|]. split; [exact HA|].
    exists num, 0, kids, keys, (Z.of_nat (length acc)), cap. split; [exact Hh|].
    split; [reflexivity|]. split; [exact (Hk eq_refl)|]. split; [exact El|]. split; [lia|].
    split; [destruct (Z.eq_dec cap 0) as [E0|E0];
            [left; split; [exact E0 | exact (proj1 (Hc0 E0))] | right; split; [lia | exact (proj1 (Hcp ltac:(lia)))]]|].
    exists Di. split; [|exact Hi]. unfold pis_slots, kids_blkR, keys_blkR. destruct (cap =? 0); reflexivity.
Qed.

Lemma pis_items_pf : forall m lblk o kids keys ts ns Di dd,
  pis_items m lblk o kids keys ts ns Di -> Forall (fun t => (depth t <= dd)%nat) ts ->
  pf_itemsR segs m lblk (pj_fdR segs m lblk dd) o kids keys (length ts) Di.
Proof.
  intros m lblk o kids keys ts ns Di dd H HF. rewrite Forall_forall in HF. destruct o; unfold pis_items in H.
  - destruct H as (Hl & Hm). rewrite <- (pis_r_combine_len _ _ ns ts Hl).
    apply (pis_r_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hm].
    intros a u D1 (nm & Hu) HP. apply in_combine_r in Hu.
    exact (pis_r_fd_mono m lblk (depth u) dd a D1 (HF u Hu) (pis_r_node_fd u m lblk a D1 HP)).
  - apply (pis_r_items_pf m lblk (pj_nodeR segs m lblk)); [|exact H].
    intros a u D1 Hu HP. exact (pis_r_fd_mono m lblk (depth u) dd a D1 (HF u Hu) (pis_r_node_fd u m lblk a D1 HP)).
Qed.

Lemma pis_fd : forall m lblk v o num kids keys cap nf ts ns Di dd,
  pis_open m lblk v o num kids keys cap nf ts ns Di -> nf = Z.of_nat (length ts) ->
  Forall (fun t => (depth t <= dd)%nat) ts ->
  pj_fdR segs m lblk (S dd) v (pis_slots o kids keys cap ++ Di).
Proof.
  intros m lblk v o num kids keys cap nf ts ns Di dd (HN & HA & Hh & Hs & Hk & Hi) En HF.
  pose proof (pis_items_pf m lblk o kids keys ts ns Di dd Hi HF) as HP.
  destruct Hs as (Ht6 & (Hn1 & Hc) & Hc0 & Hcp).
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk dd) o kids keys (Z.to_nat nf) Di)
    by (replace (Z.to_nat nf) with (length ts) by lia; exact HP).
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact HN|]. split; [exact HA|].
  destruct (Z.eq_dec cap 0) as [E0|E0].
  - subst cap. destruct (Hc0 eq_refl) as (K0 & Y0).
    assert (Ky : keys = 0) by (destruct o; [apply Y0; reflexivity | apply Hk; reflexivity]).
    exists (5 + pis_oz o), num, 0, kids, keys, nf, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [left; split; [exact K0 | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ky | split; reflexivity]|].
    split; [unfold pis_slots, kids_blkR, keys_blkR; cbn; apply Permutation_refl|].
    cbv beta. replace (Z.to_nat nf) with 0%nat in HI |- * by lia. cbn [pf_itemsR] in HI |- *. exact HI.
  - destruct (Hcp ltac:(lia)) as (L0 & L1).
    assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; exact E0).
    destruct o.
    + exists (5 + pis_oz true), num, 0, kids, keys, nf, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
      split; [exact Hh|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity | exists (8 * cap); split; [apply L1; reflexivity | split; [lia | reflexivity]]]|].
      split; [unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; cbn; apply Permutation_refl|].
      exact HI.
    + exists (5 + pis_oz false), num, 0, kids, keys, nf, cap, false, [], [(kids, 56 * cap)], [], Di.
      split; [exact Hh|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
      split; [left; split; [apply Hk; reflexivity | split; reflexivity]|].
      split; [unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; cbn; apply Permutation_refl|].
      exact HI.
Qed.

Lemma pis_fd_next : forall m lblk v o num kids keys cap nf ts ns Di dd Dn Dt,
  pis_open m lblk v o num kids keys cap nf ts ns Di -> nf = Z.of_nat (length ts) + 1 ->
  Forall (fun t => (depth t <= dd)%nat) ts ->
  pj_fdR segs m lblk dd (kids + 56 * Z.of_nat (length ts)) Dt ->
  (if o then pj_keyR segs m lblk true (keys + 8 * Z.of_nat (length ts)) Dn else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apartR (Dn ++ Dt) v ->
  pj_fdR segs m lblk (S dd) v (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt).
Proof.
  intros m lblk v o num kids keys cap nf ts ns Di dd Dn Dt (HN0 & HA0 & Hh & Hs & Hk & Hi) En HF Ht Hn HN HA.
  pose proof (pis_items_pf m lblk o kids keys ts ns Di dd Hi HF) as HP.
  destruct Hs as (Ht6 & (Hn1 & Hc) & Hc0 & Hcp).
  destruct (Hcp ltac:(lia)) as (L0 & L1).
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk dd) o kids keys (Z.to_nat nf) (Di ++ Dn ++ Dt)).
  { replace (Z.to_nat nf) with (S (length ts)) by lia. apply pis_r_pf_snoc; [exact HP | |exact Ht].
    destruct o; [exact Hn | cbn [pj_keyR]; exact Hn]. }
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact HN|].
  split; [rewrite app_assoc; apply pis_r_apart_app; [exact HA0 | exact HA]|].
  destruct o.
  - exists (5 + pis_oz true), num, 0, kids, keys, nf, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)],
      (Di ++ Dn ++ Dt).
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [apply L1; reflexivity | split; [lia | reflexivity]]]|].
    split; [unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; cbn; apply Permutation_refl|].
    exact HI.
  - exists (5 + pis_oz false), num, 0, kids, keys, nf, cap, false, [], [(kids, 56 * cap)], [], (Di ++ Dn ++ Dt).
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [left; split; [apply Hk; reflexivity | split; reflexivity]|].
    split; [unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; cbn; apply Permutation_refl|].
    exact HI.
Qed.

Lemma pis_fd_hdr0 : forall m lblk dd v ty num cap, pj_hdrR segs m v ty num 0 0 0 0 cap -> pj_fdR segs m lblk dd v [].
Proof.
  intros m lblk dd v ty num cap Hh.
  assert (F : pj_fdR segs m lblk 0 v []).
  { cbn [pj_fdR]. split; [constructor|]. split; [intros b x []|].
    exists ty, num, 0, 0, 0, 0, cap, false, [], [], [], []. split; [exact Hh|].
    split; [left; split; reflexivity|]. split; [left; split; [reflexivity | split; reflexivity]|].
    split; [left; split; [reflexivity | split; reflexivity]|]. split; [apply Permutation_refl|]. split; reflexivity. }
  exact (pis_r_fd_mono m lblk 0 dd v [] ltac:(lia) F).
Qed.

Lemma pis_pf_frame : forall m lblk m' lblk' (P Q : Z -> list (Z * Z) -> Prop) ks N a ka D,
  pf_itemsR segs m lblk P ks a ka N D ->
  (forall i D1, (i < N)%nat -> incl D1 D -> P (a + 56 * Z.of_nat i) D1 -> Q (a + 56 * Z.of_nat i) D1) ->
  (forall i Dk, (i < N)%nat -> incl Dk D -> pj_keyR segs m lblk ks (ka + 8 * Z.of_nat i) Dk ->
     pj_keyR segs m' lblk' ks (ka + 8 * Z.of_nat i) Dk) ->
  pf_itemsR segs m' lblk' Q ks a ka N D.
Proof.
  intros m lblk m' lblk' P Q ks N. induction N as [|N IH]; intros a ka D H HP HK; cbn [pf_itemsR] in *.
  - exact H.
  - destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2. split; [exact E|].
    split.
    + specialize (HK 0%nat Dk). replace (ka + 8 * Z.of_nat 0) with ka in HK by lia.
      apply HK; [lia | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact Hk].
    + split.
      * specialize (HP 0%nat D1). replace (a + 56 * Z.of_nat 0) with a in HP by lia.
        apply HP; [lia | subst D; intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb | exact H1].
      * apply (IH (a + 56) (ka + 8) D2 H2).
        -- intros i D3 Hi Hinc HP3.
           replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
           apply HP; [lia | subst D; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply Hinc; exact Hb
                     | exact HP3].
        -- intros i Dk3 Hi Hinc HK3.
           replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in HK3 |- * by lia.
           apply HK; [lia | subst D; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply Hinc; exact Hb
                     | exact HK3].
Qed.

Lemma pis_fd_frame : forall d m lblk m' lblk' p D,
  pj_fdR segs m lblk d p D ->
  (forall a k, In (a, k) D -> lblk a k -> lblk' a k) ->
  (forall x, pj_footR p D x -> pis_same m m' x) ->
  pj_fdR segs m' lblk' d p D.
Proof.
  intros d. induction d as [|d IH]; intros m lblk m' lblk' p D H HL HM; cbn [pj_fdR] in H |- *;
    destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & HS & HK & HY & HP & HI);
    (split; [exact Hn|]); (split; [exact Ha|]);
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
    (assert (HD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP) Hb)));
    (split; [apply (pis_hdr_frame m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]);
    (split; [destruct HS as [HS|(k & Hl & ->)];
             [left; exact HS | right; exists k; split; [apply HL; [apply HD; left; reflexivity | exact Hl] | reflexivity]]|]);
    (split; [destruct HK as [HK|(k & Hl & Hk & ->)];
             [left; exact HK | right; exists k; split;
               [apply HL; [apply HD; apply in_or_app; right; left; reflexivity | exact Hl] | split; [exact Hk | reflexivity]]]|]);
    (split; [destruct HY as [HY|(Eks & k & Hl & Hk & ->)];
             [left; exact HY | right; split; [exact Eks|]; exists k; split;
               [apply HL; [apply HD; apply in_or_app; right; apply in_or_app; right; left; reflexivity | exact Hl]
               | split; [exact Hk | reflexivity]]]|]);
    (split; [exact HP|]).
  - exact HI.
  - cbv beta in HI |- *.
    apply (pis_pf_frame m lblk m' lblk' (pj_fdR segs m lblk d) (pj_fdR segs m' lblk' d) ks (Z.to_nat n) kids keys Di HI).
    + intros i D1 Hi Hinc HP1. apply (IH m lblk m' lblk' _ D1 HP1).
      * intros a k Hak. apply HL. apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        apply Hinc. exact Hak.
      * intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
        -- right. destruct HK as [(_ & En & _)|(k & _ & Hk & EDk)]; [lia|].
           exists (kids, k). split; [apply HD; apply in_or_app; right; rewrite EDk; left; reflexivity
                                    | unfold pj_holdsR; cbn [fst snd]; lia].
        -- right. exists b. split; [|exact Hx].
           apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply Hinc. exact Hb.
    + intros i Dk1 Hi Hinc HK1. destruct ks; cbn [pj_keyR] in HK1 |- *; [|exact HK1].
      destruct HK1 as (x & Hx & Hz). exists x. split.
      * destruct HY as [(_ & Eks & _)|(_ & k & _ & Hk & EDy)]; [discriminate|].
        assert (Hin : In (keys, k) D)
          by (apply HD; apply in_or_app; right; apply in_or_app; right; rewrite EDy; left; reflexivity).
        apply (pis_u64_frame m m'); [exact Hx|]. intros y Hy.
        refine (proj1 (HM y (or_intror (ex_intro _ (keys, k) (conj Hin _))))).
        unfold pj_holdsR; cbn [fst snd]. lia.
      * destruct Hz as [Hz|(k & Hl & ->)]; [left; exact Hz|]. right. exists k. split; [|reflexivity].
        apply HL; [|exact Hl]. apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        apply Hinc. left. reflexivity.
Qed.

Lemma pis_fd_next_store : forall m m' lblk v o num kids keys cap ts ns Di dd Dn Dt,
  pis_open m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Z.of_nat (length ts) < cap ->
  Forall (fun t => (depth t <= dd)%nat) ts ->
  pj_fdR segs m lblk dd (kids + 56 * Z.of_nat (length ts)) Dt ->
  (if o then pj_keyR segs m lblk true (keys + 8 * Z.of_nat (length ts)) Dn else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apartR (Dn ++ Dt) v ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts) + 1) cap ->
  (forall x, pis_ifoot o kids keys (Z.of_nat (length ts) + 1) (Di ++ Dt) x -> pis_same m m' x) ->
  pj_fdR segs m' lblk (S dd) v (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt).
Proof.
  intros m m' lblk v o num kids keys cap ts ns Di dd Dn Dt H Hlc HF Ht Hn HN HA Hh' HM.
  assert (H' : pis_open m' lblk v o num kids keys cap (Z.of_nat (length ts) + 1) ts ns Di).
  { refine (pis_frame_v m lblk m' v o num kids keys cap _ ts ns Di num _ H Hh' ltac:(lia) _).
    intros x Hx. apply HM. destruct Hx as [Hx|[(Eo & Hx)|(b & Hb & Hx)]].
    - left. lia.
    - right. left. split; [exact Eo | lia].
    - right. right. exists b. split; [apply in_or_app; left; exact Hb | exact Hx]. }
  apply (pis_fd_next m' lblk v o num kids keys cap _ ts ns Di dd Dn Dt H' eq_refl HF).
  - apply (pis_fd_frame dd m lblk m' lblk _ Dt Ht); [intros a k _ Hl; exact Hl|].
    intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
    + left. lia.
    + right. right. exists b. split; [apply in_or_app; right; exact Hb | exact Hx].
  - destruct o; [|exact Hn].
    cbn [pj_keyR] in Hn |- *. destruct Hn as (x & Hx & Hz). exists x. split; [|exact Hz].
    apply (pis_u64_frame m m'); [exact Hx|]. intros y Hy. refine (proj1 (HM y _)).
    right. left. split; [reflexivity | lia].
  - exact HN.
  - exact HA.
Qed.

Lemma pis_grow_half_fd : forall m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' dd,
  pis_open m (prh_lin Lam) v true num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Forall (fun t => (depth t <= dd)%nat) ts ->
  Permutation Lam (kids_blkR kids cap ++ Lam0) -> Permutation Lam' ((k', 56 * cap2R cap) :: Lam0) ->
  NoDup (map fst Lam') ->
  pis_moved m m' kids k' (56 * cap) -> pis_moved m m' keys keys (8 * cap) ->
  pj_hdrR segs m' v 6 num 0 k' keys (Z.of_nat (length ts)) cap ->
  k' mod 8 = 0 -> 0 <= k' -> k' + 56 * Z.of_nat (length ts) <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m' (k' + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_apart_n Di k' (56 * Z.of_nat (length ts)) ->
  pj_apartR [(k', 56 * cap2R cap)] v ->
  pj_fdR segs m' (prh_lin Lam') (S dd) v ((k', 56 * cap2R cap) :: keys_blkR 6 keys cap ++ Di).
Proof.
  intros m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' dd H HF HP HP' HN' Hmk Hmy Hh' Hk8 Hk0 Hk1 HW HM Hap Hav.
  pose proof H as (HN & HA & Hh & Hs & _ & Hi).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  destruct Hs as (_ & (Hn1 & _) & Hc0 & Hcp).
  assert (HR : incl (keys_blkR 6 keys cap ++ Di) Lam0).
  { apply (pis_rest (kids_blkR kids cap) (keys_blkR 6 keys cap ++ Di) Lam Lam0); [| |exact HP].
    - rewrite app_assoc. exact HN.
    - rewrite app_assoc. exact (pis_open_incl m Lam v true num kids keys cap _ ts ns Di H). }
  assert (HL' : forall a k, In (a, k) Lam0 -> prh_lin Lam' a k)
    by (intros a k Hak; unfold prh_lin; apply (Permutation_in _ (Permutation_sym HP')); right; exact Hak).
  assert (Hi' : pis_items m' (prh_lin Lam') true k' keys ts ns Di).
  { apply (pis_items_xfer m (prh_lin Lam) m' (prh_lin Lam') true kids keys k' keys ts ns Di Hi).
    - intros a k Hak. apply HL'. apply HR. apply in_or_app. right. exact Hak.
    - exact HM.
    - intros i Hi'. exact (Hmk i ltac:(lia)).
    - intros i Hi' _. exact (HW i Hi').
    - intros _. exact Hk8.
    - right. exact Hap.
    - intros _ i Hi'. exact (Hmy i ltac:(lia)). }
  pose proof (pis_items_pf m' (prh_lin Lam') true k' keys ts ns Di dd Hi' HF) as HPf.
  assert (Hc2 : cap <= cap2R cap) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
  assert (Hkk : prh_lin Lam' k' (56 * cap2R cap))
    by (unfold prh_lin; apply (Permutation_in _ (Permutation_sym HP')); left; reflexivity).
  cbn [pj_fdR]. unfold pj_fshapeR.
  split.
  { apply (pis_nodup_new [(k', 56 * cap2R cap)] (keys_blkR 6 keys cap ++ Di) Lam' Lam0 HN' HP' HR).
    apply (pis_nodup_r _ (kids_blkR kids cap) (keys_blkR 6 keys cap ++ Di)). rewrite app_assoc. exact HN. }
  split.
  { change (pj_apartR ([(k', 56 * cap2R cap)] ++ (keys_blkR 6 keys cap ++ Di)) v).
    apply pis_r_apart_app; [exact Hav|].
    intros b x Hb. apply (HA b x). unfold pis_slots. rewrite <- app_assoc. apply in_or_app. right. exact Hb. }
  destruct (Z.eq_dec cap 0) as [E0|E0].
  - subst cap. destruct (Hc0 eq_refl) as (K0 & Y0). specialize (Y0 eq_refl).
    assert (Hl0 : length ts = 0%nat) by lia.
    exists 6, num, 0, k', keys, (Z.of_nat (length ts)), 0, false, [], [(k', 56 * cap2R 0)], [], Di.
    split; [exact Hh'|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap2R 0); split; [exact Hkk | split; [lia | reflexivity]]|].
    split; [left; split; [exact Y0 | split; reflexivity]|].
    split; [unfold keys_blkR; cbn; apply Permutation_refl|].
    cbv beta. rewrite Hl0 in HPf |- *. cbn in HPf |- *. exact HPf.
  - destruct (Hcp ltac:(lia)) as (L0 & L1).
    assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; exact E0).
    assert (Hky : In (keys, 8 * cap) Lam0)
      by (apply HR; apply in_or_app; left; unfold keys_blkR; rewrite Ec; cbn; left; reflexivity).
    exists 6, num, 0, k', keys, (Z.of_nat (length ts)), cap, true, [], [(k', 56 * cap2R cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh'|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap2R cap); split; [exact Hkk | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact (HL' _ _ Hky) | split; [lia | reflexivity]]]|].
    split; [unfold keys_blkR; rewrite Ec; cbn; apply Permutation_refl|].
    cbv beta. rewrite Nat2Z.id. exact HPf.
Qed.

Lemma pis_exit_open : forall m lblk v o num kids keys cap ts ns Di d,
  pis_open m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di -> (d < MAXD)%nat ->
  Forall (fun t => (depth t <= MAXD - S d)%nat) ts ->
  pj_fdR segs m lblk (MAXD - d) v (pis_slots o kids keys cap ++ Di).
Proof.
  intros m lblk v o num kids keys cap ts ns Di d H Hd HF. rewrite (pis_maxd d Hd).
  exact (pis_fd m lblk v o num kids keys cap _ ts ns Di _ H eq_refl HF).
Qed.

Lemma pis_exit_grow_kept : forall m m' lblk v o num kids keys cap ts ns Di d,
  pis_open m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di -> (d < MAXD)%nat ->
  Forall (fun t => (depth t <= MAXD - S d)%nat) ts ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts)) cap ->
  pis_moved m m' kids kids (56 * cap) -> (o = true -> pis_moved m m' keys keys (8 * cap)) ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m (kids + i) -> writable_at segs m' (kids + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pj_fdR segs m' lblk (MAXD - d) v (pis_slots o kids keys cap ++ Di).
Proof.
  intros m m' lblk v o num kids keys cap ts ns Di d H Hd HF Hh' Hmk Hmy HW HM.
  pose proof H as (_ & _ & _ & (_ & (Hn1 & _) & _) & _).
  apply (pis_exit_open m' lblk v o num kids keys cap ts ns Di d); [|exact Hd | exact HF].
  exact (pis_grow_kept m m' lblk v o num kids keys cap _ ts ns Di H Hh' Hmk Hmy HW HM Hn1).
Qed.

Lemma pis_exit_grow_half : forall m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' d,
  pis_open m (prh_lin Lam) v true num kids keys cap (Z.of_nat (length ts)) ts ns Di -> (d < MAXD)%nat ->
  Forall (fun t => (depth t <= MAXD - S d)%nat) ts ->
  Permutation Lam (kids_blkR kids cap ++ Lam0) -> Permutation Lam' ((k', 56 * cap2R cap) :: Lam0) ->
  NoDup (map fst Lam') ->
  pis_moved m m' kids k' (56 * cap) -> pis_moved m m' keys keys (8 * cap) ->
  pj_hdrR segs m' v 6 num 0 k' keys (Z.of_nat (length ts)) cap ->
  k' mod 8 = 0 -> 0 <= k' -> k' + 56 * Z.of_nat (length ts) <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m' (k' + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same m m' x) ->
  pis_apart_n Di k' (56 * Z.of_nat (length ts)) ->
  pj_apartR [(k', 56 * cap2R cap)] v ->
  pj_fdR segs m' (prh_lin Lam') (MAXD - d) v ((k', 56 * cap2R cap) :: keys_blkR 6 keys cap ++ Di).
Proof.
  intros m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' d H Hd HF HP HP' HN' Hmk Hmy Hh' Hk8 Hk0 Hk1 HW HM Hap Hav.
  rewrite (pis_maxd d Hd).
  exact (pis_grow_half_fd m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' _ H HF HP HP' HN' Hmk Hmy Hh'
    Hk8 Hk0 Hk1 HW HM Hap Hav).
Qed.

Lemma pis_exit_item : forall m m' lblk v o num kids keys cap ts ns Di d Dn Dt,
  pis_open m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Z.of_nat (length ts) < cap -> (d < MAXD)%nat ->
  Forall (fun t => (depth t <= MAXD - S d)%nat) ts ->
  pj_fdR segs m lblk (MAXD - S d) (kids + 56 * Z.of_nat (length ts)) Dt ->
  (if o then pj_keyR segs m lblk true (keys + 8 * Z.of_nat (length ts)) Dn else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apartR (Dn ++ Dt) v ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts) + 1) cap ->
  (forall x, pis_ifoot o kids keys (Z.of_nat (length ts) + 1) (Di ++ Dt) x -> pis_same m m' x) ->
  pj_fdR segs m' lblk (MAXD - d) v (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt).
Proof.
  intros m m' lblk v o num kids keys cap ts ns Di d Dn Dt H Hlc Hd HF Ht Hn HN HA Hh' HM.
  rewrite (pis_maxd d Hd).
  exact (pis_fd_next_store m m' lblk v o num kids keys cap ts ns Di _ Dn Dt H Hlc HF Ht Hn HN HA Hh' HM).
Qed.

End S.

Lemma pis_depth_snoc : forall d ts y ok t r tr ok',
  Forall (fun u => (depth u <= MAXD - S d)%nat) ts ->
  jr_value prh_jr_strtod (S d) y ok = (Some (t, r), tr, ok') ->
  Forall (fun u => (depth u <= MAXD - S d)%nat) (ts ++ [t]).
Proof.
  intros d ts y ok t r tr ok' HF E. apply Forall_app. split; [exact HF|].
  constructor; [exact (jr_value_depth prh_jr_strtod (S d) y ok t r tr ok' E) | constructor].
Qed.

Lemma pis_close_depth : forall d o (acc : list (list Z * jv)), (d < MAXD)%nat ->
  Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)) ->
  (depth (mk o (rev acc)) <= MAXD - d)%nat.
Proof.
  intros d o acc Hd HF. rewrite (pis_maxd d Hd). apply mk_depth.
  apply Forall_map in HF. exact HF.
Qed.
