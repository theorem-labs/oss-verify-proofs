(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition TML (tm : gmap N Z) (L : list (N * Z)) : Prop := map_to_list tm ≡ₚ L.

#[using="Type"] Lemma TML_nodup tm L : TML tm L -> List.NoDup (map fst L).
Proof. intros H. unfold TML in H. eapply Permutation_NoDup; [apply Permutation_map; exact H|]. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.

#[using="Type"] Lemma TML_lookup tm L k n : TML tm L -> In (k, n) L -> tm !! k = Some n.
Proof.
  intros H Hin. apply elem_of_map_to_list. unfold TML in H. rewrite H. apply list_elem_of_In. exact Hin.
Qed.

#[using="Type"] Lemma TML_lookup_None tm L k : TML tm L -> ~ In k (map fst L) -> tm !! k = None.
Proof.
  intros H NI. destruct (tm !! k) as [n|] eqn:E; [| reflexivity]. exfalso. apply NI.
  apply elem_of_map_to_list in E. unfold TML in H. rewrite H in E. apply list_elem_of_In in E. apply in_map_iff. exists (k, n). auto.
Qed.

#[using="Type"] Lemma TML_sizes tm L : TML tm L -> Permutation (sizes tm) (map snd L).
Proof. intros H. unfold sizes. apply Permutation_map. exact H. Qed.

#[using="Type"] Lemma TML_insert tm L k n : TML tm L -> ~ In k (map fst L) -> TML (<[k := n]> tm) ((k, n) :: L).
Proof.
  intros H NI. unfold TML. rewrite map_to_list_insert; [| exact (TML_lookup_None _ _ _ H NI)]. apply Permutation_cons; [reflexivity| exact H].
Qed.

Fixpoint lrm (k : N) (L : list (N * Z)) : list (N * Z) :=
  match L with [] => [] | (k', n) :: L' => if N.eqb k' k then L' else (k', n) :: lrm k L' end.

#[using="Type"] Lemma lrm_perm k n L : List.NoDup (map fst L) -> In (k, n) L -> Permutation L ((k, n) :: lrm k L).
Proof.
  induction L as [|[k' n'] L IH]; intros ND Hin; [destruct Hin|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. cbn.
  destruct (N.eqb_spec k' k) as [->|NE].
  - destruct Hin as [E|Hin]; [injection E as ->; reflexivity|]. exfalso. apply NI. apply in_map_iff. exists (k, n). auto.
  - destruct Hin as [E|Hin]; [injection E as -> ->; exfalso; exact (NE eq_refl)|].
    etransitivity; [apply perm_skip; exact (IH ND' Hin)|]. apply perm_swap.
Qed.

#[using="Type"] Lemma TML_delete tm L k n : TML tm L -> In (k, n) L -> TML (delete k tm) (lrm k L).
Proof.
  intros H Hin. pose proof (TML_nodup _ _ H) as ND. unfold TML in *.
  pose proof (map_to_list_delete tm k n (TML_lookup _ _ _ _ H Hin)) as P.
  apply (Permutation_cons_inv (a := (k, n))). etransitivity; [exact P|]. etransitivity; [exact H|]. exact (lrm_perm k n L ND Hin).
Qed.

#[using="Type"] Lemma lrm_notin k L : ~ In k (map fst L) -> lrm k L = L.
Proof.
  induction L as [|[k' n'] L IH]; intros NI; [reflexivity|]. cbn. destruct (N.eqb_spec k' k) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros X; apply NI; right; exact X.
Qed.
#[using="Type"] Lemma lrm_app k L1 L2 : ~ In k (map fst L1) -> lrm k (L1 ++ L2) = L1 ++ lrm k L2.
Proof.
  induction L1 as [|[k' n'] L1 IH]; intros NI; [reflexivity|]. cbn. destruct (N.eqb_spec k' k) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros X; apply NI; right; exact X.
Qed.
#[using="Type"] Lemma lrm_head k n L : lrm k ((k, n) :: L) = L.
Proof. cbn. rewrite N.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma R63N_app a b : R63N (a ++ b) = R63N a + R63N b.
Proof. unfold R63N. rewrite map_app. induction a as [|x a IH]; cbn; [reflexivity|]. unfold zsum in *. cbn. rewrite IH. lia. Qed.
#[using="Type"] Lemma R63N_cons x a : R63N (x :: a) = bigb x + R63N a.
Proof. unfold R63N, zsum. reflexivity. Qed.
#[using="Type"] Lemma R63N_nil : R63N [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma bigb_nonneg n : 0 <= bigb n.
Proof. unfold bigb. destruct (MMAP_THRESHOLD <=? n) eqn:E; [| lia]. apply Z.leb_le in E. pose proof (LB_Bound.round_up_pg_nonneg (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. lia. Qed.
#[using="Type"] Lemma R63N_nonneg l : 0 <= R63N l.
Proof. induction l as [|x l IH]; [rewrite R63N_nil; lia|]. rewrite R63N_cons. pose proof (bigb_nonneg x). lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma budget_of_TML tm L n :
  TML tm L -> zlen L + 1 <= 9 -> 0 <= n -> PHI P9 + R63N (map snd L) + bigb n <= BLIVE ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE.
Proof.
  intros H HL Hn HB. pose proof (TML_sizes _ _ H) as P. split.
  - apply (ROOMN_of_len P9). intros c. rewrite (zlen_perm _ _ P). unfold zlen in *. rewrite length_map. unfold P9. lia.
  - rewrite (R63N_perm _ _ P). exact HB.
Qed.

#[using="Type"] Lemma zlen_cons {A} (x : A) l : zlen (x :: l) = 1 + zlen l. Proof. unfold zlen. cbn [length]. lia. Qed.
#[using="Type"] Lemma zlen_app {A} (a b : list A) : zlen (a ++ b) = zlen a + zlen b. Proof. unfold zlen. rewrite length_app. lia. Qed.
#[using="Type"] Lemma zlen_nil {A} : zlen (@nil A) = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rctx := mkRC {
  rc_B : list (N * Z);                    (* [comment removed for export] *)
  rc_Kx : list kfe;                       (* [comment removed for export] *)
  rc_F0 : fpm;                            (* [comment removed for export] *)
  rc_hs : list hptr;                      (* [comment removed for export] *)
  rc_C : list (list byte * list byte);    (* [comment removed for export] *)
  rc_oh : option hptr;                    (* [comment removed for export] *)
  rc_fp : hptr;                           (* [comment removed for export] *)
  rc_e0 : kfe;                            (* [comment removed for export] *)
  rc_d : list byte;                       (* [comment removed for export] *)
  rc_P0 : Z                               (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition BASEB : Z := 2 * B26.
(* [comment removed for export] *)
Definition BUFMAX : Z := 2^27 + 131104.
(* [comment removed for export] *)
Definition IFSMAX : Z := 2^22.
(* [comment removed for export] *)
Definition VC0 : Z := 2^21.
Definition V_READ : Z := VC0 + 2 * MAX_INPUT + 80 * IFSMAX + BUFMAX.
(* [comment removed for export] *)
Definition liveL (L : list (N * Z)) : Z := zsum (map n1 (map snd L)).

Record rcwf (rc : rctx) : Prop := mkRCWF {
  rw_B : zlen (rc_B rc) <= 3 /\ R63N (map snd (rc_B rc)) <= BASEB;
  rw_fpB : ~ In (rc_fp rc) (map fst (rc_B rc));
  rw_Kx : forall x, In x (rc_Kx rc) -> k_fd x <> k_fd (rc_e0 rc);
  rw_own : k_own (rc_e0 rc) = Some (rc_fp rc);
  rw_kind : k_kind (rc_e0 rc) = KR;
  rw_data : k_data (rc_e0 rc) = Some (rc_d rc);
  rw_hs : In (rc_fp rc) (rc_hs rc);
  rw_F0 : ~ In (rc_fp rc) (map fst (rc_F0 rc));
  rw_oh : rc_oh rc <> Some (rc_fp rc);
  rw_d : Z.of_nat (length (rc_d rc)) < MAX_INPUT;
  rw_Blive : liveL (rc_B rc) <= 2^27 + FILE_ALLOC + 1;
  rw_P0 : 0 <= rc_P0 rc /\ pot_ok (rc_P0 rc + V_READ)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mok (m : list Z) : Prop := zlength m <= 512.
#[using="Type"] Lemma mok_nil : mok []. Proof. unfold mok, zlength. cbn. lia. Qed.
#[using="Type"] Lemma snprintf_len n f args : 1 <= n -> zlength (snprintf n f args) <= n - 1.
Proof. intros Hn. unfold snprintf, snprintf_out, zlength. rewrite length_firstn. lia. Qed.
#[using="Type"] Lemma mok_snprintf n f args : 1 <= n <= 513 -> mok (snprintf n f args).
Proof. intros Hn. unfold mok. pose proof (snprintf_len n f args ltac:(lia)). lia. Qed.
#[using="Type"] Lemma mok_fmt_errmsg f args e : mok (fmt_errmsg f args e).
Proof.
  unfold fmt_errmsg, mok. cbv zeta. pose proof (snprintf_len PCAP_ERRBUF_SIZE f args ltac:(unfold PCAP_ERRBUF_SIZE; lia)) as L1.
  destruct (PCAP_ERRBUF_SIZE <? _) eqn:E; [unfold PCAP_ERRBUF_SIZE in *; lia|]. apply Z.ltb_ge in E.
  rewrite !zlength_app. pose proof (snprintf_len (PCAP_ERRBUF_SIZE - zlength (snprintf PCAP_ERRBUF_SIZE f args) - 2) "%s" [AStr (snd (strerror_r e PCAP_ERRBUF_SIZE))] ltac:(unfold PCAP_ERRBUF_SIZE in *; lia)).
  assert (X : zlength (str ": ") = 2) by reflexivity. rewrite X. unfold PCAP_ERRBUF_SIZE in *. lia.
Qed.
End WithCeil.

Ltac head_of t := match t with ?f _ => head_of f | _ => t end.
(* [comment removed for export] *)
Ltac mok_tac :=
  first [ apply mok_nil | apply mok_fmt_errmsg | (apply mok_snprintf; unfold PCAP_ERRBUF_SIZE; lia) | assumption
        | lazymatch goal with |- mok ?m => let h := head_of m in unfold h; apply mok_snprintf; unfold PCAP_ERRBUF_SIZE; lia end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
(* [comment removed for export] *)
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
#[using="Type"] Lemma dsl_bytes d p n : bytes_ok (dsl d p n).
Proof.
  unfold dsl, of_bytes, bytes_ok. apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
#[using="Type"] Lemma bytes_ok_firstn k l : bytes_ok l -> bytes_ok (firstn k l).
Proof. intros H. unfold bytes_ok in *. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
#[using="Type"] Lemma bytes_ok_skipn k l : bytes_ok l -> bytes_ok (skipn k l).
Proof. intros H. unfold bytes_ok in *. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
#[using="Type"] Lemma bytes_ok_app a b : bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros; unfold bytes_ok in *; apply Forall_app; tauto. Qed.
#[using="Type"] Lemma le_of_bytes_range l : bytes_ok l -> 0 <= le_of_bytes l < 256 ^ (Z.of_nat (length l)).
Proof.
  induction l as [|b l IH]; intros H; cbn [le_of_bytes length]; [lia|]. inversion H; subst. specialize (IH ltac:(assumption)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
#[using="Type"] Lemma get_le32_range l k : bytes_ok l -> 0 <= get_le32 l k < 2^32.
Proof.
  intros H. unfold get_le32, zslice, zfirstn, zskipn. pose proof (le_of_bytes_range (firstn (Z.to_nat 4) (skipn (Z.to_nat k) l)) ltac:(apply bytes_ok_firstn; apply bytes_ok_skipn; exact H)) as R.
  pose proof (firstn_le_length (Z.to_nat 4) (skipn (Z.to_nat k) l)) as L.
  assert (256 ^ Z.of_nat (length (firstn (Z.to_nat 4) (skipn (Z.to_nat k) l))) <= 2^32) by (change (2^32) with (256^4); apply Z.pow_le_mono_r; lia). lia.
Qed.
#[using="Type"] Lemma get_le16_range l k : bytes_ok l -> 0 <= get_le16 l k < 2^16.
Proof.
  intros H. unfold get_le16, zslice, zfirstn, zskipn. pose proof (le_of_bytes_range (firstn (Z.to_nat 2) (skipn (Z.to_nat k) l)) ltac:(apply bytes_ok_firstn; apply bytes_ok_skipn; exact H)) as R.
  pose proof (firstn_le_length (Z.to_nat 2) (skipn (Z.to_nat k) l)) as L.
  assert (256 ^ Z.of_nat (length (firstn (Z.to_nat 2) (skipn (Z.to_nat k) l))) <= 2^16) by (change (2^16) with (256^2); apply Z.pow_le_mono_r; lia). lia.
Qed.
#[using="Type"] Lemma le_bytes_nat_ok k v : bytes_ok (le_bytes_nat k v).
Proof. revert v; induction k as [|k IH]; intros v; cbn; constructor; [| apply IH]. pose proof (Z.mod_pos_bound v 256 ltac:(lia)). lia. Qed.
#[using="Type"] Lemma le_bytes_nat_length k v : length (le_bytes_nat k v) = k.
Proof. revert v; induction k as [|k IH]; intros v; cbn; [reflexivity| now rewrite IH]. Qed.
#[using="Type"] Lemma bswap32_range v : 0 <= bswap32 v < 2^32.
Proof.
  unfold bswap32, le_bytes. pose proof (le_of_bytes_range (rev (le_bytes_nat (Z.to_nat 4) v))) as R.
  rewrite length_rev, le_bytes_nat_length in R. apply R. unfold bytes_ok. apply Forall_rev. apply le_bytes_nat_ok.
Qed.
#[using="Type"] Lemma bswap16_range v : 0 <= bswap16 v < 2^16.
Proof.
  unfold bswap16, le_bytes. pose proof (le_of_bytes_range (rev (le_bytes_nat (Z.to_nat 2) v))) as R.
  rewrite length_rev, le_bytes_nat_length in R. apply R. unfold bytes_ok. apply Forall_rev. apply le_bytes_nat_ok.
Qed.

Section Reading.
(* [comment removed for export] *)
Variable Uk : UKit.
#[local] Notation G := (uk_G Uk).
#[local] Notation nsafeP := (uk_nsafeP Uk).
#[local] Notation gstepP := (uk_gstepP Uk).
#[local] Notation GK_safe := (uk_GK_safe Uk).
#[local] Notation GK_step := (uk_GK_step Uk).
#[local] Notation HG := (uk_HG Uk).
#[local] Notation HC := (uk_HC Uk).
#[local] Notation HOG := (uk_HOG Uk).
#[local] Notation HOC := (uk_HOC Uk).
#[local] Notation eqbG := (uk_eqbG Uk).
#[local] Notation eqbC := (uk_eqbC Uk).
#[local] Notation segs := (uk_segs Uk).
#[local] Notation hi := (uk_hi Uk).
#[local] Notation PSG := (PState (uk_HG Uk) hptr).
#[local] Notation PSC := (PState (uk_HC Uk) hptr).
#[local] Notation npk := (npeek (uk_segs Uk)).
#[local] Notation relX := (USimX.relX (uk_G Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr)).
#[local] Notation usimS := (usimX (uk_nsafeP Uk) (uk_gstepP Uk) (npeek (uk_segs Uk))).
#[local] Notation RQ := (RelX.RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX := (RelX.RX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RU := (RelX.RU (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_RQ := (RelX.RX_RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_U := (RelX.RX_U (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_G := (RelX.RQ_G (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_C := (RelX.RQ_C (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_minvX := (RelX.RQ_minvX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_halted := (RelX.RQ_halted (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc := (RelX.RQ_libc (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile := (RelX.RQ_outfile (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_mq := (RelX.RQ_mq (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_lci := (RelX.RQ_lci (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_fresh := (RelX.RQ_fresh (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_toks_below := (RelX.RQ_toks_below (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_pot := (RelX.RQ_pot (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation blk_addr_range := (RelX.blk_addr_range (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_same_heap := (RelX.RQ_same_heap (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc_upd := (RelX.RQ_libc_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile_upd := (RelX.RQ_outfile_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_xstep := (RelX.RQ_xstep (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_after := (RelX.RQ_after (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Definition ru_get := @RelX.ru_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_rd_lc := @RelX.ru_rd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_lc := @RelX.ru_upd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_outfile := @RelX.ru_upd_outfile (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_heap_op := @RelX.ru_heap_op (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
Arguments ru_heap_op {A}.
#[local] Definition ru_heap_opu := @RelX.ru_heap_opu (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pmalloc := @RelX.ru_pmalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pcalloc := @RelX.ru_pcalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_prealloc := @RelX.ru_prealloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pfree := @RelX.ru_pfree (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_sys := @RelX.ru_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
Arguments ru_sys {A}.
#[local] Definition ru_read := @RelX.ru_read (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_readv := @RelX.ru_readv (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_exit := @RelX.ru_exit (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_bind := @RelX.ru_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind {A B}.
#[local] Definition ru_bind2 := @RelX.ru_bind2 (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind2 {A B A' B'}.
#[local] Definition ru_seq := @RelX.ru_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_seq {A B A' B'}.
#[local] Definition ru_ret := @RelX.ru_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_ret {A}.
#[local] Definition ru_post := @RelX.ru_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_post {A}.
#[local] Definition ru_pre := @RelX.ru_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_pre {A B}.
#[local] Definition ru_munr := @RelX.ru_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_munr {A B}.
#[local] Definition ru_use := @RelX.ru_use (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_use {A B}.
#[local] Definition ru_bind_retl := @RelX.ru_bind_retl (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind_retl {A B}.
#[local] Definition usim_pure := @usimX_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pure {A B}.
#[local] Definition usim_exI := @usimX_exI (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_exI {A B X}.
#[local] Definition usim_ret := @usimX_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_ret {A B}.
#[local] Definition usim_get := @usimX_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_upd := @usimX_upd (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_post := @usimX_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_post {A B}.
#[local] Definition usim_pre := @usimX_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pre {A B}.
#[local] Definition usim_conseq := @usimX_conseq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_conseq {A B}.
#[local] Definition usim_munr := @usimX_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_munr {A B}.
#[local] Definition usim_false := @usimX_false (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_false {A B}.
#[local] Definition usim_if := @usimX_if (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_if {A B}.
#[local] Definition usim_pointwise := @usimX_pointwise (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pointwise {A B}.
#[local] Definition usim_sys := @usimX_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_sys {A B}.
#[local] Definition usim_of_paths := @usimX_of_paths (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_of_paths {A B}.
#[local] Definition usim_bind := @usimX_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind {A B A' B'}.
#[local] Definition usim_seq := @usimX_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_seq {A B A' B'}.
#[local] Definition usim_bind_eq := @usimX_bind_eq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind_eq {A A' B'}.
#[local] Definition usim_loopV := @usimX_loopV (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_loopV {X Y A B}.
(* [comment removed for export] *)
#[local] Notation framed I R := (framedX I R) (only parsing).
#[local] Definition usim_ND := fun A B p => @usimX_ND (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) A B p.
Arguments usim_ND {A B}.
#[local] Notation FOG := (uk_FOG Uk).
#[local] Notation FOC := (uk_FOC Uk).
#[local] Notation RQ_siteG := (RelX.RQ_siteG (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Notation finsens := (RelX.finsens (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Definition usim_fenter := @RelX.usimX_fenter (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fenter {A B}.
#[local] Definition usim_fret_of_ret := @RelX.usimX_fret_of_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fret_of_ret {A B}.
#[local] Definition finsens_RX := @RelX.finsens_RX (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_pure := @RelX.finsens_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_ex := @RelX.finsens_ex (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments finsens_ex {X}.
#[local] Definition finsens_mo := @RelX.finsens_mo (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
(* [comment removed for export] *)
Ltac fins_head t := lazymatch t with ?f _ => fins_head f | _ => t end.
Ltac fins :=
  lazymatch goal with
  | |- RelX.finsens _ _ _ _ _ _ _ _ _ ?R =>
      first [ apply finsens_RX; let s := fresh in let s' := fresh in let mo := fresh in let EL := fresh in let EO := fresh in let HU := fresh in
              intros s s' mo EL EO HU; unfold UK in *; rewrite EL, EO; exact HU
            | apply finsens_ex; intro; fins
            | apply finsens_pure; fins
            | apply finsens_mo; fins
            | let h := fins_head R in unfold h; fins ]
  end.
(* [comment removed for export] *)
Ltac xfe := try (apply usim_fenter; [solve [fins]|]).
Ltac xfr := xfe; try (apply usim_fret_of_ret; [solve [fins]|]).
Variables (stkG stkC : stack_site -> Z).
Definition stk_ok (stk : stack_site -> Z) : Prop := forall site, 0 <= stk site /\ stk site + 8192 < 2^64.
Hypothesis STK : stk_ok stkG.
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).
#[local] Notation PR_G := (prims HOG FOG stkG).
#[local] Notation PR_C := (prims HOC FOC stkC).

Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation P0 := (rc_P0 rc).

(* [comment removed for export] *)
Definition psize (p : pcapT) : Z := match pc_priv p with PrivPcap _ => PCAP_SF_TOTAL | PrivNg _ _ => PCAP_NG_SF_TOTAL end.
(* [comment removed for export] *)
Definition ifas (p : pcapT) : list (N * Z) :=
  match pc_priv p with PrivNg s (Some q) => [(q, ng_ifaces_size s * PCAP_NG_IF_SIZE)] | _ => [] end.
(* [comment removed for export] *)
Definition toks (p : pcapT) : list (N * Z) := (pc_buffer p, pc_bufalloc p) :: (pc_self p, psize p) :: ifas p ++ (fp, FILE_ALLOC) :: B.

(* [comment removed for export] *)
Definition KR_ (off : Z) : list kfe := Kx ++ [kat e0 off].
Definition FR_ (off pos : Z) : fpm := (fp, PR (kat e0 off) d pos) :: F0.

(* [comment removed for export] *)
Definition RP nx (p : pcapT) (tm : gmap N Z) (pt : Z) (off pos : Z) : relX :=
  fun gh sG moG sC moC => TML tm (toks p) /\ RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)) gh sG moG sC moC.

(* [comment removed for export] *)
Record PI (p : pcapT) (pos : Z) : Prop := mkPI {
  pi_pos : 0 <= pos <= Z.of_nat (length d);
  pi_buf : 1 <= pc_bufalloc p <= BUFMAX;
  pi_bsz : 1 <= pc_bufsize p <= BUFMAX;
  pi_fp : pc_rfile p = fp;
  pi_snap : match pc_priv p with PrivPcap _ => 1 <= pc_snapshot p | PrivNg _ _ => True end;
  pi_ng : match pc_priv p with
          | PrivPcap s => sf_hdrsize s = 16 \/ sf_hdrsize s = 24
          | PrivNg s i => 0 <= ng_ifcount s /\ 20 * ng_ifcount s <= pos /\ 0 <= ng_ifaces_size s <= IFSMAX
                          /\ match i with Some _ => exists k, 0 <= k /\ ng_ifaces_size s = 2 ^ k | None => ng_ifaces_size s = 0 end
                          /\ 1 <= ng_max_blocksize s <= BUFMAX
          end
}.

(* [comment removed for export] *)
#[using="Type"] Lemma toks_R63N p : R63N (map snd (toks p)) = bigb (pc_bufalloc p) + bigb (psize p) + R63N (map snd (ifas p)) + bigb FILE_ALLOC + R63N (map snd B).
Proof. unfold toks. cbn [map snd app]. rewrite !R63N_cons, map_app, R63N_app. cbn [map snd]. rewrite R63N_cons. lia. Qed.

#[using="Type"] Lemma bigb_psize p : bigb (psize p) = 0.
Proof. unfold psize. destruct (pc_priv p); apply bigb_small; unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia. Qed.
#[using="Type"] Lemma bigb_FILE : bigb FILE_ALLOC = 0.
Proof. apply bigb_small. unfold FILE_ALLOC, MMAP_THRESHOLD. lia. Qed.

#[using="Type"] Lemma ifas_R63N p pos : PI p pos -> R63N (map snd (ifas p)) <= IFSMAX * PCAP_NG_IF_SIZE + 3 * PGSZ /\ zlen (ifas p) <= 1.
Proof.
  intros [_ _ _ _ _ NG]. unfold ifas. destruct (pc_priv p) as [|s [q|]]; cbn [map snd]; rewrite ?R63N_cons, ?R63N_nil, ?zlen_cons, ?zlen_nil; try (unfold IFSMAX, PCAP_NG_IF_SIZE, PGSZ; lia).
  destruct NG as (_ & _ & SZ & _). pose proof (bigb_le (ng_ifaces_size s * PCAP_NG_IF_SIZE) ltac:(unfold PCAP_NG_IF_SIZE; lia)). unfold IFSMAX, PCAP_NG_IF_SIZE, PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Definition VIF (p : pcapT) : Z := match pc_priv p with PrivPcap _ => 0 | PrivNg s _ => 80 * ng_ifaces_size s end.
Definition PA (sl : bool) (p : pcapT) (pos : Z) (pt : Z) : Prop :=
  P0 <= pt /\ pt + (if sl then 0 else BUFMAX) <= P0 + VC0 + 2 * pos + VIF p + BUFMAX.

#[using="Type"] Lemma PA_mono sl p p' pos pos' pt : PA sl p pos pt -> pos <= pos' -> VIF p = VIF p' -> PA sl p' pos' pt.
Proof. unfold PA. intros [A B] L E. rewrite <- E. split; lia. Qed.
#[using="Type"] Lemma PA_slack sl p pos pt : PA sl p pos pt -> PA true p pos pt.
Proof. unfold PA. destruct sl; intros [A B]; split; try lia. unfold BUFMAX. lia. Qed.
#[using="Type"] Lemma PA_pay p pos pt c : PA false p pos pt -> 0 <= c <= BUFMAX -> PA true p pos (pt + c).
Proof. unfold PA. intros [A B] C. split; lia. Qed.
#[using="Type"] Lemma PA_earn p p' pos pos' pt c : PA false p pos pt -> 0 <= c -> c <= 2 * (pos' - pos) -> VIF p = VIF p' -> PA false p' pos' (pt + c).
Proof. unfold PA. intros [A B] C D E. rewrite <- E. split; lia. Qed.
(* [comment removed for export] *)
#[using="RCW"] Lemma PA_pot sl p pos pt n' : PA sl p pos pt -> PI p pos -> 0 <= n' -> n' + (if sl then BUFMAX else 0) <= BUFMAX -> 0 <= pt /\ pt + n' <= VOLMAX.
Proof.
  intros [A B] HPI Hn Hs. pose proof (rw_P0 _ RCW) as [P1 [_ P2]]. pose proof (pi_pos _ _ HPI) as PP.
  assert (VIF p <= 80 * IFSMAX).
  { unfold VIF. destruct HPI as [_ _ _ _ _ NG]. destruct (pc_priv p) as [|sng i]; [unfold IFSMAX; lia|]. destruct NG as (_ & _ & SZ & _). lia. }
  unfold V_READ in P2. pose proof (rw_d _ RCW). unfold VC0, BUFMAX, IFSMAX, MAX_INPUT in *. destruct sl; lia.
Qed.

#[using="RCW"] Lemma PA_pot0 p pos pt n' : PA false p pos pt -> PI p pos -> 0 <= n' <= BUFMAX -> 0 <= pt /\ pt + n' <= VOLMAX.
Proof. intros A B C. apply (PA_pot false p pos pt n' A B); cbn; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma liveL_cons k n L : liveL ((k, n) :: L) = n1 n + liveL L.
Proof. unfold liveL. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
#[using="Type"] Lemma liveL_app a b : liveL (a ++ b) = liveL a + liveL b.
Proof. unfold liveL. rewrite !map_app, zsum_app. reflexivity. Qed.
#[using="Type"] Lemma liveL_nonneg L : 0 <= liveL L.
Proof. unfold liveL. induction L as [|[k n] L IH]; [cbn; lia|]. cbn [map]. rewrite zsum_cons. unfold n1 at 1. lia. Qed.
#[using="Type"] Lemma live1_TML tm L : TML tm L -> live1 tm = liveL L.
Proof. intros H. unfold live1, liveL. apply zsum_perm. apply Permutation_map. exact (TML_sizes _ _ H). Qed.
#[using="Type"] Lemma liveL_lrm k n L : List.NoDup (map fst L) -> In (k, n) L -> liveL L = n1 n + liveL (lrm k L).
Proof. intros ND Hin. unfold liveL. rewrite (zsum_perm _ _ (Permutation_map n1 (Permutation_map snd (lrm_perm k n L ND Hin)))). cbn [map]. rewrite zsum_cons. reflexivity. Qed.

#[using="Type"] Lemma toks_liveL p : liveL (toks p) = n1 (pc_bufalloc p) + n1 (psize p) + liveL (ifas p) + n1 FILE_ALLOC + liveL B.
Proof. unfold toks. rewrite !liveL_cons, liveL_app, liveL_cons. lia. Qed.
#[using="Type"] Lemma ifas_liveL p pos : PI p pos -> liveL (ifas p) <= IFSMAX * PCAP_NG_IF_SIZE.
Proof.
  intros [_ _ _ _ _ NG]. unfold ifas. destruct (pc_priv p) as [|sg [q|]].
  - unfold liveL. cbn. unfold IFSMAX, PCAP_NG_IF_SIZE. lia.
  - rewrite liveL_cons. unfold liveL. cbn [map zsum fold_right]. destruct NG as (_ & _ & SZ & _). unfold n1, IFSMAX, PCAP_NG_IF_SIZE in *. lia.
  - unfold liveL. cbn. unfold IFSMAX, PCAP_NG_IF_SIZE. lia.
Qed.
(* [comment removed for export] *)
#[using="RCW"] Lemma RP_live p pos tm n' :
  PI p pos -> TML tm (toks p) -> 0 <= n' <= BUFMAX -> n' <= NMAXA /\ live1 tm + n' <= LIVEMAX /\ zlen (sizes tm) + 1 <= LIVECNT.
Proof.
  intros HPI HT Hn. pose proof (ifas_liveL p pos HPI) as IL. pose proof (rw_Blive _ RCW) as BL. pose proof (rw_B _ RCW) as [BL2 _]. destruct (ifas_R63N p pos HPI) as [_ IL2].
  pose proof (pi_buf _ _ HPI) as PB. rewrite (live1_TML _ _ HT), toks_liveL. rewrite (zlen_perm _ _ (TML_sizes _ _ HT)).
  assert (EZ : zlen (map snd (toks p)) = 3 + zlen (ifas p) + zlen B).
  { unfold zlen. rewrite length_map. unfold toks. cbn [length app]. rewrite length_app. cbn [length]. lia. }
  rewrite EZ.
  assert (N1 : forall z, 0 <= z -> n1 z <= z + 1) by (intros; unfold n1; lia).
  pose proof (N1 (pc_bufalloc p) ltac:(lia)). pose proof (N1 (psize p) ltac:(unfold psize; destruct (pc_priv p); unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL; lia)).
  assert (psize p <= 2^20) by (unfold psize; destruct (pc_priv p); unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL; lia).
  unfold n1 at 3. unfold NMAXA, LIVEMAX, LIVECNT, BUFMAX, IFSMAX, PCAP_NG_IF_SIZE, FILE_ALLOC in *. lia.
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma RP_budget p pos tm n :
  PI p pos -> TML tm (toks p) -> 0 <= n <= BUFMAX ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ bigb n <= QMAX.
Proof.
  intros HPI HT Hn. destruct (ifas_R63N p pos HPI) as [IR IL]. pose proof (rw_B _ RCW) as [BL BR].
  pose proof (pi_buf _ _ HPI) as PB. pose proof (bigb_le (pc_bufalloc p) ltac:(lia)) as BB. pose proof (bigb_le n ltac:(lia)) as BN.
  destruct (budget_of_TML tm (toks p) n HT) as [R1 R2].
  - unfold toks. rewrite !zlen_cons, zlen_app, zlen_cons. lia.
  - lia.
  - rewrite toks_R63N, bigb_psize, bigb_FILE, PHI_P9. unfold BASEB, B26, BUFMAX, IFSMAX, PCAP_NG_IF_SIZE, BLIVE, PGSZ, MAX_INPUT in *. lia.
  - split; [exact R1|]. split; [exact R2|]. unfold QMAX, BUFMAX, PGSZ in *. lia.
Qed.

#[using="RCW"] Lemma RP_budget_if p pos tm n :
  PI p pos -> TML tm (toks p) -> 0 <= n <= IFSMAX * PCAP_NG_IF_SIZE -> R63N (map snd (ifas p)) <= IFSMAX / 2 * PCAP_NG_IF_SIZE + 3 * PGSZ ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ bigb n <= QMAX.
Proof.
  intros HPI HT Hn HI. destruct (ifas_R63N p pos HPI) as [_ IL]. pose proof (rw_B _ RCW) as [BL BR].
  pose proof (pi_buf _ _ HPI) as PB. pose proof (bigb_le (pc_bufalloc p) ltac:(lia)) as BB. pose proof (bigb_le n ltac:(lia)) as BN.
  destruct (budget_of_TML tm (toks p) n HT) as [R1 R2].
  - unfold toks. rewrite !zlen_cons, zlen_app, zlen_cons. lia.
  - lia.
  - rewrite toks_R63N, bigb_psize, bigb_FILE, PHI_P9. unfold BASEB, B26, BUFMAX, IFSMAX, PCAP_NG_IF_SIZE, BLIVE, PGSZ, MAX_INPUT in *. cbn in HI. lia.
  - split; [exact R1|]. split; [exact R2|]. unfold QMAX, IFSMAX, PCAP_NG_IF_SIZE, PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma TML_perm tm L L' : TML tm L -> Permutation L L' -> TML tm L'.
Proof. intros H P. unfold TML in *. etransitivity; [exact H| exact P]. Qed.

#[using="Type"] Lemma TML_fresh tm L nx pt gh sG moG sC moC K C W :
  TML tm L -> RUK tm nx pt K C idl W gh sG moG sC moC -> ~ In nx (map fst L).
Proof.
  intros HT [HR _] Hin. apply in_map_iff in Hin as ([k n] & E & Hin). cbn in E; subst k.
  pose proof (TML_lookup _ _ _ _ HT Hin) as L1. rewrite (RQ_fresh _ _ _ _ _ _ _ _ HR) in L1. discriminate.
Qed.

#[using="Type"] Lemma gr_malloc tm L nx pt K C W n :
  TML tm L -> zlen L + 1 <= 9 -> 0 <= n < 2^40 -> bigb n <= QMAX -> PHI P9 + R63N (map snd L) + bigb n <= BLIVE ->
  0 <= pt -> pt + n1 n <= VOLMAX -> n1 n <= NMAXA -> liveL L + n1 n <= LIVEMAX ->
  usimS (RUK tm nx pt K C idl W) (pmalloc HOG n) (pmalloc HOC n)
        (eqpost (fun r => fun gh sG moG sC moC => (r = Some nx /\ TML (<[nx := n]> tm) ((nx, n) :: L)) /\ RUK (<[nx := n]> tm) (N.succ nx) (pt + n1 n) K C idl W gh sG moG sC moC)).
Proof.
  intros HT HL Hn HQ HB P1 P2 P3 P4. destruct (budget_of_TML tm L n HT HL ltac:(lia) HB) as [R1 R2].
  apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  assert (PM : pre_malloc tm pt n).
  { split; [lia|]. split; [unfold size_overflows; apply Z.leb_gt; lia|]. split; [exact HQ|]. split; [exact R1|]. split; [exact R2|].
    unfold apre. rewrite (live1_TML _ _ HT), (zlen_perm _ _ (TML_sizes _ _ HT)). unfold zlen in *. rewrite length_map. unfold LIVECNT. repeat split; lia. }
  eapply ru_post; [apply (ru_pmalloc tm nx pt _ _ n (UK_stable _ _ _ _ _) PM)|].
  intros a gh sG moG sC moC [-> H]. split; [split; [reflexivity| apply TML_insert; [exact HT| exact FR]]|]. exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ H ltac:(lia)).
Qed.

#[using="Type"] Lemma gr_calloc tm L nx pt K C W m n :
  TML tm L -> zlen L + 1 <= 9 -> 0 <= m < 2^20 -> 0 <= n < 2^20 -> m * n < MMAP_THRESHOLD -> PHI P9 + R63N (map snd L) <= BLIVE ->
  0 <= pt -> pt + n1 (m * n) <= VOLMAX -> liveL L + n1 (m * n) <= LIVEMAX ->
  usimS (RUK tm nx pt K C idl W) (pcalloc HOG m n) (pcalloc HOC m n)
        (eqpost (fun r => fun gh sG moG sC moC => (r = Some nx /\ TML (<[nx := m * n]> tm) ((nx, m * n) :: L)) /\ RUK (<[nx := m * n]> tm) (N.succ nx) (pt + n1 (m * n)) K C idl W gh sG moG sC moC)).
Proof.
  intros HT HL Hm Hn Hmn HB P1 P2 P4. pose proof (bigb_small (m * n) Hmn) as B0. unfold MMAP_THRESHOLD in Hmn.
  destruct (budget_of_TML tm L (m * n) HT HL ltac:(lia) ltac:(lia)) as [R1 R2].
  apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  assert (PM : pre_calloc tm pt m n).
  { split; [lia|]. split; [lia|]. split.
    { destruct (Z.eqb_spec n 0) as [->|NZ]; [reflexivity|]. cbn [negb andb]. apply Z.ltb_ge. apply Z.div_le_lower_bound; unfold SIZE_MAX; lia. }
    split; [unfold size_overflows; apply Z.leb_gt; lia|]. split; [rewrite B0; unfold QMAX; lia|]. split; [exact R1|]. split; [exact R2|].
    unfold apre. rewrite (live1_TML _ _ HT), (zlen_perm _ _ (TML_sizes _ _ HT)). unfold zlen in *. rewrite length_map. unfold LIVECNT, NMAXA, n1 in *. repeat split; lia. }
  eapply ru_post; [apply (ru_pcalloc tm nx pt _ _ m n (UK_stable _ _ _ _ _) PM)|].
  intros a gh sG moG sC moC [-> H]. split; [split; [reflexivity| apply TML_insert; [exact HT| exact FR]]|]. exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ H ltac:(lia)).
Qed.

#[using="Type"] Lemma gr_free tm L nx pt K C W k n :
  TML tm L -> In (k, n) L -> PHI P9 + R63N (map snd L) <= BLIVE ->
  usimS (RUK tm nx pt K C idl W) (pfree HOG k) (pfree HOC k)
        (eqpost (fun _ => fun gh sG moG sC moC => TML (delete k tm) (lrm k L) /\ RUK (delete k tm) nx pt K C idl W gh sG moG sC moC)).
Proof.
  intros HT Hin HB. eapply ru_post; [apply (ru_pfree tm nx pt _ _ k n (UK_stable _ _ _ _ _)); split; [exact (TML_lookup _ _ _ _ HT Hin)| rewrite (R63N_perm _ _ (TML_sizes _ _ HT)); exact HB]|].
  intros [] gh sG moG sC moC H. split; [apply (TML_delete _ _ _ _ HT Hin)| exact H].
Qed.

#[using="Type"] Lemma gr_realloc tm L nx pt K C W k n n' :
  TML tm L -> In (k, n) L -> zlen L + 1 <= 9 -> 1 <= n' < 2^40 -> bigb n' <= QMAX -> PHI P9 + R63N (map snd L) + bigb n' <= BLIVE ->
  0 <= pt -> pt + n' <= VOLMAX -> n' <= NMAXA -> liveL L + n' <= LIVEMAX ->
  usimS (RUK tm nx pt K C idl W) (prealloc HOG k n') (prealloc HOC k n')
        (eqpost (fun r => fun gh sG moG sC moC => (r = Some nx /\ TML (<[nx := n']> (delete k tm)) ((nx, n') :: lrm k L)) /\
                   RUK (<[nx := n']> (delete k tm)) (N.succ nx) (pt + n') K C idl W gh sG moG sC moC)).
Proof.
  intros HT Hin HL Hn HQ HB P1 P2 P3 P4. destruct (budget_of_TML tm L n' HT HL ltac:(lia) HB) as [R1 R2].
  apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  assert (PM : pre_realloc tm pt k n n').
  { split; [exact (TML_lookup _ _ _ _ HT Hin)|]. split; [lia|]. split; [unfold size_overflows; apply Z.leb_gt; lia|]. split; [unfold LEN_MAX, PGSZ; lia|]. split; [exact HQ|]. split; [exact R1|]. split; [exact R2|].
    unfold apre. rewrite (live1_TML _ _ HT), (zlen_perm _ _ (TML_sizes _ _ HT)). unfold zlen in *. rewrite length_map. unfold LIVECNT. repeat split; lia. }
  eapply ru_post; [apply (ru_prealloc tm nx pt _ _ k n n' (UK_stable _ _ _ _ _) PM)|].
  intros a gh sG moG sC moC [-> H]. split; [split; [reflexivity|]|].
  - apply TML_insert; [apply (TML_delete _ _ _ _ HT Hin)|]. intros Hin'. apply FR. apply in_map_iff in Hin' as ([k' v] & E & Hin'). cbn in E; subst k'.
    apply in_map_iff. exists (nx, v). split; [reflexivity|]. eapply Permutation_in; [symmetry; apply (lrm_perm k n L (TML_nodup _ _ HT) Hin)|]. right. exact Hin'.
  - exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ H ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fdel_notin h (F : fpm) : ~ In h (map fst F) -> fdel h F = F.
Proof.
  induction F as [|[h' P] F IH]; intros NI; [reflexivity|]. unfold fdel. cbn. destruct (N.eqb_spec h' h) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  cbn. f_equal. apply IH. intros X; apply NI; right; exact X.
Qed.

#[using="Type"] Lemma KR_in off : In (kat e0 off) (KR_ off).
Proof. unfold KR_. apply in_app_iff. right. left. reflexivity. Qed.
#[using="RCW"] Lemma KR_kset off off' : kset (kat (kat e0 off) off') (KR_ off) = KR_ off'.
Proof.
  unfold KR_. rewrite kat_kat. apply kset_snoc_new; [| reflexivity]. intros x Hx. cbn. exact (rw_Kx _ RCW x Hx).
Qed.
#[using="Type"] Lemma FR_in off pos : In (fp, PR (kat e0 off) d pos) (FR_ off pos).
Proof. left. reflexivity. Qed.
#[using="RCW"] Lemma FR_fupd off pos P : fupd fp P (FR_ off pos) = (fp, P) :: F0.
Proof. unfold fupd, FR_. cbn. rewrite N.eqb_refl. cbn. f_equal. apply (fdel_notin fp F0). exact (rw_F0 _ RCW). Qed.
#[using="RCW"] Lemma own_kat off : k_own (kat e0 off) = Some fp.
Proof. unfold kat, kmove. cbn. exact (rw_own _ RCW). Qed.
#[using="Type"] Lemma toks_fp p : In (fp, FILE_ALLOC) (toks p).
Proof. unfold toks. right. right. apply in_app_iff. right. left. reflexivity. Qed.
#[using="Type"] Lemma toks_buf p : In (pc_buffer p, pc_bufalloc p) (toks p).
Proof. left. reflexivity. Qed.
#[using="Type"] Lemma toks_self p : In (pc_self p, psize p) (toks p).
Proof. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Definition rdest_ok (p : pcapT) (dst : rdest hptr) (n : Z) : Prop :=
  match dst with
  | DHeap q o => q = pc_buffer p /\ 0 <= o /\ o + n <= 2^40
  | DStack site o => 0 <= o /\ o + n <= 8192
  end.

#[using="STK"] Lemma eval_rdest_ok p dst n tm nx pt K C W gh sG moG sC moC :
  TML tm (toks p) -> RUK tm nx pt K C idl W gh sG moG sC moC -> rdest_ok p dst n -> 0 <= n ->
  0 <= eval_rdest HOG FOG stkG sG dst /\ eval_rdest HOG FOG stkG sG dst + n < 2^64.
Proof.
  intros HT [HR _] HD Hn. unfold eval_rdest. destruct dst as [q o|site o]; cbn in HD.
  - destruct HD as (-> & Ho & Hon). pose proof (RQ_blk_addr _ _ _ _ _ _ _ _ _ _ _ HR (TML_lookup _ _ _ _ HT (toks_buf p))) as (A1 & A2 & A3).
    lia.
  - destruct (fo_site FOG sG site) as [a|] eqn:ES; [destruct (RQ_siteG _ _ _ _ _ _ _ _ _ _ HR ES) as [S1 S2]; lia|].
    destruct (STK site) as [S1 S2]. lia.
Qed.

(* [comment removed for export] *)
#[using="STK RCW"] Lemma pr_fread nx p tm pt off pos dst n :
  PI p pos -> TML tm (toks p) -> rdest_ok p dst n -> 0 <= n < 2^40 ->
  usimS (RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)))
        (e_fread PR_G fp dst n) (e_fread PR_C fp dst n)
        (eqpost (fun r => fun gh sG moG sC moC => exists off',
           (zlength r <= n /\ (zlength r < n -> pos + zlength r = Z.of_nat (length d)) /\ pos + zlength r <= Z.of_nat (length d) /\ r = dsl d pos (zlength r)) /\
           RUK tm nx pt (KR_ off') Cc idl (WF oh hs (FR_ off' (pos + zlength r))) gh sG moG sC moC)).
Proof.
  intros HPI HT HD Hn. cbn [e_fread prims].
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros gh0 sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  pose proof (eval_rdest_ok p dst n tm nx pt _ _ _ _ _ _ _ _ HT HR0 HD ltac:(lia)) as [D1 D2].
  eapply ru_pre; [| intros ? ? ? ? ? (-> & -> & -> & -> & ->); exact HR0].
  eapply ru_post; [apply (us_fread Uk tm nx pt (KR_ off) Cc oh hs (FR_ off pos) fp (kat e0 off) d pos _ _ n (KR_in off) (own_kat off) (rw_hs _ RCW) (FR_in off pos)
                          (TML_lookup _ _ _ _ HT (toks_fp p)) ltac:(lia) D1 D2)|].
  intros r gh sG moG sC moC (off' & (Q1 & Q2 & Q3 & Q4 & Q5) & H). exists off'. rewrite KR_kset, FR_fupd in H. split; [| exact H]. auto.
Qed.

#[using="RCW"] Lemma pr_ferror nx tm pt off pos :
  usimS (RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos))) (e_ferror PR_G fp) (e_ferror PR_C fp)
        (eqpost (fun r => fun gh sG moG sC moC => r = false /\ RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)) gh sG moG sC moC)).
Proof. cbn [e_ferror prims]. apply (us_ferror Uk tm nx pt _ _ oh hs _ fp (kat e0 off) _ (KR_in off) (own_kat off) (rw_hs _ RCW) (FR_in off pos)). Qed.

#[using="RCW"] Lemma pr_fileno nx tm pt off pos :
  usimS (RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos))) (e_fileno PR_G fp) (e_fileno PR_C fp)
        (eqpost (fun r => fun gh sG moG sC moC => r = k_fd e0 /\ RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)) gh sG moG sC moC)).
Proof. cbn [e_fileno prims]. apply (us_fileno Uk tm nx pt _ _ oh hs _ fp (kat e0 off) _ (KR_in off) (own_kat off) (rw_hs _ RCW) (FR_in off pos)). Qed.

#[using="Type"] Lemma pr_errno tm nx pt K C oh' hs' F :
  usimS (RUK tm nx pt K C idl (WF oh' hs' F)) (e_last_errno PR_G) (e_last_errno PR_C) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh' hs' F))).
Proof. cbn [e_last_errno prims]. apply us_get_errno. Qed.

#[using="Type"] Lemma pr_errmsg tm nx pt K C oh' hs' F f args :
  usimS (RUK tm nx pt K C idl (WF oh' hs' F)) (errmsg_for_errno MOps PR_G f args) (errmsg_for_errno MOps PR_C f args)
        (eqpost (fun r => fun gh sG moG sC moC => mok r /\ RUK tm nx pt K C idl (WF oh' hs' F) gh sG moG sC moC)).
Proof.
  unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe. eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh' hs' F).
  - eapply ru_post; [apply pr_errno|]. intros ? ? ? ? ? ? H; exact (conj I H).
  - intros e _. xfr; apply ru_ret. intros. split; [apply mok_fmt_errmsg| assumption].
Qed.

#[using="RCW"] Lemma pr_read_fail_msg nx tm pt off pos msg :
  mok msg ->
  usimS (RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos))) (read_fail_msg MOps PR_G fp msg) (read_fail_msg MOps PR_C fp msg)
        (eqpost (fun r => fun gh sG moG sC moC => mok r /\ RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)) gh sG moG sC moC)).
Proof.
  intros Hm. unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe. eapply ruk_bind with (K1 := fun _ => KR_ off) (C1 := fun _ => Cc) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (FR_ off pos)); [apply (pr_ferror nx)|].
  intros e ->. cbn. xfr; apply ru_ret. intros. split; [exact Hm| assumption].
Qed.

End Reading.

End WithCeil.
