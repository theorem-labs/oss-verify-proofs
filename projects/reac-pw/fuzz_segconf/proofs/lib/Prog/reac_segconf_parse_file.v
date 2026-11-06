(** reac_segconf_parse_file (plain build, 0x14cbc): the whole function from its nine pieces (family F3,
    reac_segconf_parse_file_pieces_c.v). Written new.

    [pieces_give_contract_holds]: the pieces give H_TAIL n for every n by induction on n (H_TAIL 0 holds outright:
    its rest would be shorter than 0; H_TAIL (S n) is P2's tail from H_HEAD n, and H_HEAD n is P2's head from the
    mid-line cuts at n, each of which the pieces reduce to H_TAIL n), so H_HEAD n for every n, then S_P1 gives the
    contract. No binary fact is used here: the pieces carry them all.

    [reac_segconf_parse_file_holds]: the contract from the callee contracts, through the nine piece theorems
    pf_p1_holds .. pf_p9_holds (Prog/pf_p1.v .. pf_p9.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import
  reac_segconf_parse_file_c reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require
  snprintf_c strchr_c strlen_c memcpy_c trim_c strspn_c refuse_c strncasecmp_c strcmp_c memset_c strcasecmp_c
  bcmp_c reac_box_catalogue_by_token_c reac_box_catalogue_c
  pf_p1 pf_p2 pf_p3 pf_p4 pf_p5 pf_p6 pf_p7 pf_p8 pf_p9.
Import ListNotations.

Section Compose.
Hypotheses (P1 : S_P1) (P2 : S_P2) (P3 : S_P3) (P4 : S_P4) (P5 : S_P5) (P6 : S_P6) (P7 : S_P7) (P8 : S_P8)
  (P9 : S_P9).

(** A rest shorter than 0 does not exist. *)
Lemma tail_zero : H_TAIL 0.
Proof. unfold H_TAIL. intros * _ _ Hn. exfalso. exact (Nat.nlt_0_r _ Hn). Qed.

(** Every mid-line cut at n reduces to H_TAIL n, so P2's head does too. *)
Lemma head_of_tail : forall n, H_TAIL n -> H_HEAD n.
Proof.
  intros n T.
  destruct (P9 n) as (K9 & R9 & N9 & V9 & M9 & C9).
  destruct (P3 n) as [L3 O3]. destruct (P5 n) as [K5 S5]. destruct (P6 n) as [R6 I6].
  apply (proj1 (P2 n)).
  - exact (L3 T).
  - exact (P4 n T (C9 T)).
  - apply K5.
    + exact (O3 T).
    + exact (R6 (I6 (R9 T) (V9 T))).
    + exact (P7 n (M9 T) (S5 T)).
    + exact (P8 n (R9 T) (V9 T)).
    + exact (K9 T).
    + exact (N9 T).
    + exact T.
  - exact T.
Qed.

Lemma tail_all : forall n, H_TAIL n.
Proof.
  induction n as [|n IH]; [exact tail_zero|].
  apply (proj2 (P2 (S n))); [cbn [pred]; exact (head_of_tail n IH) | exact (proj1 P1)].
Qed.

Lemma contract_of_pieces : reac_segconf_parse_file_contract.
Proof. exact (proj2 P1 (fun n => head_of_tail n (tail_all n)) (proj1 P1)). Qed.

End Compose.

Theorem pieces_give_contract_holds : pieces_give_contract.
Proof. unfold pieces_give_contract. exact contract_of_pieces. Qed.

(** The function from its callee contracts. *)
Theorem reac_segconf_parse_file_holds :
  snprintf_c.snprintf_contract -> strchr_c.strchr_contract -> strlen_c.strlen_contract ->
  memcpy_c.memcpy_contract -> trim_c.trim_contract -> strspn_c.strspn_contract -> refuse_c.refuse_contract ->
  strncasecmp_c.strncasecmp_contract -> strcmp_c.strcmp_contract -> memset_c.memset_contract ->
  strcasecmp_c.strcasecmp_contract -> bcmp_c.bcmp_contract ->
  reac_box_catalogue_by_token_c.reac_box_catalogue_by_token_contract ->
  reac_box_catalogue_c.reac_box_catalogue_contract ->
  reac_segconf_parse_file_contract.
Proof.
  intros SN SC SL MC TR SS RF SNC SCM MS SCC BC BT BX.
  exact (contract_of_pieces
           (pf_p1.pf_p1_holds SN) (pf_p2.pf_p2_holds SC SL MC TR) (pf_p3.pf_p3_holds SS RF)
           (pf_p4.pf_p4_holds SC TR SNC SL RF SCM MS SN) (pf_p5.pf_p5_holds SC TR SL RF SCC)
           (pf_p6.pf_p6_holds BC) (pf_p7.pf_p7_holds SN RF BT BX) (pf_p8.pf_p8_holds SCC)
           (pf_p9.pf_p9_holds RF SN)).
Qed.
