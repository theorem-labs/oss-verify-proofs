(** The tables and strings ent_build's kinds 0 and 1 read, as the walk needs them: the .data.rel.ro pointer tables
    vocab and odd_ch read through MemC (the contract's RELRO premise), and each string with its NUL and the bytes
    strlen reads after it (to the next 8-byte boundary), present in the image's read-only bytes and apart from the
    stack. Checked on the plain image by computation. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout RoleImg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** The pointer tables of .data.rel.ro: vocab (9) then odd_ch (14), 8 bytes each, from RELRO_TBL *)
Definition relro_ptrs : list Z := pa_vocab_s role_plain_addrs ++ pa_odd_s role_plain_addrs.

Lemma relro_rom : forall a, RELRO_TBL <= a < RELRO_TBL_END -> seg_rom rsegs (wa a) <> None.
Proof. intros a Ha. apply (rom_range RELRO_TBL 184); [vm_compute; reflexivity | unfold RELRO_TBL_END in Ha; exact Ha]. Qed.

Definition bytes_eqo (o : option (list byte)) (l : list byte) : bool :=
  match o with Some bs => bytes_eqb bs l | None => false end.

Lemma bytes_eqo_eq : forall o l, bytes_eqo o l = true -> o = Some l.
Proof.
  intros [bs|] l H; cbn [bytes_eqo] in H; [|discriminate]. apply bytes_eqb_eq in H. subst. reflexivity.
Qed.

Lemma relro_image : forallb (fun j => bytes_eqo (rdn rsegs (fun _ => None) (wa (RELRO_TBL + 8 * Z.of_nat j)) 8)
                                               (le8 (Z_to_bv 64 (nth j relro_ptrs 0)))) (seq 0 23) = true.
Proof. vm_compute. reflexivity. Qed.

Section Tbl.
Variables (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma rdn_relro : forall m1 eb n a, MemC sp m r src pp lo m1 eb -> RELRO_TBL <= a ->
  a + Z.of_nat n <= RELRO_TBL_END -> rdn rsegs m1 (wa a) n = rdn rsegs (fun _ => None) (wa a) n.
Proof.
  intros m1 eb n. induction n as [|n IH]; intros a MC H1 H2; [reflexivity|].
  cbn [rdn]. rewrite (wa_succ a). rewrite (IH (a + 1) MC) by lia.
  pose proof (MemC_relro sp m r src pp lo HE m1 eb a MC ltac:(lia) (relro_rom a ltac:(lia))) as T.
  unfold mrd in T. rewrite T. reflexivity.
Qed.

(** The pointer j of the tables (vocab j for j < 9, odd_ch (j - 9) else). *)
Lemma relro_read : forall m1 eb (j : nat), MemC sp m r src pp lo m1 eb -> (j < 23)%nat ->
  ov_read_bytes rsegs m1 (wa (RELRO_TBL + 8 * Z.of_nat j)) 8 = Some (le8 (Z_to_bv 64 (nth j relro_ptrs 0))).
Proof.
  intros m1 eb j MC Hj. rewrite ov_rdn. rewrite (rdn_relro m1 eb 8 _ MC) by (unfold RELRO_TBL, RELRO_TBL_END; lia).
  apply bytes_eqo_eq. pose proof relro_image as H. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

End Tbl.

(** ** C strings of the image *)
(** The 7 bytes of the image after a (what strlen may read after a NUL, to the next 8-byte boundary). *)
Definition slack_of (a : Z) : list byte := match image_bytes rsegs a 7 with Some l => l | None => [] end.

Definition str_ok (p : Z) (s : list byte) : bool :=
  ro_bytes_b rsegs p (s ++ NUL :: slack_of (p + Z.of_nat (length s) + 1)) &&
  ((- (p + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length (slack_of (p + Z.of_nat (length s) + 1)))) &&
  no_nul s && forallb (fun j => rom_some (p + Z.of_nat j)) (seq 0 (S (length s))) &&
  (0 <=? p) && (p + Z.of_nat (length s) + 8 <=? 2^32).

Lemma no_nul_not_in : forall s, no_nul s = true -> ~ In NUL s.
Proof.
  induction s as [|x s IH]; intros H Hin; [exact Hin|]. cbn [no_nul forallb] in H.
  apply andb_prop in H as [H1 H2]. destruct Hin as [E|Hin].
  - subst x. vm_compute in H1. discriminate H1.
  - exact (IH H2 Hin).
Qed.

Lemma str_ok_facts : forall m1 p s, mem_inv rsegs m1 -> str_ok p s = true ->
  bytes_at rsegs m1 p (s ++ NUL :: slack_of (p + Z.of_nat (length s) + 1)) /\
  (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length (slack_of (p + Z.of_nat (length s) + 1))) /\
  ~ In NUL s /\
  forallb (fun j => rom_some (p + Z.of_nat j)) (seq 0 (S (length s))) = true /\ 0 <= p /\
  p + Z.of_nat (length s) + 8 <= 2^32.
Proof.
  intros m1 p s MI H. unfold str_ok in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H6. apply Z.leb_le in H5.
  assert (L : Z.of_nat (length (slack_of (p + Z.of_nat (length s) + 1))) <= 7).
  { unfold slack_of. destruct (image_bytes rsegs (p + Z.of_nat (length s) + 1) 7) eqn:E; [|cbn; lia].
    rewrite (image_bytes_length rsegs 7 _ _ E). lia. }
  split; [apply image_bytes_at; [exact MI | exact H1 | lia | rewrite length_app; cbn [length]; lia]|].
  split; [exact H2|]. split; [apply no_nul_not_in; exact H3|]. split; [exact H4|]. lia.
Qed.

(** The strings of a table of pointers ps to the texts ss. *)
Definition strs_ok (ps : list Z) (ss : list (list byte)) : bool :=
  forallb (fun j => str_ok (nth j ps 0) (nth j ss [])) (seq 0 (length ss)).

Lemma strs_ok_nth : forall ps ss j, strs_ok ps ss = true -> (j < length ss)%nat -> str_ok (nth j ps 0) (nth j ss []) = true.
Proof. intros ps ss j H Hj. unfold strs_ok in H. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Lemma vocab_strs : strs_ok (pa_vocab_s role_plain_addrs) vocab = true.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_strs : strs_ok (pa_odd_s role_plain_addrs) odd_ch = true.
Proof. vm_compute. reflexivity. Qed.

Lemma param_strs : strs_ok (pa_param_s role_plain_addrs) param = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fixed_strs : str_ok (pa_hpfx role_plain_addrs) HPFX && str_ok (pa_dot role_plain_addrs) DOT &&
  str_ok (pa_empty role_plain_addrs) [] && str_ok (pa_s9 role_plain_addrs) S9 = true.
Proof. vm_compute. reflexivity. Qed.
