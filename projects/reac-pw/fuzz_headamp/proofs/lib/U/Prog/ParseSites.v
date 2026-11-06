(** The call sites of the callee contracts inside reac_headamp_prop_parse_result (UBSan): what the parse walk must show
    at each, and closed lemmas for the parts that follow from the parse contract's own premises (parse_args, the stack)
    and from what the parse itself writes (parse_writes). Nothing of a binary is proved here.
    - strtol (U/Prog/strtol_c.v strtol_contract) at 0x14ef8 `jal 0x1ce98`, with sp = the parse's sp - 0x90, a0 = rest =
      key + 13, a1 = the dot cell sp - 0x90 + 0x18, a2 = 10: [strtol_pre] is strtol_contract's
      premise list; [strtol_site] gives it from parse_args, the stack, the parse's writes so far, errno a cell, the key
      string inside the pod and the dot cell; [strtol_use] applies the contract.
    - strncmp (U/Prog/strncmp_c.v strncmp_contract) at 0x14ea0 `jal 0x1dd0c`, a0 = key, a1 = 0x102bd ("reac.headamp."),
      a2 = 13; strcmp (U/Prog/strcmp_c.v strcmp_contract, from the slot kit) at 0x14f34 / 0x14f48 / 0x14f5c (`jal
      0x1dc44`), a0 = dot + 1, a1 = "phantom" 0x1032f, "pad" 0x1045f, "sens" 0x102b8: the walk shows the key / name bytes
      (inside the pod: [pod_kept] carries them across the parse's writes) and the literals are read-only image bytes
      ([lit_prefix], [lit_phantom], [lit_pad], [lit_sens], [lits_at]). The value of strncmp_model on the key against
      the prefix is the walk's (or the model's) lemma: v = 0 iff Pod/Headamp.v ha_prefix key. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c strtol_c.
Import ListNotations.
Open Scope Z_scope.

(** The dot cell (char *dot) in the parse's frame: sp_p + 0x18 (0x14efc `ld a3,0x18(sp)` reads it after strtol). *)
Definition PARSE_DOT : Z := 0x18.

Lemma stk_lower : forall m lo hi hi', stk rsegs m lo hi -> lo <= hi' <= hi -> stk rsegs m lo hi'.
Proof. intros m lo hi hi' (H0 & H1 & H) Hh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

(** ** The pod's bytes across the parse's own writes *)
Lemma pod_kept : forall m m1 lo sp tp P O cap R bs ev can n A xs,
  parse_args m lo sp tp P O cap R bs ev can -> lo + PARSE_STACK <= sp -> 0 <= n <= cap ->
  munch (parse_writes sp O n (PARSE_ERRNO tp) R) m m1 ->
  P <= A -> A + Z.of_nat (length xs) <= P + Z.of_nat (length bs) ->
  bytes_at rsegs m A xs -> bytes_at rsegs m1 A xs.
Proof.
  intros m m1 lo sp tp P O cap R bs ev can n A xs HA Hst Hn HM H1 H2 HB.
  destruct HA as (_ & _ & _ & _ & _ & HPlo & Hcap & _ & _ & HOlo & HOP & HR & _ & HEd & _).
  eapply bytes_at_transport; [exact HB | exact HM |].
  cbn [disjoint_from] in HEd. unfold parse_writes, PARSE_STACK in *.
  destruct (R =? 0) eqn:ER; cbn [app disjoint_from].
  - repeat split; lia.
  - apply Z.eqb_neq in ER. destruct HR as [HR | (_ & _ & HR)]; [contradiction|]. repeat split; lia.
Qed.

(** The SSP cells (or any region apart from every region the parse may write) across the parse's own writes. *)
Lemma ssp_kept : forall m m1 lo sp tp P O cap R bs ev can n X xs,
  parse_args m lo sp tp P O cap R bs ev can -> lo + PARSE_STACK <= sp -> 0 <= n <= cap ->
  munch (parse_writes sp O n (PARSE_ERRNO tp) R) m m1 ->
  disjoint_from (parse_space lo sp O cap (PARSE_ERRNO tp) R) X (Z.of_nat (length xs)) ->
  bytes_at rsegs m X xs -> bytes_at rsegs m1 X xs.
Proof.
  intros m m1 lo sp tp P O cap R bs ev can n X xs HA Hst Hn HM HD HB.
  eapply bytes_at_transport; [exact HB | exact HM |].
  unfold parse_writes, parse_space, PARSE_STACK in *.
  destruct (R =? 0); cbn [app disjoint_from] in *; repeat split; lia.
Qed.

(** ** strtol *)
Definition strtol_pre (m : word -> option byte) (sp tp : word) (lo A Ep : Z) (str : list byte) (ev can e0 : word)
    : Prop :=
  bytes_at rsegs m A (str ++ [Z_to_bv 8 0]) /\ A + Z.of_nat (length str) + 1 < 2^64 /\
  0 < Ep /\ rw_cells rsegs m Ep [C8 e0] /\
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] /\
  bytes_at rsegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) /\ bytes_at rsegs m STRTOL_SSP_GUARD (le8 can) /\
  stk rsegs m lo (bv_unsigned sp) /\ lo + 368 <= bv_unsigned sp /\
  (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) /\
  (Ep + 8 <= lo \/ bv_unsigned sp <= Ep) /\
  (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) /\
  (Ep + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= Ep) /\
  (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) /\
  (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) /\
  (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) /\
  (STRTOL_SSP_GUARD + 8 <= Ep \/ Ep + 8 <= STRTOL_SSP_GUARD) /\
  mem_inv rsegs m.

Lemma strtol_use : strtol_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Ep : Z) (str : list byte) (ev can e0 : word)
         (lo : Z),
    strtol_pre m sp tp lo A Ep str ev can e0 ->
    evt rsegs (strtol_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Ep str ev lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 Ep) (Z_to_bv 64 10) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRTOL) fc None m (seg_rom rsegs)).
Proof.
  intros HC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Ep str
    ev can e0 lo (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
  exact (HC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Ep str
           ev can e0 lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18).
Qed.

(** At 0x14ef8: from the parse contract's premises at its entry memory m, the memory m1 at the call (the parse wrote
    only inside parse_writes so far, kept the stack writable, errno a cell), the key string after the prefix at A
    inside the pod, and the dot cell: strtol_contract's premises at sp_p = sp - 0x90 with the same lo. *)
Lemma strtol_site : forall m m1 lo (sp tp : word) P O cap R bs ev can n A str Ep e0 ev1,
  parse_args m lo (bv_unsigned sp) tp P O cap R bs ev can -> lo + PARSE_STACK <= bv_unsigned sp -> 0 <= n <= cap ->
  munch (parse_writes (bv_unsigned sp) O n (PARSE_ERRNO tp) R) m m1 ->
  P <= A -> A + Z.of_nat (length str) + 1 <= P + Z.of_nat (length bs) ->
  bytes_at rsegs m A (str ++ [Z_to_bv 8 0]) ->
  stk rsegs m1 lo (bv_unsigned sp) -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 (PARSE_ERRNO tp) [C4 ev1] ->
  Ep = bv_unsigned sp - PARSE_FRAME + PARSE_DOT -> rw_cells rsegs m1 Ep [C8 e0] ->
  strtol_pre m1 (Z_to_bv 64 (bv_unsigned sp - PARSE_FRAME)) tp lo A Ep str ev1 can e0.
Proof.
  intros m m1 lo sp tp P O cap R bs ev can n A str Ep e0 ev1 HA Hst Hn HM HA1 HA2 HB Hstk HMI HE -> HD.
  pose proof HA as (_ & _ & _ & _ & _ & HPlo & Hcap & _ & _ & HOlo & _ & HR & _ & HEd & HRE & HG1 & HG2 & HGd1 & HGd2).
  pose proof Hstk as (Hlo0 & Hsp64 & _).
  assert (HB1 : bytes_at rsegs m1 A (str ++ [Z_to_bv 8 0])).
  { eapply pod_kept; [exact HA | exact Hst | exact Hn | exact HM | exact HA1 | | exact HB].
    rewrite length_app. cbn [length]. lia. }
  assert (HG1' : bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD))).
  { eapply ssp_kept; [exact HA | exact Hst | exact Hn | exact HM | | exact HG1]. rewrite length_le8. exact HGd1. }
  assert (HG2' : bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can)).
  { eapply ssp_kept; [exact HA | exact Hst | exact Hn | exact HM | | exact HG2]. rewrite length_le8. exact HGd2. }
  assert (G : forall X, disjoint_from (parse_space lo (bv_unsigned sp) O cap (PARSE_ERRNO tp) R) X 8 ->
             (X + 8 <= lo \/ bv_unsigned sp <= X) /\ (X + 8 <= PARSE_ERRNO tp \/ PARSE_ERRNO tp + 4 <= X)).
  { intros X HX. unfold parse_space in HX. destruct (R =? 0); cbn [app disjoint_from] in HX; tauto. }
  destruct (G _ HGd1) as [G1a G1b]. destruct (G _ HGd2) as [G2a G2b].
  cbn [disjoint_from] in HEd.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - PARSE_FRAME)) = bv_unsigned sp - PARSE_FRAME).
  { apply MState.unsigned_lit. unfold PARSE_STACK, PARSE_FRAME in *. lia. }
  unfold strtol_pre. rewrite Esp. change STRTOL_SSP_GOT with PARSE_SSP_GOT. change STRTOL_SSP_GUARD with PARSE_SSP_GUARD.
  unfold PARSE_ERRNO in *. unfold PARSE_STACK, PARSE_FRAME, PARSE_DOT in *.
  refine (conj HB1 (conj _ (conj _ (conj HD (conj HE (conj HG1' (conj HG2' (conj _ _)))))))).
  - lia.
  - lia.
  - eapply stk_lower; [exact Hstk | lia].
  - repeat split; try lia. exact HMI.
Qed.

(** ** strncmp and strcmp: the literals are read-only image bytes *)
Fixpoint ro_bytesb (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom rsegs (wa a) with Some b' => (bv_unsigned b' =? bv_unsigned b) | None => false end &&
      ro_addr rsegs (wa a) && ro_bytesb (a + 1) bs'
  end.

Lemma ro_bytesb_sound : forall bs a, ro_bytesb a bs = true -> ro_bytes rsegs a bs.
Proof.
  induction bs as [|b bs IH]; intros a H; cbn [ro_bytes]; [exact I|]. cbn [ro_bytesb] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [|exact (IH _ H3)]. unfold ro_byte. split; [|exact H2].
  destruct (seg_rom rsegs (wa a)) as [b'|]; [|discriminate H1]. apply Z.eqb_eq in H1. f_equal. apply bv_eq. exact H1.
Qed.

Definition LIT_PREFIX : Z := 0x102bd.
Definition LIT_PHANTOM : Z := 0x1032f.
Definition LIT_PAD : Z := 0x1045f.
Definition LIT_SENS : Z := 0x102b8.

Lemma lit_prefix : ro_bytes rsegs LIT_PREFIX (HA_PREFIX ++ [NUL]).
Proof. apply ro_bytesb_sound. vm_compute. reflexivity. Qed.
Lemma lit_phantom : ro_bytes rsegs LIT_PHANTOM (NAME_PHANTOM ++ [NUL]).
Proof. apply ro_bytesb_sound. vm_compute. reflexivity. Qed.
Lemma lit_pad : ro_bytes rsegs LIT_PAD (NAME_PAD ++ [NUL]).
Proof. apply ro_bytesb_sound. vm_compute. reflexivity. Qed.
Lemma lit_sens : ro_bytes rsegs LIT_SENS (NAME_SENS ++ [NUL]).
Proof. apply ro_bytesb_sound. vm_compute. reflexivity. Qed.

Lemma lits_at : forall m, mem_inv rsegs m ->
  bytes_at rsegs m LIT_PREFIX (HA_PREFIX ++ [NUL]) /\ bytes_at rsegs m LIT_PHANTOM (NAME_PHANTOM ++ [NUL]) /\
  bytes_at rsegs m LIT_PAD (NAME_PAD ++ [NUL]) /\ bytes_at rsegs m LIT_SENS (NAME_SENS ++ [NUL]).
Proof.
  intros m HM.
  split; [apply ro_bytes_at; [exact HM | unfold LIT_PREFIX; lia | vm_compute; intros Hc; discriminate Hc | exact lit_prefix]|].
  split; [apply ro_bytes_at; [exact HM | unfold LIT_PHANTOM; lia | vm_compute; intros Hc; discriminate Hc | exact lit_phantom]|].
  split; [apply ro_bytes_at; [exact HM | unfold LIT_PAD; lia | vm_compute; intros Hc; discriminate Hc | exact lit_pad]|].
  apply ro_bytes_at; [exact HM | unfold LIT_SENS; lia | vm_compute; intros Hc; discriminate Hc | exact lit_sens].
Qed.
