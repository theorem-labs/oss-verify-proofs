(* Satisfiability witnesses of the function-specific Pre of the two image-A exemplars (fuzz_close_c.v, copy_attr_c.v), at memories
   holding the values a real run holds at the call (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) sections
   1 and 2: fuzz_close from nl_talk 0x88e54 after one exchange; copy_attr from nl_talk 0x88d00 on an IFLA_IFALIAS attribute
   "ab" into op_read's 16-byte alias buffer). The journal part of the Pre (link_amem.v `apre`) needs AR of image A's start
   state, which the start-up files give; it is written out in link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f).
   Each lemma holds for every segment list: the witness memory holds every byte the Pre reads, so no ROM byte is read.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem fuzz_close_c copy_attr_c.
Import ListNotations.
Local Open Scope Z_scope.

(* little-endian bytes, and a field store into a byte list *)
Definition wle_bytes (n : nat) (v : Z) : list byte :=
  map (fun k => zb ((v / 2 ^ (8 * Z.of_nat k)) mod 256)) (seq 0 n).
Definition wput (bs : list byte) (off : Z) (n : nat) (v : Z) : list byte :=
  firstn (Z.to_nat off) bs ++ wle_bytes n v ++ skipn (Z.to_nat off + n) bs.

(* a in [lo, lo + n) *)
Definition inrz (a lo n : Z) : bool := (lo <=? a) && (a <? lo + n).
Lemma inrz_true : forall a lo n, lo <= a < lo + n -> inrz a lo n = true.
Proof. intros a lo n H. unfold inrz. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma inrz_false : forall a lo n, a < lo \/ lo + n <= a -> inrz a lo n = false.
Proof.
  intros a lo n H. unfold inrz. destruct H as [H|H].
  - replace (lo <=? a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (a <? lo + n) with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r.
Qed.

(* ==========================================================================
   1. fuzz_close: g_nl after one exchange, at the close in nl_talk (0x88e54)
   ========================================================================== *)

(* one chunk of 36 bytes queued and consumed, one 32-byte request sent, the socket open once, 64 interfaces *)
Definition fc_bs : list byte :=
  let z := repeat (zb 0) (Z.to_nat NK_SIZE) in
  let z := wput z NK_CHUNK_LEN 8 36 in
  let z := wput z NK_N_CHUNKS 4 1 in
  let z := wput z NK_NEXT 4 1 in
  let z := wput z NK_OPEN 4 1 in
  let z := wput z NK_OPENED 4 1 in
  let z := wput z NK_SENT_LEN 8 32 in
  let z := wput z NK_N_SENT 4 1 in
  wput z NK_N_IF 4 64.

(* The fields, checked by ONE computation. Every other proof below is over an abstract list `bs` with these fields as
   hypotheses: a tactic that sees the 271992-byte list itself (rewrite, lia, f_equal) may try to reduce it by
   conversion, which costs minutes. *)
Definition fc_check (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? NK_SIZE) &&
  (nk_n_chunks bs =? 1) && (nk_next bs =? 1) && (nk_n_sent bs =? 1) && (nk_n_if bs =? 64) &&
  (nk_open bs =? 1) && (nk_opened bs =? 1) && (nk_closed bs =? 0) && (nk_misuse bs =? 0) &&
  (nk_end_errno bs =? 0) && (nk_socket_errno bs =? 0) && (nk_send_errno bs =? 0) &&
  (fld_u64 bs (NK_CHUNK_LEN + 8 * 0) =? 36) && (fld_u64 bs (NK_SENT_LEN + 8 * 0) =? 32).
Lemma fc_check_ok : fc_check fc_bs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fc_fields : forall bs, fc_check bs = true ->
  Z.of_nat (length bs) = NK_SIZE /\
  nk_n_chunks bs = 1 /\ nk_next bs = 1 /\ nk_n_sent bs = 1 /\ nk_n_if bs = 64 /\
  nk_open bs = 1 /\ nk_opened bs = 1 /\ nk_closed bs = 0 /\ nk_misuse bs = 0 /\
  nk_end_errno bs = 0 /\ nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  fld_u64 bs (NK_CHUNK_LEN + 8 * 0) = 36 /\ fld_u64 bs (NK_SENT_LEN + 8 * 0) = 32.
Proof.
  intros bs H. unfold fc_check in H. repeat rewrite andb_true_iff in H.
  repeat match type of H with
  | _ /\ _ => let H1 := fresh "H" in destruct H as [H H1]; apply Z.eqb_eq in H1
  end.
  apply Z.eqb_eq in H. repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma fc_wf_of : forall bs, fc_check bs = true -> nlk_wf bs.
Proof.
  intros bs Hb. destruct (fc_fields bs Hb) as (_ & Hc & Hn & Hs & Hi & Ho & Hod & Hcl & Hm & He1 & He2 & He3 & Hl0 & Hs0).
  unfold nlk_wf, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  - intros j Hj. assert (j = 0) by lia. subst j. lia.
  - intros j Hj. assert (j = 0) by lia. subst j. lia.
Qed.

(* g_nl's bytes bs at LA_G_NL, nothing else *)
Definition g_mem (bs : list byte) : word -> option byte := fun w =>
  if inrz (bv_unsigned w) LA_G_NL NK_SIZE then nth_error bs (Z.to_nat (bv_unsigned w - LA_G_NL)) else None.

Lemma g_mem_at : forall bs i, Z.of_nat (length bs) = NK_SIZE -> (i < length bs)%nat ->
  g_mem bs (Z_to_bv 64 (LA_G_NL + Z.of_nat i)) = nth_error bs i.
Proof.
  intros bs i Hlen Hi.
  unfold g_mem. rewrite unsigned_lit_small by (unfold LA_G_NL, NK_SIZE in *; lia).
  rewrite inrz_true by (unfold LA_G_NL, NK_SIZE in *; lia).
  cbv beta iota. f_equal. replace (LA_G_NL + Z.of_nat i - LA_G_NL) with (Z.of_nat i) by lia. apply Nat2Z.id.
Qed.

Lemma g_mem_anlk : forall segs bs, Z.of_nat (length bs) = NK_SIZE -> anlk_at segs (g_mem bs) LA_G_NL bs.
Proof.
  intros segs bs Hlen. split; [|exact Hlen]. split.
  - split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL, NK_SIZE in *; lia|].
    intros i Hi. unfold mbyte. rewrite g_mem_at by assumption.
    destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  - intros i Hi. unfold writable_at, wview.
    replace (LA_G_NL + i) with (LA_G_NL + Z.of_nat (Z.to_nat i)) by lia.
    rewrite g_mem_at by lia.
    destruct (nth_error bs (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|]. apply nth_error_None in E. lia.
Qed.

Lemma fuzz_close_apre_of : forall segs regs bs, fc_check bs = true -> fuzz_close_apre segs regs (g_mem bs).
Proof.
  intros segs regs bs Hb. destruct (fc_fields bs Hb) as (Hlen & _ & _ & _ & _ & _ & _ & Hcl & _).
  exists bs. split; [exact (g_mem_anlk segs bs Hlen)|]. split; [exact (fc_wf_of bs Hb)|]. lia.
Qed.

Definition fc_mem : word -> option byte := g_mem fc_bs.
Lemma fc_wf : nlk_wf fc_bs.
Proof. exact (fc_wf_of fc_bs fc_check_ok). Qed.

(* the Pre lambda of fuzz_close_acontract holds at fc_mem, for every segment list and register file *)
Lemma fuzz_close_apre_sat : forall segs regs, fuzz_close_apre segs regs fc_mem.
Proof. intros segs regs. exact (fuzz_close_apre_of segs regs fc_bs fc_check_ok). Qed.

(* ==========================================================================
   2. copy_attr: an IFLA_IFALIAS attribute "ab" into a 16-byte alias buffer (nl_talk 0x88d00)
   ========================================================================== *)

(* the attribute, in nl_talk's class-9 side frame (fake stack, below alloc_ceiling, high memory) *)
Definition CA_A : Z := 0x7f0000001040.
(* the alias buffer: op_read's text_buf(16) block, malloc(17) *)
Definition CA_B : Z := 0x602000000010.
(* nl_talk's realigned sp on the real stack *)
Definition CA_SP : Z := 0x7ffffffde000.
(* rta_len = 8, rta_type = IFLA_IFALIAS (20), payload "ab\0\0" *)
Definition ca_attr : list byte := map zb [8; 0; 20; 0; 0x61; 0x62; 0; 0].
Definition ca_pay : list byte := map zb [0x61; 0x62; 0; 0].

(* the shadow bytes around the two objects are 0 (frame_alloc_9 zeroes the frame's shadow; malloc(17) gives 0, 0, 1;
   only the first two granules of the block are read) *)
Definition ca_mem : word -> option byte := fun w =>
  if inrz (bv_unsigned w) (shadow_addr CA_A - 64) 128 || inrz (bv_unsigned w) (shadow_addr CA_B - 64) 128
  then Some (zb 0)
  else if inrz (bv_unsigned w) CA_A 8 then nth_error ca_attr (Z.to_nat (bv_unsigned w - CA_A))
  else if inrz (bv_unsigned w) CA_B 17 then Some (zb 0x5a)
  else None.

Lemma ca_shadow : forall s, (shadow_addr CA_A - 64 <= s < shadow_addr CA_A + 64) \/
  (shadow_addr CA_B - 64 <= s < shadow_addr CA_B + 64) -> ca_mem (Z_to_bv 64 s) = Some (zb 0).
Proof.
  intros s Hs. unfold shadow_addr, SHADOW_OFF, CA_A, CA_B in Hs.
  unfold ca_mem. rewrite unsigned_lit_small by lia.
  destruct Hs as [Hs|Hs]; [rewrite (inrz_true s) by (unfold shadow_addr, SHADOW_OFF, CA_A; lia); reflexivity|].
  rewrite (inrz_true s (shadow_addr CA_B - 64)) by (unfold shadow_addr, SHADOW_OFF, CA_B; lia).
  rewrite orb_true_r. reflexivity.
Qed.

Lemma ca_block : forall a, CA_B <= a < CA_B + 17 -> ca_mem (Z_to_bv 64 a) = Some (zb 0x5a).
Proof.
  intros a Ha. unfold ca_mem. rewrite unsigned_lit_small by (unfold CA_B in Ha; lia).
  rewrite (inrz_false a (shadow_addr CA_A - 64)) by (unfold shadow_addr, SHADOW_OFF, CA_A, CA_B in *; lia).
  rewrite (inrz_false a (shadow_addr CA_B - 64)) by (unfold shadow_addr, SHADOW_OFF, CA_B in *; lia).
  rewrite (inrz_false a CA_A) by (unfold CA_A, CA_B in *; lia).
  rewrite inrz_true by lia. reflexivity.
Qed.

Lemma ca_ard_shadow : forall segs s, (shadow_addr CA_A - 64 <= s < shadow_addr CA_A + 64) \/
  (shadow_addr CA_B - 64 <= s < shadow_addr CA_B + 64) -> ard segs ca_mem s = Some 0.
Proof. intros segs s Hs. unfold ard, mbyte. rewrite (ca_shadow s Hs). reflexivity. Qed.

(* the Pre lambda of copy_attr_acontract holds at ca_mem, for every segment list, at every register file with
   a0 = CA_A, a1 = CA_B, a2 = 16 and sp = CA_SP *)
Lemma copy_attr_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = CA_A -> aarg regs 1 = CA_B -> aarg regs 2 = 16 -> spZ regs = CA_SP ->
  copy_attr_apre segs regs ca_mem.
Proof.
  intros segs regs H0 H1 H2 Hsp. unfold copy_attr_apre, apart_frame. rewrite H0, H1, H2, Hsp.
  assert (HK : COPY_ATTR_AK = 8240) by reflexivity. rewrite HK.
  exists 8, ca_pay.
  split.
  { intros k Hk. destruct k as [|[|k]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
  split; [unfold RTA_HDR; lia|].
  split.
  { split; [unfold CA_A, RTA_HDR; lia|]. split; [change (length ca_pay) with 4%nat; unfold CA_A, RTA_HDR; lia|].
    intros i Hi. change (length ca_pay) with 4%nat in Hi.
    destruct i as [|[|[|[|i]]]]; [vm_compute; reflexivity .. | lia]. }
  split; [reflexivity|].
  split; [unfold CA_A; lia|].
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd, CA_A; right; lia|].
  split; [left; unfold CA_A, CA_SP; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply ca_ard_shadow. left. unfold shadow_of_addr, shadow_addr, SHADOW_OFF, CA_A in *. lia. }
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply ca_ard_shadow. left. unfold RTA_HDR, shadow_of_addr, shadow_addr, SHADOW_OFF, CA_A in *. lia. }
  split.
  { intros _ s Hs. rewrite ca_ard_shadow; [discriminate|].
    left. unfold RTA_HDR, shadow_addr, SHADOW_OFF, CA_A in *. lia. }
  split.
  { intros b Hb. unfold CA_A in Hb. lia. }
  intros _ _.
  split; [left; unfold CA_B, CA_SP; lia|].
  split; [unfold apart, RTA_HDR, CA_A, CA_B; lia|].
  split.
  { exists (repeat (zb 0x5a) 16). split; [reflexivity|]. split.
    - split; [unfold CA_B; lia|]. split; [rewrite repeat_length; unfold CA_B; lia|].
      intros i Hi. rewrite repeat_length in Hi. unfold mbyte.
      rewrite ca_block by lia. rewrite nth_error_repeat by exact Hi. reflexivity.
    - intros i Hi. rewrite repeat_length in Hi. unfold writable_at, wview.
      rewrite ca_block by lia. cbv beta iota. discriminate. }
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd, CA_B; right; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply ca_ard_shadow. right. unfold shadow_of_addr, shadow_addr, SHADOW_OFF, CA_B in *. lia. }
  intros s Hs. rewrite ca_ard_shadow; [discriminate|].
  right. unfold shadow_addr, SHADOW_OFF, CA_B in *. lia.
Qed.
