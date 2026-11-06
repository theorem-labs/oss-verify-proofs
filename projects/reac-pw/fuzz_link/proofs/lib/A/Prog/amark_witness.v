(* Satisfiability witnesses of the function-specific Pre of the mark contracts (reac_served_say_to and the two decide
   entries), at memories holding the values a real run holds at the call, and the shared facts the other
   witnesses of the slice need. The journal part of every Pre (link_amem.v `apre`) needs AR of image A's start
   state, which the start-up files give; it is written out in
   link-a/contracts/mark.md (internal record, sha256 17cf224365ab), as link-a/form/WITNESS.md
   (internal record, sha256 b8aaf8151f7f) does for the two exemplars. Each lemma holds for every segment list: the
   witness memory holds every byte the Pre reads, so no ROM byte is read.

   The witnesses of remember, reac_code_emit, reac_served_mark and mark_quietly are written out in
   link-a/contracts/mark.md (internal record, sha256 17cf224365ab) (the state of a run at their call sites: g_nl after
   interfaces() and one exchange, the calloc(1, 516) marks block, the fmemopen FILE over g_said, the name "nl0" of
   g_names). They are not closed lemmas here because each needs the whole 1304-byte FILE of `amemfile_k` or the 64-entry
   interface table of `aiftab_at` written out as byte lists, and the form of those two predicates is the frame's A twin
   to come (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 item 5): a witness built against this
   slice's own `amemfile_k` would have to be rebuilt with it.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem form_witness model_decide_c reac_served_say_to_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   0. Shared facts
   ========================================================================== *)

(* a byte literal under 256 is the NUL byte only when its number is 0 *)
Lemma zb_ne_0 : forall c, 0 < c < 256 -> zb c <> zb 0.
Proof.
  intros c Hc E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap, bv_modulus in E. cbn [Z.of_N] in E.
  rewrite !Z.mod_small in E by lia. lia.
Qed.

(* a list of non-NUL byte numbers gives a list of bytes with no NUL, which is what `acstr_at` asks beside the
   bytes themselves *)
Lemma no_nul_map : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (zb 0) (map (Z_to_bv 8) l).
Proof.
  induction l as [|c l IH]; intros HF; [intros []|].
  inversion HF as [|x xs Hc HF' Heq]; subst. cbn [map In]. intros [E|H].
  - exact (zb_ne_0 c Hc E).
  - exact (IH HF' H).
Qed.

Lemma no_nul_prefix : ~ In (zb 0) S_PREFIX.
Proof. apply no_nul_map. repeat constructor; lia. Qed.
Lemma no_nul_vlan : ~ In (zb 0) S_VLAN.
Proof. apply no_nul_map. repeat constructor; lia. Qed.

(* the bytes of a witness memory that answers every byte of the list itself *)
Lemma abytes_of_mem : forall segs (m : word -> option byte) (p : Z) (l : list byte),
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, (i < length l)%nat -> m (Z_to_bv 64 (p + Z.of_nat i)) = nth_error l i) ->
  abytes segs m p l.
Proof.
  intros segs m p l H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mbyte. rewrite (H i Hi).
  destruct (nth_error l i) eqn:E; [reflexivity|]. exfalso. apply nth_error_None in E. lia.
Qed.

(* ==========================================================================
   1. reac_served_say_to: g_say writable, which is the whole of its Pre
   ========================================================================== *)

(* the 8 bytes of g_say, nothing else (its call site is mark_quietly 0x8841c, where fmemopen has just answered) *)
Definition sy_mem : word -> option byte := fun w =>
  if inrz (bv_unsigned w) LA_G_SAY 8 then Some (zb 0) else None.

Lemma reac_served_say_to_apre_sat : forall segs regs, reac_served_say_to_apre segs regs sy_mem.
Proof.
  intros segs regs i Hi. unfold writable_at, wview, sy_mem.
  rewrite unsigned_lit_small by (unfold LA_G_SAY in *; lia).
  rewrite inrz_true by (unfold LA_G_SAY in *; lia). cbv beta iota. discriminate.
Qed.

(* ==========================================================================
   2. model_decide / reac_served_decide: a "vlan" kind and no alias
   ========================================================================== *)

(* A call shape of reac_served_decide with the kind "vlan" in a buffer of a class-3 side frame (the fake stack,
   the high band of `amem_range`) and a NULL alias pointer, so the answer is
   `decide (Some "vlan") None` = V_LEAVE_VLAN = 2. At reac_served_mark 0x89a48 the alias is never NULL (a1 is
   s7 = s9 + 0x60, its own alias buffer); the NULL case is `astr_arg`'s None arm, which the Pre admits and the
   code tests at +0x08. The lemma shows the Pre can be met; it does not claim this is the state at 0x89a48. *)
Definition DC_K : Z := 0x7f0000002040.
Definition DC_SP : Z := 0x7ffffffde000.
(* 16 bytes at each object: the string, its NUL, and the rest of the NUL's 8-byte word, which the runtime's
   string wrappers read word-wise *)
Definition dc_vlan16 : list byte := map zb [118; 108; 97; 110; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition dc_pre16 : list byte := map zb [114; 101; 97; 99; 45; 112; 119; 58; 0; 0; 0; 0; 0; 0; 0; 0].

Definition dc_mem : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if inrz a (shadow_addr LA_RSD_PREFIX - 64) 128 || inrz a (shadow_addr DC_K - 64) 128
  then Some (zb 0)
  else if inrz a LA_RSD_PREFIX 16 then nth_error dc_pre16 (Z.to_nat (a - LA_RSD_PREFIX))
  else if inrz a LA_RSD_VLAN 16 then nth_error dc_vlan16 (Z.to_nat (a - LA_RSD_VLAN))
  else if inrz a DC_K 16 then nth_error dc_vlan16 (Z.to_nat (a - DC_K))
  else None.

Ltac dc_consts := unfold shadow_addr, SHADOW_OFF, LA_RSD_PREFIX, LA_RSD_VLAN, DC_K in *.

Lemma dc_shadow : forall s,
  (shadow_addr LA_RSD_PREFIX - 64 <= s < shadow_addr LA_RSD_PREFIX + 64) \/
  (shadow_addr DC_K - 64 <= s < shadow_addr DC_K + 64) -> dc_mem (Z_to_bv 64 s) = Some (zb 0).
Proof.
  intros s Hs. unfold dc_mem. rewrite unsigned_lit_small by (dc_consts; lia). cbv zeta.
  destruct Hs as [Hs|Hs].
  - rewrite (inrz_true s) by (dc_consts; lia). reflexivity.
  - rewrite (inrz_true s (shadow_addr DC_K - 64)) by (dc_consts; lia). rewrite orb_true_r. reflexivity.
Qed.

Lemma dc_ard_shadow : forall segs s,
  (shadow_addr LA_RSD_PREFIX - 64 <= s < shadow_addr LA_RSD_PREFIX + 64) \/
  (shadow_addr DC_K - 64 <= s < shadow_addr DC_K + 64) -> ard segs dc_mem s = Some 0.
Proof. intros segs s Hs. unfold ard, mbyte. rewrite (dc_shadow s Hs). reflexivity. Qed.

Lemma dc_pre_at : forall i, (i < 16)%nat ->
  dc_mem (Z_to_bv 64 (LA_RSD_PREFIX + Z.of_nat i)) = nth_error dc_pre16 i.
Proof.
  intros i Hi. unfold dc_mem. rewrite unsigned_lit_small by (dc_consts; lia). cbv zeta.
  rewrite (inrz_false (LA_RSD_PREFIX + Z.of_nat i)) by (dc_consts; lia).
  rewrite (inrz_false (LA_RSD_PREFIX + Z.of_nat i) (shadow_addr DC_K - 64)) by (dc_consts; lia).
  cbn [orb]. rewrite inrz_true by (dc_consts; lia).
  replace (LA_RSD_PREFIX + Z.of_nat i - LA_RSD_PREFIX) with (Z.of_nat i) by lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma dc_vlan_at : forall i, (i < 16)%nat ->
  dc_mem (Z_to_bv 64 (LA_RSD_VLAN + Z.of_nat i)) = nth_error dc_vlan16 i.
Proof.
  intros i Hi. unfold dc_mem. rewrite unsigned_lit_small by (dc_consts; lia). cbv zeta.
  rewrite (inrz_false (LA_RSD_VLAN + Z.of_nat i)) by (dc_consts; lia).
  rewrite (inrz_false (LA_RSD_VLAN + Z.of_nat i) (shadow_addr DC_K - 64)) by (dc_consts; lia).
  cbn [orb]. rewrite (inrz_false (LA_RSD_VLAN + Z.of_nat i) LA_RSD_PREFIX) by (dc_consts; lia).
  rewrite inrz_true by (dc_consts; lia).
  replace (LA_RSD_VLAN + Z.of_nat i - LA_RSD_VLAN) with (Z.of_nat i) by lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma dc_kind_at : forall i, (i < 16)%nat ->
  dc_mem (Z_to_bv 64 (DC_K + Z.of_nat i)) = nth_error dc_vlan16 i.
Proof.
  intros i Hi. unfold dc_mem. rewrite unsigned_lit_small by (dc_consts; lia). cbv zeta.
  rewrite (inrz_false (DC_K + Z.of_nat i)) by (dc_consts; lia).
  rewrite (inrz_false (DC_K + Z.of_nat i) (shadow_addr DC_K - 64)) by (dc_consts; lia).
  cbn [orb]. rewrite (inrz_false (DC_K + Z.of_nat i) LA_RSD_PREFIX) by (dc_consts; lia).
  rewrite (inrz_false (DC_K + Z.of_nat i) LA_RSD_VLAN) by (dc_consts; lia).
  rewrite inrz_true by (dc_consts; lia).
  replace (DC_K + Z.of_nat i - DC_K) with (Z.of_nat i) by lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

(* the lengths, once, so that no proof below has to reduce a Definition inside `length` *)
Lemma len_pre16 : length dc_pre16 = 16%nat. Proof. reflexivity. Qed.
Lemma len_vlan16 : length dc_vlan16 = 16%nat. Proof. reflexivity. Qed.
Lemma len_prefix : length (S_PREFIX ++ [zb 0]) = 9%nat. Proof. reflexivity. Qed.
Lemma len_vlan : length (S_VLAN ++ [zb 0]) = 5%nat. Proof. reflexivity. Qed.
Lemma len_prefix_Z : Z.of_nat (length S_PREFIX) = 8. Proof. reflexivity. Qed.
Lemma len_vlan_Z : Z.of_nat (length S_VLAN) = 4. Proof. reflexivity. Qed.

(* every byte of a 16-byte object is visible, which is what the wrappers need of the NUL's word *)
Lemma dc_vis_pre : forall segs b, LA_RSD_PREFIX <= b < LA_RSD_PREFIX + 16 -> ard segs dc_mem b <> None.
Proof.
  intros segs b Hb. unfold ard, mbyte.
  replace b with (LA_RSD_PREFIX + Z.of_nat (Z.to_nat (b - LA_RSD_PREFIX))) by lia.
  rewrite dc_pre_at by lia.
  destruct (nth_error dc_pre16 (Z.to_nat (b - LA_RSD_PREFIX))) eqn:E; [cbn; discriminate|].
  exfalso. apply nth_error_None in E. rewrite len_pre16 in E. lia.
Qed.

Lemma dc_vis_vlan : forall segs b, LA_RSD_VLAN <= b < LA_RSD_VLAN + 16 -> ard segs dc_mem b <> None.
Proof.
  intros segs b Hb. unfold ard, mbyte.
  replace b with (LA_RSD_VLAN + Z.of_nat (Z.to_nat (b - LA_RSD_VLAN))) by lia.
  rewrite dc_vlan_at by lia.
  destruct (nth_error dc_vlan16 (Z.to_nat (b - LA_RSD_VLAN))) eqn:E; [cbn; discriminate|].
  exfalso. apply nth_error_None in E. rewrite len_vlan16 in E. lia.
Qed.

Lemma dc_vis_kind : forall segs b, DC_K <= b < DC_K + 16 -> ard segs dc_mem b <> None.
Proof.
  intros segs b Hb. unfold ard, mbyte.
  replace b with (DC_K + Z.of_nat (Z.to_nat (b - DC_K))) by lia.
  rewrite dc_kind_at by lia.
  destruct (nth_error dc_vlan16 (Z.to_nat (b - DC_K))) eqn:E; [cbn; discriminate|].
  exfalso. apply nth_error_None in E. rewrite len_vlan16 in E. lia.
Qed.


Lemma dc_cstr_prefix : forall segs, acstr_at segs dc_mem LA_RSD_PREFIX S_PREFIX.
Proof.
  intros segs. split; [|exact no_nul_prefix].
  apply abytes_of_mem; [dc_consts; lia | rewrite len_prefix; dc_consts; lia |].
  intros i Hi. rewrite len_prefix in Hi. rewrite dc_pre_at by lia.
  destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];
    [vm_compute; reflexivity .. | exfalso; lia].
Qed.

Lemma dc_cstr_vlan : forall segs, acstr_at segs dc_mem LA_RSD_VLAN S_VLAN.
Proof.
  intros segs. split; [|exact no_nul_vlan].
  apply abytes_of_mem; [dc_consts; lia | rewrite len_vlan; dc_consts; lia |].
  intros i Hi. rewrite len_vlan in Hi. rewrite dc_vlan_at by lia.
  destruct i as [|[|[|[|[|i]]]]]; [vm_compute; reflexivity .. | exfalso; lia].
Qed.

Lemma dc_cstr_kind : forall segs, acstr_at segs dc_mem DC_K S_VLAN.
Proof.
  intros segs. split; [|exact no_nul_vlan].
  apply abytes_of_mem; [dc_consts; lia | rewrite len_vlan; dc_consts; lia |].
  intros i Hi. rewrite len_vlan in Hi. rewrite dc_kind_at by lia.
  destruct i as [|[|[|[|[|i]]]]]; [vm_compute; reflexivity .. | exfalso; lia].
Qed.

(* what each of the three strings must satisfy for the strncmp / strcmp wrappers to read it *)
Lemma dc_rt_prefix : forall segs regs, spZ regs = DC_SP ->
  astr_rt_ok segs regs DECIDE_AK dc_mem LA_RSD_PREFIX S_PREFIX.
Proof.
  intros segs regs Hsp. unfold astr_rt_ok, apart_frame. rewrite Hsp.
  assert (HK : DECIDE_AK = 8208) by reflexivity. rewrite HK.
  rewrite len_prefix_Z.
  split; [dc_consts; lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd; dc_consts; left; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply dc_ard_shadow. left. unfold shadow_of_addr in *. dc_consts. lia. }
  split.
  { intros s Hs. rewrite dc_ard_shadow; [discriminate|]. left. dc_consts. lia. }
  split.
  { intros b Hb. apply dc_vis_pre. dc_consts. lia. }
  unfold DC_SP. dc_consts. left. lia.
Qed.

Lemma dc_rt_vlan : forall segs regs, spZ regs = DC_SP ->
  astr_rt_ok segs regs DECIDE_AK dc_mem LA_RSD_VLAN S_VLAN.
Proof.
  intros segs regs Hsp. unfold astr_rt_ok, apart_frame. rewrite Hsp.
  assert (HK : DECIDE_AK = 8208) by reflexivity. rewrite HK.
  rewrite len_vlan_Z.
  split; [dc_consts; lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd; dc_consts; left; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply dc_ard_shadow. left. unfold shadow_of_addr in *. dc_consts. lia. }
  split.
  { intros s Hs. rewrite dc_ard_shadow; [discriminate|]. left. dc_consts. lia. }
  split.
  { intros b Hb. apply dc_vis_vlan. dc_consts. lia. }
  unfold DC_SP. dc_consts. left. lia.
Qed.

Lemma dc_rt_kind : forall segs regs, spZ regs = DC_SP ->
  astr_rt_ok segs regs DECIDE_AK dc_mem DC_K S_VLAN.
Proof.
  intros segs regs Hsp. unfold astr_rt_ok, apart_frame. rewrite Hsp.
  assert (HK : DECIDE_AK = 8208) by reflexivity. rewrite HK.
  rewrite len_vlan_Z.
  split; [dc_consts; lia|]. split; [lia|].
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd; dc_consts; right; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    apply dc_ard_shadow. right. unfold shadow_of_addr in *. dc_consts. lia. }
  split.
  { intros s Hs. rewrite dc_ard_shadow; [discriminate|]. right. dc_consts. lia. }
  split.
  { intros b Hb. apply dc_vis_kind. dc_consts. lia. }
  unfold DC_SP. dc_consts. left. lia.
Qed.

(* the Pre lambda of reac_served_decide_acontract holds at dc_mem, at every register file with a0 = DC_K,
   a1 = 0 and sp = DC_SP. The same lemma at LA_MD_PREFIX / LA_MD_VLAN is model_decide's, with the same proof
   over a memory holding model_decide's own two literals. *)
Lemma reac_served_decide_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = DC_K -> aarg regs 1 = 0 -> spZ regs = DC_SP ->
  decide_apre segs LA_RSD_PREFIX LA_RSD_VLAN regs dc_mem.
Proof.
  intros segs regs H0 H1 Hsp. unfold decide_apre.
  exists (Some S_VLAN), None.
  split. { unfold astr_arg. rewrite H0. split; [dc_consts; lia | apply dc_cstr_kind]. }
  split. { unfold astr_arg. exact H1. }
  split; [apply dc_cstr_prefix|].
  split; [apply dc_rt_prefix; exact Hsp|].
  split; [apply dc_cstr_vlan|].
  split; [apply dc_rt_vlan; exact Hsp|].
  split.
  { intros t Ht. inversion Ht as [Ht']. rewrite H0. apply dc_rt_kind; exact Hsp. }
  intros t Ht. discriminate Ht.
Qed.

(* the answer at this witness: `decide (Some S_VLAN) None` is V_LEAVE_VLAN *)
Lemma dc_answer : decide (Some S_VLAN) None = V_LEAVE_VLAN.
Proof. vm_compute. reflexivity. Qed.
