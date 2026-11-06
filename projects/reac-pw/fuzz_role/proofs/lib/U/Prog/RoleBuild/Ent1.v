(** ent_build's kind 1 in the UBSan image (pod.h:285-296): a key from vocab[i % 9] (the pointer table at 0x1e100
    in .data.rel.ro), ent_text with its NUL, and for kind & 0x80 an 'x' and a second NUL. From the jump table's target
    0x13548 to the join 0x13c48: the index (0x13548-0x13598, or 0x13770 when no byte is left), then 0x1377c: the
    pointer, strlen, memcpy into e->body, the NUL, type and size, and 0x137d4-0x13818 or 0x13610. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout RoleImg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts EntRo.
Import ListNotations.
Open Scope Z_scope.

(** ** The table and its strings *)
Definition VPTR : list Z := pa_vocab_s role_ubsan_addrs.

Lemma vocab_relro : relro8_ok 0x1e100 VPTR = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vptr_length : length VPTR = 9%nat.
Proof. reflexivity. Qed.

Lemma vocab_rostr : forall i, (i < 9)%nat -> rostr_ok (nth i VPTR 0) (nth i vocab []) = true.
Proof. intros i Hi. do 9 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

Lemma vocab_len : forall i, (i < 9)%nat -> (0 < length (nth i vocab []) <= 18)%nat.
Proof. intros i Hi. do 9 (destruct i as [|i]; [vm_compute; lia|]). lia. Qed.

(** The pod of kind 1 for the kind byte kind and the vocab index i. *)
Definition case1_ent (kind : Z) (i : nat) : ent :=
  let e := ent_text (nth i vocab []) true in
  if Z.testbit kind 7 && (e_size e + 2 <=? 96) then Ent POD_STRING (e_size e + 2) (e_body e ++ [Z_to_bv 8 120; NUL])
  else e.

Lemma ent_text_short : forall s, (length s <= 95)%nat ->
  ent_text s true = Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [NUL]).
Proof.
  intros s H. unfold ent_text. rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. f_equal. lia.
Qed.

(** bs written right after the prefix A of A ++ zeros k (the body's next bytes). *)
Lemma bd_cat : forall (A bs : list byte) k j, j = length A -> (length bs <= k)%nat ->
  upd_bytes (A ++ zeros k) j bs = (A ++ bs) ++ zeros (k - length bs).
Proof. intros A bs k j -> H. rewrite upd_app_zeros by exact H. apply app_assoc. Qed.

Section Case1.
Variables (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Local Abbreviation QE := (QJ sp gp tp s11 F fc m r src pp lo (ent_build r)).

(** From 0x1377c with a0 = &vocab[i]. *)
Lemma case1_tail : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 : word) m1 (b : byte)
    (i : nat) r',
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) -> (i < 9)%nat ->
  a0 = Z_to_bv 64 (0x1e100 + 8 * Z.of_nat i) ->
  (bv_signed s4 <? 0) = Z.testbit (bv_unsigned b) 7 ->
  ent_build r = (case1_ent (bv_unsigned b) i, r') ->
  s1 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32))
             (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1377c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 m1 b i r' MC Hi -> Hs Eb E1 E5.
  pose proof (ep_range sp m r src pp lo HE) as R.
  set (p := nth i VPTR 0) in *. set (s := nth i vocab []) in *.
  pose proof (vocab_len i Hi) as Hl. fold s in Hl.
  pose proof (vocab_rostr i Hi) as Hok. fold p s in Hok.
  pose proof (relro8_read m1 0x1e100 VPTR i vocab_relro ltac:(rewrite vptr_length; lia) ltac:(lia)
    ltac:(rewrite vptr_length; lia)
    ltac:(intros a Ha; rewrite vptr_length in Ha; apply (MemC_relro sp m r src pp lo HE _ _ _ _ a MC);
          unfold RELRO_TBL, RELRO_TBL_END; lia)) as HP.
  fold p in HP.
  (* 0x1377c ld s8,0(a0); mv a0,s8; jal strlen *)
  step. do 2 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (rostr_bytes m1 p s MI1 Hok) as (SB & NN & SL & P0 & P1 & _).
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := img_slack p s).
    - rewrite unsigned_lit by lia. exact SB.
    - exact NN.
    - rewrite unsigned_lit by lia. exact SL.
    - exact MI1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mx &
              E & MU2 & WM2 & MI2 & SB2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  pose proof (MemC_call_nil _ _ _ _ _ _ _ _ MC MU2 WM2 MI2) as MC2. clear MC MU2 WM2 MI2 MI1 SB. rename MC2 into MC.
  rewrite unsigned_lit in SB2 by lia.
  (* 0x13788 addi a1,zero,95; mv s7,a0; mv s6,a0; bltu a0,a1 *)
  do 3 step. step. brt.
  (* 0x1379c addi s9,sp,0xc0; mv a0,s9; mv a1,s8; mv a2,s6; jal memcpy *)
  do 5 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 192) (length s) MC ltac:(lia)
    ltac:(unfold FRAME_LOCALS; lia)) as (junk & LJ & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := s) (junk := junk).
    - rewrite unsigned_lit by lia. exact (bytes_at_prefix _ _ _ _ SB2).
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact CJ.
    - rewrite !unsigned_lit by lia.
      destruct (ro_apart sp m r src pp lo HE p s (bv_unsigned sp + 192) (Z.of_nat (length s)) Hok ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)); lia.
    - exact MI1. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & my &
              E & MU3 & WM3 & MI3 & CE3 & _).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU3, CE3 by lia. rewrite Nat2Z.id in CE3.
  apply rw_CB_bytes in CE3 as [B3 _].
  pose proof (MemC_call_bd sp m r src pp lo HE _ my _ _ _ _ 0 s MC MU3 WM3 MI3 B3 ltac:(lia) ltac:(lia)) as MC2.
  clear MC MU3 WM3 MI3 B3 MI1 CJ LJ junk SB2. rename MC2 into MC.
  rewrite upd_zeros0 in MC by lia.
  (* 0x137b0 ld a0,0x80(sp); bltu a0,s6 (trap) *)
  pose proof (MemC_c80 sp m r src pp lo HE _ _ _ _ MC) as H80.
  step. step. brf. clear H80.
  (* 0x137b8 addi a0,s6,1; add a1,s9,s6; sb zero,0(a1) *)
  do 2 step.
  est_bd HE MC (bv_unsigned sp + 192 + Z.of_nat (length s)) (length s) 1%nat.
  lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b0) => replace b0 with [NUL] in MC by reflexivity end.
  rewrite (bd_cat s [NUL] (96 - length s) (length s) eq_refl) in MC by (cbn [length]; lia).
  (* 0x137c4 addi a1,zero,8; sw a1,0xb8(sp); sw a0,0xbc(sp); ld s8,0x68(sp) *)
  step. est_t HE MC. est_sz HE MC.
  pose proof (MemC_c68 sp m r src pp lo HE _ _ _ _ MC) as H68. step. clear H68.
  (* 0x137d4 bgez s4 *)
  step.
  destruct (Z.testbit (bv_unsigned b) 7) eqn:B7.
  - (* kind & 0x80: 'x' and a second NUL after the NUL *)
    replace (bv_lts s4 (Z_to_bv 64 0)) with true by (symmetry; unfold_cond; fold_lit_ux; rewrite Hs; reflexivity).
    cbn [negb].
    assert (Ee : case1_ent (bv_unsigned b) i =
                 Ent POD_STRING (Z.of_nat (length s) + 1 + 2) ((s ++ [NUL]) ++ [Z_to_bv 8 120; NUL])).
    { unfold case1_ent. fold s. rewrite ent_text_short by lia. cbn [e_size e_body]. rewrite B7.
      replace (Z.of_nat (length s) + 1 + 2 <=? 96) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    rewrite Ee in Eb.
    (* 0x137d8 addi a1,zero,93; bltu a1,s7 *)
    step. step. brf.
    (* 0x137e0 ld s7,0x78(sp); ld a1,0x80(sp); bgeu s6,a1 (trap) *)
    pose proof (MemC_c78 sp m r src pp lo HE _ _ _ _ MC) as H78.
    pose proof (MemC_c80 sp m r src pp lo HE _ _ _ _ MC) as H80.
    step. step. step. brf. clear H78 H80.
    (* 0x137ec addi a1,sp,0xc0; add a1,a1,a0; addi a0,s6,2; addi a2,zero,120; sb a2,0(a1) *)
    do 4 step.
    est_bd HE MC (bv_unsigned sp + 192 + (Z.of_nat (length s) + 1)) (length s + 1)%nat 1%nat.
    lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b1) => replace b1 with [Z_to_bv 8 120] in MC by reflexivity end.
    rewrite (bd_cat (s ++ [NUL]) [Z_to_bv 8 120] _ (length s + 1) ltac:(rewrite length_app; cbn [length]; lia)) in MC
      by (cbn [length]; lia).
    (* 0x13800 ld a1,0x80(sp); bltu a1,a0 (trap) *)
    pose proof (MemC_c80 sp m r src pp lo HE _ _ _ _ MC) as H80.
    step. step. brf. clear H80.
    (* 0x13808 addi a1,sp,0xc0; add a0,a1,a0; addi s6,s6,3; sb zero,0(a0) *)
    do 3 step.
    est_bd HE MC (bv_unsigned sp + 192 + (Z.of_nat (length s) + 2)) (length s + 2)%nat 1%nat.
    lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b1) => replace b1 with [NUL] in MC by reflexivity end.
    rewrite (bd_cat ((s ++ [NUL]) ++ [Z_to_bv 8 120]) [NUL] _ (length s + 2)
      ltac:(rewrite !length_app; cbn [length]; lia)) in MC by (cbn [length]; lia).
    (* 0x13818 sw s6,0xbc(sp); mv s9,s5; j *)
    est_sz HE MC. do 2 step.
    eapply join_13c48; [exact Eb | exact E1 | exact E5 | reflexivity | exact MC | | | ].
    + apply le4_le32.
    + rewrite le4_le32. cbn [e_size]. f_equal. lia.
    + cbn [e_body]. rewrite <- !app_assoc. cbn [app]. rewrite !length_app. cbn [length].
      match goal with |- _ ++ _ :: _ :: _ :: zeros ?a = _ ++ _ :: _ :: _ :: zeros ?b2 =>
        replace b2 with a by lia; reflexivity end.
  - replace (bv_lts s4 (Z_to_bv 64 0)) with false by (symmetry; unfold_cond; fold_lit_ux; rewrite Hs; reflexivity).
    cbn [negb].
    assert (Ee : case1_ent (bv_unsigned b) i = Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [NUL])).
    { unfold case1_ent. fold s. rewrite B7. cbn [andb]. apply ent_text_short. lia. }
    rewrite Ee in Eb.
    (* 0x13610 mv s9,s5; ld s7,0x78(sp); j *)
    pose proof (MemC_c78 sp m r src pp lo HE _ _ _ _ MC) as H78.
    do 3 step.
    eapply join_13c48; [exact Eb | exact E1 | exact E5 | reflexivity | exact MC | | | ].
    + apply le4_le32.
    + apply le4_le32.
    + cbn [e_body]. rewrite length_app. cbn [length].
      match goal with |- _ ++ zeros ?a = _ ++ zeros ?b2 => replace b2 with a by lia; reflexivity end.
Qed.

Lemma case1_ok_sec : case_at sp gp tp s11 F fc m r src pp lo 1 0x13548.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct rest as [|c rest].
  - (* no byte for i: i = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13548 beqz s6; 0x13770 mv s1,zero; auipc; addi a0 = vocab *)
    step. brt. do 3 step.
    apply case1_tail with (i := 0%nat) (b := b) (r' := []); [exact MC | lia | reflexivity | exact Hs | | reflexivity | ].
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13548 beqz s6; addi s5,s5,1; addi a0,zero,1; bgeu a0,s5 (trap) *)
    step. brf. do 2 step. step. brf.
    (* 0x13558 lbu a1,1(s9) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x1355c auipc; addi a0 = vocab; i % 9 (0x13564-0x1357c) *)
    do 9 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned c mod 9) by (symmetry; byte_eq c) end.
    pose proof (Z.mod_pos_bound (bv_unsigned c) 9 ltac:(lia)) as Hc9.
    assert (Hc : bv_unsigned c mod 9 = 0 \/ bv_unsigned c mod 9 = 1 \/ bv_unsigned c mod 9 = 2 \/
                 bv_unsigned c mod 9 = 3 \/ bv_unsigned c mod 9 = 4 \/ bv_unsigned c mod 9 = 5 \/
                 bv_unsigned c mod 9 = 6 \/ bv_unsigned c mod 9 = 7 \/ bv_unsigned c mod 9 = 8) by lia.
    destruct Hc as [K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]; rewrite K;
      (* 0x13580 slli a1,a1,3; not a2,a0; bltu a2,a1 (trap); addi s1,s1,-2; addi s5,s9,2; add a0,a0,a1; j *)
      (do 2 step; step; brf; do 4 step;
       lazymatch type of K with _ = ?k =>
         let kn := eval vm_compute in (Z.to_nat k) in
         apply case1_tail with (i := kn) (b := b) (r' := rest);
         [ exact MC | lia | reflexivity | exact Hs
         | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity
         | f_equal; rewrite L; lia | f_equal; rewrite L; lia ]
       end).
Qed.


End Case1.

Theorem case1_ok : forall (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case_at sp gp tp s11 F fc m r src pp lo 1 0x13548.
Proof. intros. apply case1_ok_sec; assumption. Qed.

