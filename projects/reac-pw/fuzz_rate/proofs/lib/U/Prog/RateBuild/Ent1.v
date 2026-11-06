(** ent_build's kind 1 in the UBSan image (pod.h:285-296): a key from vocab[i % 9] (the pointer table at 0x1ecc8
    in .data.rel.ro), ent_text with its NUL, and for kind & 0x80 an 'x' and a second NUL. From the jump table's target
    0x13778 to the join 0x13ee4: the index (0x13778-0x137cc, or 0x13958 when no byte is left), |r'| kept in the spill
    cell sp + 0x48 (0x137c0 `sd t1`, 0x13958 `sd zero`) across strlen and memcpy, then 0x13964: the pointer, strlen,
    memcpy into e->body, the NUL, type and size, |r'| read back at 0x139b8, and 0x139c0-0x13a00 / 0x13a04 / 0x13a64
    or 0x13dcc. The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent1.v
    re-walked at rate's registers, cells and addresses. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout RateImg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts EntRo.
Import ListNotations.
Open Scope Z_scope.

(** ** The table and its strings *)
Definition VPTR : list Z := pa_vocab_s rate_ubsan_addrs.

Lemma vocab_relro : relro8_ok 0x1ecc8 VPTR = true.
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

(** ** The spill cell carried across the stores into e (SP: its 8 bytes at sp + 0x48) *)
(** SP moved to the goal's memory write_to_mem m1 (Z_to_bv 64 a) cs, for a store at a >= sp + 0xe8. *)
Ltac sp_tr HE SP :=
  lazymatch type of SP with bytes_at _ ?m1 _ ?bs =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 ?a) ?cs) _) =>
    let SP2 := fresh "SP" in
    pose proof (spill_st _ _ _ _ _ _ HE m1 bs a cs SP ltac:(apply length_le8) ltac:(unlit; lia)
                  ltac:(rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length]; lia))
      as SP2;
    clear SP; rename SP2 into SP
  end end.

(** EntFacts' est_t / est_sz / est_bd with SP carried to the new memory before it is named. *)
Ltac est_t_sp HE MC SP :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 232)) 4 = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 232)) (le4 ?v)) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_t _ _ _ _ _ _ HE m1 t sz bd v MC) as MC2; clear MC; rename MC2 into MC;
      sp_tr HE SP; name_mem
    end
  end.

Ltac est_sz_sp HE MC SP :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 236)) 4 = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 236)) (le4 ?v)) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_sz _ _ _ _ _ _ HE m1 t sz bd v MC) as MC2; clear MC; rename MC2 into MC;
      sp_tr HE SP; name_mem
    end
  end.

Ltac est_bd_sp HE MC SP a k n :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa a) n = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    unlit; step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 ?a') ?bs) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_bd _ _ _ _ _ _ HE m1 t sz bd a' k bs MC ltac:(unlit; lia)
                    ltac:(rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length]; lia)) as MC2;
      clear MC; rename MC2 into MC; sp_tr HE SP; name_mem
    end
  end.

(** The store into the spill cell (0x137c0 `sd t1,0x48(sp)`, 0x13958 `sd zero,0x48(sp)`): MemC kept, SP made. *)
Ltac st_spill HE MC SP :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    pose proof (MemC_spill_ok _ _ _ _ _ _ HE m1 t sz bd MC) as HS;
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 72)) ?bs) _) =>
      let MC2 := fresh "MC" in
      destruct (MemC_st_spill _ _ _ _ _ _ HE m1 t sz bd bs MC ltac:(apply length_le8)) as [MC2 SP];
      clear MC; rename MC2 into MC; name_mem
    end
  end.

Section Case1.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Local Abbreviation QE := (QJ sp gp tp s3 F fc m r src pp lo (ent_build r)).

(** From 0x13964 with a0 = &vocab[i] and |r'| in the spill cell. *)
Lemma case1_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1 (b : byte)
    (i : nat) r',
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) -> (i < 9)%nat ->
  bytes_at rsegs m1 (bv_unsigned sp + 72) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  a0 = Z_to_bv 64 (0x1ecc8 + 8 * Z.of_nat i) ->
  (bv_signed s11 <? 0) = Z.testbit (bv_unsigned b) 7 ->
  ent_build r = (case1_ent (bv_unsigned b) i, r') ->
  s7 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) (Z_to_bv 64 0x4000) s7 s8 s9 s10
             s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13964) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 b i r' MC Hi SP -> Hs Eb E7.
  pose proof (ep_range sp m r src pp lo HE) as R.
  set (p := nth i VPTR 0) in *. set (s := nth i vocab []) in *.
  pose proof (vocab_len i Hi) as Hl. fold s in Hl.
  pose proof (vocab_rostr i Hi) as Hok. fold p s in Hok.
  pose proof (relro8_read m1 0x1ecc8 VPTR i vocab_relro ltac:(rewrite vptr_length; lia) ltac:(lia)
    ltac:(rewrite vptr_length; lia)
    ltac:(intros a Ha; rewrite vptr_length in Ha; apply (MemC_relro sp m r src pp lo HE _ _ _ _ a MC);
          unfold RELRO_TBL, RELRO_TBL_END; lia)) as HP.
  fold p in HP.
  (* 0x13964 ld s10,0(a0); mv a0,s10; jal strlen *)
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
  assert (SP2 : bytes_at rsegs mx (bv_unsigned sp + 72) (le8 (Z_to_bv 64 (Z.of_nat (length r')))))
    by (eapply spill_call_nil; [exact SP | exact MU2]).
  pose proof (MemC_call_nil _ _ _ _ _ _ _ _ MC MU2 WM2 MI2) as MC2.
  clear MC MU2 WM2 MI2 MI1 SB SP HP. rename MC2 into MC. rename SP2 into SP.
  rewrite unsigned_lit in SB2 by lia.
  (* 0x13970 addi a1,zero,95; mv s9,a0; mv s8,a0; bltu a0,a1 (taken: no clamp) *)
  do 3 step. step. brt.
  (* 0x13984 addi s6,sp,0xf0; mv a0,s6; mv a1,s10; mv a2,s8; jal memcpy *)
  do 5 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 240) (length s) MC ltac:(lia)
    ltac:(unfold FRAME_LOCALS; lia)) as (junk & LJ & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := s) (junk := junk).
    - rewrite unsigned_lit by lia. exact (bytes_at_prefix _ _ _ _ SB2).
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact CJ.
    - rewrite !unsigned_lit by lia.
      destruct (ro_apart sp m r src pp lo HE p s (bv_unsigned sp + 240) (Z.of_nat (length s)) Hok ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)); lia.
    - exact MI1. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & my &
              E & MU3 & WM3 & MI3 & CE3 & _).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU3, CE3 by lia. rewrite Nat2Z.id in CE3.
  apply rw_CB_bytes in CE3 as [B3 _].
  assert (SP2 : bytes_at rsegs my (bv_unsigned sp + 72) (le8 (Z_to_bv 64 (Z.of_nat (length r')))))
    by (eapply spill_call; [exact SP | apply length_le8 | exact MU3 | lia]).
  pose proof (MemC_call_bd sp m r src pp lo HE _ my _ _ _ _ 0 s MC MU3 WM3 MI3 B3 ltac:(lia) ltac:(lia)) as MC2.
  clear MC MU3 WM3 MI3 B3 MI1 CJ LJ junk SB2 SP. rename MC2 into MC. rename SP2 into SP.
  rewrite upd_zeros0 in MC by lia.
  (* 0x13998 ld a0,0xa0(sp); bltu a0,s8 (trap) *)
  pose proof (MemC_ca0 sp m r src pp lo HE _ _ _ _ MC) as HA0.
  step. step. brf. clear HA0.
  (* 0x139a0 addi a0,s8,1; add a1,s6,s8; sb zero,0(a1) *)
  do 2 step.
  est_bd_sp HE MC SP (bv_unsigned sp + 240 + Z.of_nat (length s)) (length s) 1%nat.
  lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b0) => replace b0 with [NUL] in MC by reflexivity end.
  rewrite (bd_cat s [NUL] (96 - length s) (length s) eq_refl) in MC by (cbn [length]; lia).
  (* 0x139ac addi a1,zero,8; sw a1,0xe8(sp); sw a0,0xec(sp) *)
  step. est_t_sp HE MC SP. est_sz_sp HE MC SP.
  (* 0x139b8 ld t1,0x48(sp) *)
  pose proof (bytes_at_read8 _ _ _ SP (length_le8 _)) as H48.
  step. clear H48 SP.
  pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as HD8.
  pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as HC8.
  (* 0x139bc bgez s11 *)
  step.
  destruct (Z.testbit (bv_unsigned b) 7) eqn:B7.
  - (* kind & 0x80: 'x' and a second NUL after the NUL *)
    replace (bv_lts s11 (Z_to_bv 64 0)) with true by (symmetry; unfold_cond; fold_lit_ux; rewrite Hs; reflexivity).
    cbn [negb].
    assert (Ee : case1_ent (bv_unsigned b) i =
                 Ent POD_STRING (Z.of_nat (length s) + 1 + 2) ((s ++ [NUL]) ++ [Z_to_bv 8 120; NUL])).
    { unfold case1_ent. fold s. rewrite ent_text_short by lia. cbn [e_size e_body]. rewrite B7.
      replace (Z.of_nat (length s) + 1 + 2 <=? 96) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    rewrite Ee in Eb.
    (* 0x139c0 lui s6,4; addi a1,zero,93; bltu a1,s9 *)
    do 2 step. step. brf.
    (* 0x139cc ld a1,0xa0(sp); bgeu s8,a1 (trap) *)
    pose proof (MemC_ca0 sp m r src pp lo HE _ _ _ _ MC) as HA0.
    step. step. brf. clear HA0.
    (* 0x139d4 addi a1,sp,0xf0; add a1,a1,a0; addi a0,s8,2; addi a2,zero,120; sb a2,0(a1) *)
    do 4 step.
    est_bd HE MC (bv_unsigned sp + 240 + (Z.of_nat (length s) + 1)) (length s + 1)%nat 1%nat.
    lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b1) => replace b1 with [Z_to_bv 8 120] in MC by reflexivity end.
    rewrite (bd_cat (s ++ [NUL]) [Z_to_bv 8 120] _ (length s + 1) ltac:(rewrite length_app; cbn [length]; lia)) in MC
      by (cbn [length]; lia).
    (* 0x139e8 ld a1,0xa0(sp); bltu a1,a0 (trap) *)
    pose proof (MemC_ca0 sp m r src pp lo HE _ _ _ _ MC) as HA0.
    step. step. brf. clear HA0.
    (* 0x139f0 addi a1,sp,0xf0; add a0,a1,a0; addi s8,s8,3; sb zero,0(a0) *)
    do 3 step.
    est_bd HE MC (bv_unsigned sp + 240 + (Z.of_nat (length s) + 2)) (length s + 2)%nat 1%nat.
    lazymatch type of MC with MemC _ _ _ _ _ _ (upd_bytes _ _ ?b1) => replace b1 with [NUL] in MC by reflexivity end.
    rewrite (bd_cat ((s ++ [NUL]) ++ [Z_to_bv 8 120]) [NUL] _ (length s + 2)
      ltac:(rewrite !length_app; cbn [length]; lia)) in MC by (cbn [length]; lia).
    (* 0x13a00 sw s8,0xec(sp) *)
    est_sz HE MC.
    (* 0x13a04 mv s9,s7; j; 0x13a64 ld s8,0xd8(sp); ld s11,0xc8(sp); j 0x13ee4 *)
    pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as HD8'.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as HC8'.
    do 5 step.
    eapply join_13ee4; [exact Eb | reflexivity | exact E7 | exact MC | | | ].
    + apply le4_le32.
    + rewrite le4_le32. cbn [e_size]. f_equal. lia.
    + cbn [e_body]. rewrite <- !app_assoc. cbn [app]. rewrite !length_app. cbn [length].
      match goal with |- _ ++ _ :: _ :: _ :: zeros ?a = _ ++ _ :: _ :: _ :: zeros ?b2 =>
        replace b2 with a by lia; reflexivity end.
  - replace (bv_lts s11 (Z_to_bv 64 0)) with false by (symmetry; unfold_cond; fold_lit_ux; rewrite Hs; reflexivity).
    cbn [negb].
    assert (Ee : case1_ent (bv_unsigned b) i = Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [NUL])).
    { unfold case1_ent. fold s. rewrite B7. cbn [andb]. apply ent_text_short. lia. }
    rewrite Ee in Eb.
    (* 0x13dcc mv s9,s7; ld s8,0xd8(sp); ld s11,0xc8(sp); lui s6,4; j 0x13ee4 *)
    do 5 step.
    eapply join_13ee4; [exact Eb | reflexivity | exact E7 | exact MC | | | ].
    + apply le4_le32.
    + apply le4_le32.
    + cbn [e_body]. rewrite length_app. cbn [length].
      match goal with |- _ ++ zeros ?a = _ ++ zeros ?b2 => replace b2 with a by lia; reflexivity end.
Qed.

Lemma case1_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 1 0x13778.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct rest as [|c rest].
  - (* no byte for i: i = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13778 beqz s8 (taken); 0x13958 sd zero,0x48(sp); auipc; addi a0 = vocab *)
    step. brt.
    st_spill HE MC SP.
    do 2 step.
    apply case1_tail with (i := 0%nat) (b := b) (r' := []); [exact MC | lia | exact SP | reflexivity | exact Hs | | ].
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13778 beqz s8; addi s7,s7,1; addi a0,zero,1; bgeu a0,s7 (trap) *)
    step. brf. do 2 step. step. brf.
    (* 0x13788 lbu a1,1(s9) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x1378c auipc; addi a0 = vocab; i % 9 (0x13794-0x137ac) *)
    do 9 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned c mod 9) by (symmetry; byte_eq c) end.
    pose proof (Z.mod_pos_bound (bv_unsigned c) 9 ltac:(lia)) as Hc9.
    assert (Hc : bv_unsigned c mod 9 = 0 \/ bv_unsigned c mod 9 = 1 \/ bv_unsigned c mod 9 = 2 \/
                 bv_unsigned c mod 9 = 3 \/ bv_unsigned c mod 9 = 4 \/ bv_unsigned c mod 9 = 5 \/
                 bv_unsigned c mod 9 = 6 \/ bv_unsigned c mod 9 = 7 \/ bv_unsigned c mod 9 = 8) by lia.
    destruct Hc as [K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]; rewrite K;
      (* 0x137b0 slli a1,a1,3; not a2,a0; bltu a2,a1 (trap); addi t1,t1,-2; sd t1,0x48(sp); addi s7,s9,2;
         add a0,a0,a1; j 0x13964 *)
      (do 2 step; step; brf; step; st_spill HE MC SP; do 3 step;
       lazymatch type of K with _ = ?k =>
         let kn := eval vm_compute in (Z.to_nat k) in
         apply case1_tail with (i := kn) (b := b) (r' := rest);
         [ exact MC | lia
         | lazymatch type of SP with bytes_at _ _ _ (le8 ?w) =>
             replace (Z_to_bv 64 (Z.of_nat (length rest))) with w; [exact SP | f_equal; rewrite L; lia] end
         | reflexivity | exact Hs
         | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity
         | f_equal; rewrite L; lia ]
       end).
Qed.

End Case1.

Theorem case1_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case_at sp gp tp s3 F fc m r src pp lo 1 0x13778.
Proof. intros. apply case1_ok_sec; assumption. Qed.
