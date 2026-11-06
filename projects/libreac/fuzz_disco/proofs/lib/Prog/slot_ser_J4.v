From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser_ws slot_ser_J0 slot_ser_J1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser slot_ser_J2 slot_ser_J3.
Import ListNotations.
Open Scope Z_scope.

Lemma obj_bytes_empty : forall b vpad, obj_bytes b vpad jobj_empty = repeat (Z_to_bv 8 0) 144.
Proof. intros b vpad. reflexivity. Qed.

Lemma not_neg : forall i, 0 <= i < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 i)) 18446744073709551615) = Z_to_bv 64 (- (i + 1)).
Proof.
  intros i Hi. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. apply zbv_eq.
  replace (18446744073709551615 - i) with (- (i + 1) + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full.
Qed.

Lemma obj_head : json_scalar_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b c i i2 now : Z) (B : list Z) (o' : jobj) (jk vpk jv vpad j216 j192 : list byte),
  sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s1 = Z_to_bv 64 c -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s5 = Z_to_bv 64 (X + 1024 + 144 * c) -> s7 = Z_to_bv 64 (- jlen B) ->
  s8 = Z_to_bv 64 (X + 2336) -> s9 = Z_to_bv 64 1 -> s10 = Z_to_bv 64 i -> s11 = Z_to_bv 64 now ->
  0 <= c <= 7 -> 0 <= i -> at_byte B i 123 = true ->
  (if at_byte B (json_ws B (i + 1)) 125 then Some (json_ws B (i + 1) + 1, jobj_empty)
   else json_pairs B (json_ws B (i + 1)) jobj_empty (length B)) = Some (i2, o') ->
  length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 992) [CB 20 jk] -> rw_cells rsegs m (X + 1012) [CB 4 vpk] ->
  rw_cells rsegs m (X + 216) [CB 8 j216] -> rw_cells rsegs m (X + 192) [CB 8 j192] ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 (b + 1))] ->
  rw_cells rsegs m (X + 1024 + 144 * c) [CB 144 (repeat (Z_to_bv 8 0) 144)] ->
  rw_cells rsegs m (X + 2320) [CB 20 jv] -> rw_cells rsegs m (X + 2340) [CB 4 vpad] ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x51d38 <= lo ->
  X + 2592 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (jk' jv' j216' j192' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 (Z_to_bv 64 (i2 - 1)) s7 s8 s9' s10' s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13c0c) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 192, X + 200); (X + 216, X + 224); (X + 992, X + 1012);
              (X + 1024 + 144 * c, X + 1024 + 144 * c + 144); (X + 2320, X + 2340)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 1024 + 144 * c) [CB 144 (obj_bytes b vpad o')] /\
       rw_cells rsegs m' (X + 992) [CB 20 jk'] /\ rw_cells rsegs m' (X + 2320) [CB 20 jv'] /\
       rw_cells rsegs m' (X + 216) [CB 8 j216'] /\ rw_cells rsegs m' (X + 192) [CB 8 j192'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b c i i2 now B o' jk vpk jv vpad j216 j192 Esp Es0 Es1 Es2 Es3 Es4 Es5 Es7 Es8 Es9 Es10 Es11
    Hc Hi A123 JP Lk Lv Ljv Hb Hbl FB BB CK CV C216 C192 C224 CO CJ CP C200 JTB MI ST HK HI HX.
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite length_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  destruct (at_byte_true B i 123 A123) as [L0 C0].
  set (i1 := json_ws B (i + 1)) in *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1. fold i1 in G1.
  assert (L1 : i1 < jlen B).
  { destruct (at_byte B i1 125) eqn:A; [exact (proj1 (at_byte_true B i1 125 A))|].
    destruct (length B) as [|f]; [discriminate JP|]. cbn [json_pairs] in JP.
    destruct (jscalar B i1) as [[[[j kk] ks] kl]|] eqn:JS1; [|discriminate JP].
    exact (proj1 (js_rng B i1 j kk ks kl JS1)). }
  assert (L01 : i + 1 < jlen B) by (apply (ws_lt B (i + 1)); [lia | exact L1]).
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD0.
  pose proof CK as CKw. apply ser_cb in CKw as (_ & _ & WK).
  pose proof (munch_refl [(lo, X); (X + 192, X + 200); (X + 216, X + 224); (X + 992, X + 1012);
              (X + 1024 + 144 * c, X + 1024 + 144 * c + 144); (X + 2320, X + 2340)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  subst sp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia. rewrite C0, Z.eqb_refl. cbn [negb]. cbv iota.
  step. step. rewrite ltu_lit by lia. replace (i + 1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  step. step. step.
  rewrite (not_neg i) by lia.
  eapply evt_cut.
  { eapply ws_L9 with (b := b) (i := i + 1) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a1x E]. subst ms'. fold i1.
  step. rewrite neg_lit, Z.opp_involutive.
  step. rewrite ltu_lit by lia. replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  pose proof (ws_rd m b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia.
  destruct (at_byte B i1 125) eqn:A125.
  - destruct (at_byte_true B i1 125 A125) as [_ C125]. rewrite C125, Z.eqb_refl. cbv iota.
    injection JP as Ei2 Eo. subst i2 o'. replace (i1 + 1 - 1) with i1 by lia.
    apply evt_done. do 18 eexists. exists m, jk, jv, j216, j192.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [rewrite obj_bytes_empty; exact CO|]. split; [exact CK|]. split; [exact CJ|]. split; [exact C216|exact C192].
  - assert (C125 : (jbyte B i1 =? 125) = false).
    { unfold at_byte in A125. replace (i1 <? jlen B) with true in A125 by (symmetry; apply Z.ltb_lt; lia). exact A125. }
    rewrite C125. cbv iota.
    assert (LBf : (0 < length B)%nat) by (unfold jlen in L1; lia).
    pose proof (Nat.succ_pred_pos (length B) LBf) as LBs. rewrite <- LBs in JP.
    set (f := Nat.pred (length B)) in *.
    pose proof JP as JP1. cbn [json_pairs] in JP1.
    destruct (jscalar B i1) as [[[[j kk] ks] kl]|] eqn:JS1; cbv iota in JP1; [|discriminate JP1].
    destruct (kk =? 1) eqn:K1; cbn [negb] in JP1; cbv iota in JP1; [|discriminate JP1].
    apply Z.eqb_eq in K1. subst kk. clear JP1.
    pose proof (js_rng B i1 j 1 ks kl JS1) as [_ G2].
    step. step. step. step. step.
    eapply (js_call JS) with (lo := lo) (X := X) (b := b) (i := i1) (V := X + 992) (B := B) (j := j) (k := 1)
      (s := ks) (l := kl); [js_side .. | ].
    intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 ST1 BV.
    rewrite (ret_pc_even 0x139cc) by (first [lia | reflexivity]).
    unfold JSON_SCALAR_K in MU1.
    transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    pose proof (tok_cells m1 (X + 992) _ _ _ BV WK) as CK1. clear BV.
    step. rewrite eqb_lit by lia. replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    step. step. step. if_vm.
    step. step. if_vm.
    step. step. step. step. step. step. step. step. step. step. step.
    rewrite (unsigned_lit c) in * by lia. rewrite (Z.mul_comm c 144) in *.
    eapply evt_cut.
    { eapply (key_loop JS JT (S f)) with (lo := lo) (X := X) (b := b) (cur := X + 1024 + 144 * c) (now := now)
        (i := i1) (j := j) (ks := ks) (kl := kl) (r := i2) (B := B) (o := jobj_empty) (o' := o') (f := f)
        (vpk := vpk) (vpad := vpad) (jv := jv) (m0 := m1);
        first [eassumption | reflexivity | (f_equal; lia) | lia | apply munch_refl | apply wmono_refl
              | apply jobj_empty_inb | (rewrite obj_bytes_empty; eassumption) | exact (cells_cb3 _ _ _ _ _ CK1)]. }
    intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
                jk2 & jv2 & E & MU2 & WM2 & MI2 & ST2 & CO2 & CK2 & CJ2).
    subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    apply evt_done. do 18 eexists.
    exists m2, jk2, jv2, (le8 (Z_to_bv 64 (X + 1024 + 144 * c + 96))), (le8 (Z_to_bv 64 (X + 1024 + 144 * c + 120))).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact CO2|]. split; [exact CK2|]. split; [exact CJ2|]. split; apply ser_c8; assumption.
Qed.
