From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser_J2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c json_scalar_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_ws uslot_ser uslot_ser_Pq uslot_ser_J1 uslot_ser_J2.
Import ListNotations.
Open Scope Z_scope.

Lemma ukey_tail : json_scalar_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b i3 r : Z) (B : list Z) (o1 o' : jobj) (f : nat) (jk : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i3 -> s9 = Z_to_bv 64 1 -> s10 = Z_to_bv 64 32 ->
  X mod 16 = 0 -> 0 <= i3 <= jlen B ->
  ((at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) o1 f = Some (r, o')) \/
   (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = o1)) ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 1024) [CB 20 jk] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' : word, r = i3 + 1 /\ o' = o1 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13b70) fc None m (seg_rom rsegs)) \/
       (exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
               (i4 j4 ks4 kl4 : Z) (f4 : nat),
          f = S f4 /\ 0 <= i4 /\ jscalar B i4 = Some (j4, 1, ks4, kl4) /\ json_pairs B i4 o1 (S f4) = Some (r, o') /\
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 j4) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x1394c) fc None m' (seg_rom rsegs) /\
          munch [(lo, X); (X + 1024, X + 1044)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
          rw_cells rsegs m' (X + 1024)
            [CB 20 (le8 (Z_to_bv 64 (b + ks4)) ++ le8 (Z_to_bv 64 kl4) ++ le4 (Z_to_bv 64 1))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b00) fc None m (seg_rom rsegs)).
Proof.
  intros JS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b i3 r B o1 o' f jk Esp Es1 Es2 Es3 Es4 Es6 Es9 Es10 HX16 Hi3 MD Hb Hbl FB BB CK JTB MI ST HK HI HX.
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite ulength_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  assert (HV8 : (X + 1024) mod 8 = 0) by (clear - HX16; Z.div_mod_to_equations; lia).
  assert (L3 : i3 < jlen B).
  { destruct MD as [(A & _)|(_ & A & _)]; apply at_byte_true in A; lia. }
  pose proof CK as CKw. apply user_cb in CKw as (_ & _ & WK).
  pose proof (uws_rd m b B i3 BB ltac:(lia)) as RD3. pose proof (ws_byte B i3 FB) as HC3.
  subst sp s1 s2 s3 s4 s6 s9 s10.
  pose proof (munch_refl [(lo, X); (X + 1024, X + 1044)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite ltu_lit by lia. replace (i3 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia.
  destruct MD as [(A44 & JP4)|(A44 & A125 & Er & Eo)].
  - apply at_byte_true in A44 as [_ C44]. rewrite C44, Z.eqb_refl. cbn [negb]. cbv iota.
    set (i4 := json_ws B (i3 + 1)) in *.
    pose proof (ws_ge B (i3 + 1) ltac:(lia)) as G4. fold i4 in G4.
    destruct f as [|f4]; [discriminate JP4|].
    pose proof JP4 as JP5. cbn [json_pairs] in JP5.
    destruct (jscalar B i4) as [[[[j4 kk] ks4] kl4]|] eqn:JS4; cbv iota in JP5; [|discriminate JP5].
    destruct (kk =? 1) eqn:K1; cbn [negb] in JP5; cbv iota in JP5; [|discriminate JP5].
    apply Z.eqb_eq in K1. subst kk. clear JP5.
    pose proof (js_rng B i4 j4 1 ks4 kl4 JS4) as [L4 G5].
    eapply evt_cut.
    { eapply uws14w with (b := b) (i := i3) (B := B); first [reflexivity | lia | assumption]. }
    intros ms' [a0x E]. subst ms'. fold i4.
    step. step. step. step.
    eapply (ujs_call JS) with (lo := lo) (X := X) (b := b) (i := i4) (V := X + 1024) (B := B) (j := j4) (k := 1)
      (s := ks4) (l := kl4); [ujs_side .. | ].
    intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 ST1 BV.
    rewrite (ret_pc_even 0x13b54) by (first [lia | reflexivity]).
    unfold JSON_SCALAR_K in MU1.
    transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    pose proof (utok_cells m1 (X + 1024) _ _ _ BV WK) as CK1. clear BV.
    step. rewrite eqb_lit by lia. replace (j4 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    step. step. if_vm.
    step.
    apply evt_done. right. do 16 eexists. exists i4, j4, ks4, kl4, f4.
    split; [reflexivity|]. split; [lia|]. split; [exact JS4|]. split; [exact JP4|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    exact (ucells_cb3 _ _ _ _ _ CK1).
  - apply at_byte_true in A125 as [_ C125].
    replace (jbyte B i3 =? 44) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    step. step. rewrite eqb_lit by lia. rewrite C125, Z.eqb_refl. cbn [negb]. cbv iota.
    step.
    apply evt_done. left. do 2 eexists. split; [exact Er|]. split; [exact Eo|]. reflexivity.
Qed.

Lemma ukey_loop : json_scalar_contract -> jtok_is_contract ->
  forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo X b cur i j ks kl r : Z) (B : list Z) (o o' : jobj) (f : nat) (vpk vpad jv : list byte),
  (f < n)%nat ->
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s5 = Z_to_bv 64 cur -> s7 = Z_to_bv 64 (cur + 24) -> s0 = Z_to_bv 64 (cur + 48) ->
  s8 = Z_to_bv 64 (X + 2368) -> s9 = Z_to_bv 64 1 -> s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 0 ->
  a0 = Z_to_bv 64 j ->
  X mod 16 = 0 -> cur mod 8 = 0 ->
  0 <= i -> jscalar B i = Some (j, 1, ks, kl) -> json_pairs B i o (S f) = Some (r, o') ->
  length o = 6%nat -> Forall (tok_inb B) o -> length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 1024) [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] ->
  rw_cells rsegs m (X + 1044) [CB 4 vpk] ->
  rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 (cur + 72))] -> rw_cells rsegs m (X + 232) [C8 (Z_to_bv 64 (cur + 96))] ->
  rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 (cur + 120))] ->
  rw_cells rsegs m cur [CB 144 (obj_bytes b vpad o)] ->
  rw_cells rsegs m (X + 2352) [CB 20 jv] -> rw_cells rsegs m (X + 2372) [CB 4 vpad] ->
  X + 1056 <= cur -> cur + 144 <= X + 2352 ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  munch [(lo, X); (X + 1024, X + 1044); (cur, cur + 144); (X + 2352, X + 2372)] m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (jk' jv' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 (Z_to_bv 64 (r - 1)) s7 s8 s9 s10 (Z_to_bv 64 1) t3' t4' t5' t6')
                F (Z_to_bv 64 0x13b70) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 1024, X + 1044); (cur, cur + 144); (X + 2352, X + 2372)] m0 m' /\ wmono rsegs m0 m' /\
       mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' cur [CB 144 (obj_bytes b vpad o')] /\ rw_cells rsegs m' (X + 1024) [CB 20 jk'] /\
       rw_cells rsegs m' (X + 2352) [CB 20 jv'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1394c) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT n. induction n as [|n IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
      lo X b cur i j ks kl r B o o' f vpk vpad jv
      Hn Esp Es1 Es2 Es3 Es4 Es5 Es7 Es0 Es8 Es9 Es10 Es11 Ea0 HX16 Hc8 Hi JSk JP Lo Io Lk Lv Ljv Hb Hbl FB BB CK CV
      C248 C232 C208 CO CJ CP Hc1 Hc2 JTB MI ST HK HI HX MU WM; [lia|].
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite ulength_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  eapply evt_cut.
  { eapply (ukey_head JS JT) with (lo := lo) (X := X) (b := b) (cur := cur) (i := i) (j := j) (ks := ks) (kl := kl)
      (r := r) (B := B) (o := o) (o' := o') (f := f) (vpk := vpk) (vpad := vpad) (jv := jv);
      first [eassumption | reflexivity | lia]. }
  intros ms' (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m1 &
              i3 & o1 & jv1 & E & MU1 & WM1 & MI1 & ST1 & CO1 & CJ1 & Hi3 & Lo1 & Io1 & MD).
  subst ms'. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  eapply evt_cut.
  { eapply (ukey_tail JS) with (lo := lo) (X := X) (b := b) (i3 := i3) (r := r) (B := B) (o1 := o1)
      (o' := o') (f := f); first [eassumption | reflexivity | lia]. }
  intros ms' [(a0x & a1x & Er & Eo & E) |
              (ra2 & t02 & t12 & t22 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
               i4 & j4 & ks4 & kl4 & f4 & Ef & Hi4 & JS4 & JP4 & E & MU2 & WM2 & MI2 & ST2 & CK2)].
  - subst ms' o'. apply evt_done. do 17 eexists.
    exists (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1)), jv1.
    replace (r - 1) with i3 by lia.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    split; [exact CO1|]. split; [exact CK|exact CJ1].
  - subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    pose proof CJ1 as CJw. apply user_cb in CJw as (Ljv1 & _ & _).
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m2 lo X b cur i4 j4 ks4 kl4 r B
              o1 o' f4 vpk vpad jv1);
      first [eassumption | reflexivity | lia].
Qed.
