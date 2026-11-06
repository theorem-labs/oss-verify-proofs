From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser_J2 slot_ser_J4.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c json_scalar_c memset_c memset.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_tokb uslot_ser_ws uslot_ser uslot_ser_Pq uslot_ser_J1 uslot_ser_J2.
Import ListNotations.
Open Scope Z_scope.

Lemma uobj_head : json_scalar_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b c i i2 : Z) (B : list Z) (o' : jobj) (jk vpk jv vpad jo j208 j232 j240 j248 : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i -> s8 = Z_to_bv 64 (X + 2368) -> s9 = Z_to_bv 64 c ->
  s10 = Z_to_bv 64 32 ->
  X mod 16 = 0 -> 0 <= c <= 8 -> 0 <= i -> at_byte B i 123 = true ->
  (if at_byte B (json_ws B (i + 1)) 125 then Some (json_ws B (i + 1) + 1, jobj_empty)
   else json_pairs B (json_ws B (i + 1)) jobj_empty (length B)) = Some (i2, o') ->
  length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] ->
  rw_cells rsegs m (X + 208) [CB 8 j208] -> rw_cells rsegs m (X + 232) [CB 8 j232] ->
  rw_cells rsegs m (X + 240) [CB 8 j240] -> rw_cells rsegs m (X + 248) [CB 8 j248] ->
  rw_cells rsegs m (X + 1024) [CB 20 jk] -> rw_cells rsegs m (X + 1044) [CB 4 vpk] ->
  rw_cells rsegs m (X + 1056 + 144 * c) [CB 144 jo] ->
  rw_cells rsegs m (X + 2352) [CB 20 jv] -> rw_cells rsegs m (X + 2372) [CB 4 vpad] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  evt rsegs
    (fun ms' =>
       (exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 (Z_to_bv 64 (X + 1056 + 144 * c)) (Z_to_bv 64 (i2 - 1)) s7 s8 s9 s10 s11
                        t3' t4' t5' t6')
                   F (Z_to_bv 64 0x13b74) fc None m' (seg_rom rsegs) /\
          munch [(X + 1056 + 144 * c, X + 1200 + 144 * c)] m m' /\
          wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
          rw_cells rsegs m' (X + 1056 + 144 * c) [CB 144 (obj_bytes b vpad o')]) \/
       (exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
               (j ks kl : Z) (f : nat),
          0 <= json_ws B (i + 1) /\ jscalar B (json_ws B (i + 1)) = Some (j, 1, ks, kl) /\
          json_pairs B (json_ws B (i + 1)) jobj_empty (S f) = Some (i2, o') /\
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (X + 1056 + 144 * c + 48)) s1 (Z_to_bv 64 j)
                        a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (Z_to_bv 64 (X + 1056 + 144 * c))
                        (Z_to_bv 64 (json_ws B (i + 1))) (Z_to_bv 64 (X + 1056 + 144 * c + 24)) s8
                        (Z_to_bv 64 1) s10 (Z_to_bv 64 0) t3' t4' t5' t6')
                   F (Z_to_bv 64 0x1394c) fc None m' (seg_rom rsegs) /\
          munch [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044);
                 (X + 1056 + 144 * c, X + 1200 + 144 * c)] m m' /\
          wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
          bytes_at rsegs m' b (pf_bytes (B ++ [0])) /\
          rw_cells rsegs m' (X + 1024)
            [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] /\
          rw_cells rsegs m' (X + 1044) [CB 4 vpk] /\
          rw_cells rsegs m' (X + 240) [C8 (Z_to_bv 64 c)] /\
          rw_cells rsegs m' (X + 248) [C8 (Z_to_bv 64 (X + 1056 + 144 * c + 72))] /\
          rw_cells rsegs m' (X + 232) [C8 (Z_to_bv 64 (X + 1056 + 144 * c + 96))] /\
          rw_cells rsegs m' (X + 208) [C8 (Z_to_bv 64 (X + 1056 + 144 * c + 120))] /\
          rw_cells rsegs m' (X + 1056 + 144 * c) [CB 144 (obj_bytes b vpad jobj_empty)] /\
          rw_cells rsegs m' (X + 2352) [CB 20 jv] /\ rw_cells rsegs m' (X + 2372) [CB 4 vpad] /\
          bytes_at rsegs m' JSON_SCALAR_L js_table))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)).
Proof.
  intros JS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b c i i2 B o' jk vpk jv vpad jo j208 j232 j240 j248 Esp Es1 Es2 Es3 Es4 Es6 Es8 Es9 Es10
    HX16 Hc Hi A123 JP Lk Lv Ljv Hb Hbl FB BB C176 C208 C232 C240 C248 CK CV CO CJ CP JTB MI ST HK HI HX.
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite ulength_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  assert (HV8 : (X + 1024) mod 8 = 0) by (clear - HX16; Z.div_mod_to_equations; lia).
  assert (Hc8 : (X + 1056 + 144 * c) mod 8 = 0) by (clear - HX16; Z.div_mod_to_equations; lia).
  destruct (at_byte_true B i 123 A123) as [L0 C0].
  set (i1 := json_ws B (i + 1)) in *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1. fold i1 in G1.
  assert (L1 : i1 < jlen B).
  { destruct (at_byte B i1 125) eqn:A; [exact (proj1 (at_byte_true B i1 125 A))|].
    destruct (length B) as [|f]; [discriminate JP|]. cbn [json_pairs] in JP.
    destruct (jscalar B i1) as [[[[j kk] ks] kl]|] eqn:JS1; [|discriminate JP].
    exact (proj1 (js_rng B i1 j kk ks kl JS1)). }
  pose proof CK as CKw. apply user_cb in CKw as (_ & _ & WK).
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044);
              (X + 1056 + 144 * c, X + 1200 + 144 * c)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  subst sp s1 s2 s3 s4 s6 s8 s9 s10.
  step. step. step.
  step. rewrite ltu_lit by lia. replace (8 <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. rewrite ?(unsigned_lit c) by lia.
  step. step. rewrite utok_nt_ltu by lia. cbv iota.
  step. step. replace (X + 1056 + c * 144) with (X + 1056 + 144 * c) by lia.
  step. step. step. step.
  eapply evt_cut.
  { eapply memset_holds; [|exact MI]. rewrite !unsigned_lit by lia. exact CO. }
  intros ms' (t0x & t1x & t2x & a1y & a2y & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m1 &
              E & MU1 & WM1 & MI1 & CZ).
  subst ms'. rewrite !unsigned_lit in MU1, CZ by lia.
  assert (MUz : munch [(X + 1056 + 144 * c, X + 1200 + 144 * c)] m m1)
    by (eapply munch_weaken; [|exact MU1]; unfold sub_fp; cbn [outside]; intros; lia).
  transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  assert (CZ1 : rw_cells rsegs m1 (X + 1056 + 144 * c) [CB 144 (obj_bytes b vpad jobj_empty)])
    by (rewrite obj_bytes_empty; exact CZ).
  clear CZ.
  rewrite (ret_pc_even 0x138a4) by (first [lia | reflexivity]).
  pose proof (uws_rd m1 b B i BB ltac:(lia)) as RD0. pose proof (ws_byte B i FB) as HC0.
  step. rewrite ltu_lit by lia. replace (i <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia. rewrite C0, Z.eqb_refl. cbn [negb].
  cbv iota.
  step.
  eapply evt_cut.
  { eapply uws_L9 with (b := b) (i := i + 1) (B := B);
      first [reflexivity | (f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia) | lia | assumption]. }
  intros ms' [a0x E]. subst ms'. fold i1.
  replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
  pose proof (uws_rd m1 b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia.
  destruct (at_byte B i1 125) eqn:A125.
  - destruct (at_byte_true B i1 125 A125) as [_ C125]. rewrite C125, Z.eqb_refl. cbv iota.
    injection JP as Ei2 Eo. subst i2 o'. replace (i1 + 1 - 1) with i1 by lia.
    apply evt_done. left. do 16 eexists. exists m1.
    split; [reflexivity|]. split; [exact MUz|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
    exact CZ1.
  - assert (C125 : (jbyte B i1 =? 125) = false).
    { unfold at_byte in A125. replace (i1 <? jlen B) with true in A125 by (symmetry; apply Z.ltb_lt; lia).
      exact A125. }
    rewrite C125. cbv iota.
    assert (LBf : (0 < length B)%nat) by (unfold jlen in L1; lia).
    pose proof (Nat.succ_pred_pos (length B) LBf) as LBs. rewrite <- LBs in JP.
    set (f := Nat.pred (length B)) in *.
    pose proof JP as JP1. cbn [json_pairs] in JP1.
    destruct (jscalar B i1) as [[[[j kk] ks] kl]|] eqn:JS1; cbv iota in JP1; [|discriminate JP1].
    destruct (kk =? 1) eqn:K1; cbn [negb] in JP1; cbv iota in JP1; [|discriminate JP1].
    apply Z.eqb_eq in K1. subst kk. clear JP1.
    pose proof (js_rng B i1 j 1 ks kl JS1) as [_ G2].
    clear MUz. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    step. step. step. step. step. step.
    eapply (ujs_call JS) with (lo := lo) (X := X) (b := b) (i := i1) (V := X + 1024) (B := B) (j := j) (k := 1)
      (s := ks) (l := kl); [ujs_side .. | ].
    intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU3 WM3 MI3 ST3 BV.
    rewrite (ret_pc_even 0x1391c) by (first [lia | reflexivity]).
    unfold JSON_SCALAR_K in MU3.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI1.
    pose proof (utok_cells m3 (X + 1024) _ _ _ BV WK) as CK1. clear BV.
    step. rewrite eqb_lit by lia. replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    cbv iota.
    step. step. if_vm.
    step. rewrite (uand7_zero (X + 1056 + 144 * c)) by first [assumption | lia].
    step. step. step. step. step. step. step. step.
    apply evt_done. right. do 16 eexists. exists j, ks, kl, f.
    split; [lia|]. split; [reflexivity|]. split; [exact JP|]. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [exact (ucells_cb3 _ _ _ _ _ CK1)|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    eassumption.
Qed.
