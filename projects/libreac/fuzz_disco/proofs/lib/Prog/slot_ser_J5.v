From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs memset_c memset.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_ws slot_ser_J0 slot_ser slot_ser_J2 slot_ser_J4.
Import ListNotations.
Open Scope Z_scope.

Ltac lt_t := lazymatch goal with |- context [?x <? ?y] => replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) end;
  cbn [negb]; cbv iota.
Ltac ge_t := lazymatch goal with |- context [?x <? ?y] => replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) end;
  cbn [negb]; cbv iota.

Lemma sltiu_c : forall c, 0 <= c < 8 -> v_sltiu (Z_to_bv 64 c) 8 = Z_to_bv 64 1.
Proof.
  intros c Hc. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 8) with 8.
  replace (c <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma obj_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X b c i2 : Z) (B : list Z) (jr : list byte),
  sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s1 = Z_to_bv 64 c -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 (i2 - 1) -> s7 = Z_to_bv 64 (- jlen B) ->
  0 <= c <= 7 -> 1 <= i2 ->
  ((at_byte B (json_ws B i2) 44 = true /\ at_byte B (json_ws B (json_ws B i2 + 1)) 123 = true) \/
   (at_byte B (json_ws B i2) 44 = false /\ at_byte B (json_ws B i2) 93 = true /\
    json_ws B (json_ws B i2 + 1) = jlen B)) ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 (b + 1))] ->
  rw_cells rsegs m (X + 1168 + 144 * c) [CB (Z.to_nat (1152 - 144 * c)) jr] ->
  mem_inv rsegs m -> 0 < X -> X + 2592 < 2 ^ 63 ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' a2' a3' : word,
          at_byte B (json_ws B i2) 44 = false /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 (c + 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x140bc) fc None m (seg_rom rsegs)) \/
       (exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
          at_byte B (json_ws B i2) 44 = true /\
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (c + 1)) a0' a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 (Z_to_bv 64 (X + 1024 + 144 * (c + 1))) (Z_to_bv 64 (c + 1)) s7 s8 (Z_to_bv 64 1)
                        (Z_to_bv 64 (json_ws B (json_ws B i2 + 1))) s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x13954) fc None m' (seg_rom rsegs) /\
          munch [(X + 1168 + 144 * c, X + 1312 + 144 * c)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          rw_cells rsegs m' (X + 1168 + 144 * c) [CB 144 (repeat (Z_to_bv 8 0) 144)] /\
          rw_cells rsegs m' (X + 1312 + 144 * c) [CB (Z.to_nat (1008 - 144 * c)) (skipn 144 jr)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c0c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X b c i2 B jr Esp Es0 Es1 Es2 Es3 Es4 Es6 Es7 Hc Hi2 MD Hb HbB FB BB C224 CR MI HX0 HX.
  set (i3 := json_ws B i2) in *.
  assert (L3 : i3 < jlen B) by (destruct MD as [(A & _)|(_ & A & _)]; exact (proj1 (at_byte_true _ _ _ A))).
  assert (L2 : i2 < jlen B) by (apply (ws_lt B i2); [lia | exact L3]).
  pose proof (ws_ge B i2 ltac:(lia)) as G3. fold i3 in G3.
  destruct (ser_split m (X + 1168 + 144 * c) (X + 1312 + 144 * c) 144 (Z.to_nat (1008 - 144 * c))
              (Z.to_nat (1152 - 144 * c)) jr ltac:(lia) ltac:(lia) CR) as [CR1 CR2]. clear CR.
  pose proof (munch_refl [(X + 1168 + 144 * c, X + 1312 + 144 * c)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (ws_rd m b B i3 BB ltac:(lia)) as RD3. pose proof (ws_byte B i3 FB) as HC3.
  subst sp s0 s1 s2 s3 s4 s6 s7.
  step. step. rewrite ltu_lit by lia. lt_t.
  step. rewrite (not_neg (i2 - 1)) by lia.
  step. step.
  eapply evt_cut.
  { eapply ws_L15 with (b := b) (i := i2) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a1x E]. subst ms'. fold i3.
  step. rewrite neg_lit, Z.opp_involutive.
  step. rewrite ltu_lit by lia. lt_t.
  step. step. rewrite ws_zxb by lia.
  step. step. step. rewrite eqb_lit by lia.
  destruct MD as [(A44 & A123)|(A44 & A93 & HW)].
  - destruct (at_byte_true B i3 44 A44) as [_ C44]. rewrite C44, Z.eqb_refl. cbn [negb]. cbv iota.
    set (i4 := json_ws B (i3 + 1)) in *.
    destruct (at_byte_true B i4 123 A123) as [L4 _].
    pose proof (ws_ge B (i3 + 1) ltac:(lia)) as G4. fold i4 in G4.
    assert (L31 : i3 + 1 < jlen B) by (apply (ws_lt B (i3 + 1)); [lia | exact L4]).
    step. step. rewrite ltu_lit by lia. lt_t.
    step. rewrite (not_neg i3) by lia. step. step.
    eapply evt_cut.
    { eapply ws_L16 with (b := b) (i := i3 + 1) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
    intros ms' [a2x E]. subst ms'. fold i4.
    step. rewrite neg_lit, Z.opp_involutive.
    step. step. rewrite ltu_lit by lia. lt_t.
    step. step. step. step. step.
    rewrite (sltiu_c c) by lia. rewrite (unsigned_lit (c + 1)) by lia.
    replace (X + 1024 + (c + 1) * 144) with (X + 1024 + 144 * (c + 1)) by lia.
    step. step. step. step.
    eapply evt_cut.
    { eapply memset_holds; [|exact MI]. rewrite !unsigned_lit by lia.
      replace (X + 1024 + 144 * (c + 1)) with (X + 1168 + 144 * c) by lia. exact CR1. }
    intros ms' (t0x & t1x & t2x & a1y & a2y & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m1 &
                E & MU1 & WM1 & MI1 & CZ).
    subst ms'. rewrite !unsigned_lit in MU1, CZ by lia.
    replace (X + 1024 + 144 * (c + 1)) with (X + 1168 + 144 * c) in MU1, CZ by lia.
    transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    rewrite (ret_pc_even 0x13cd4) by (first [lia | reflexivity]).
    step.
    step. rewrite ltu_lit by lia. lt_t.
    step.
    apply evt_done. right. do 16 eexists. exists m1.
    split; [exact A44|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    split; [exact CZ|exact CR2].
  - destruct (at_byte_true B i3 93 A93) as [_ C93].
    replace (jbyte B i3 =? 44) with false by (rewrite C93; reflexivity). cbn [negb]. cbv iota.
    step. step. rewrite eqb_lit by lia. rewrite C93, Z.eqb_refl. cbn [negb]. cbv iota.
    step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (i3 + 1) (jlen B)) as [Lt|Ge]; cbn [negb]; cbv iota.
    + step. rewrite (not_neg i3) by lia. step. rewrite neg_lit. step.
      eapply evt_cut.
      { eapply ws_L17 with (b := b) (i := i3 + 1) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
      intros ms' [a3x E]. subst ms'. apply evt_done. left. do 4 eexists. split; [exact A44|]. reflexivity.
    + assert (E1 : i3 + 1 = jlen B) by (rewrite (ws_past B (i3 + 1)) in HW by lia; exact HW).
      step. rewrite eqb_lit by lia. rewrite E1, Z.eqb_refl. cbn [negb]. cbv iota.
      apply evt_done. left. do 4 eexists. split; [exact A44|]. reflexivity.
Qed.
