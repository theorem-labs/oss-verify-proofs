From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser_J2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_ws uslot_ser_tokb.
Import ListNotations.
Open Scope Z_scope.

Ltac ult_t := lazymatch goal with |- context [?x <? ?y] => replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) end;
  cbn [negb]; cbv iota.

Lemma uswrap32 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma uobj_tail_e : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X b count i2 : Z) (B : list Z),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 (i2 - 1) -> s9 = Z_to_bv 64 count -> s10 = Z_to_bv 64 32 ->
  0 <= count < IMAX -> 1 <= i2 ->
  ((at_byte B (json_ws B i2) 44 = true /\ at_byte B (json_ws B (json_ws B i2 + 1)) 123 = true) \/
   (at_byte B (json_ws B i2) 44 = false /\ at_byte B (json_ws B i2) 93 = true /\
    json_ws B (json_ws B i2 + 1) = jlen B)) ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' : word,
          at_byte B (json_ws B i2) 44 = false /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 (jlen B)) s7 s8 (Z_to_bv 64 (count + 1)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs)) \/
       (exists a0' a1' : word,
          at_byte B (json_ws B i2) 44 = true /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 (json_ws B (json_ws B i2 + 1))) s7 s8 (Z_to_bv 64 (count + 1))
                        s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b74) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X b count i2 B Esp Es1 Es2 Es3 Es4 Es6 Es9 Es10 Hc Hi2 MD Hb HbB FB BB C216.
  set (i3 := json_ws B i2) in *.
  assert (L3 : i3 < jlen B) by (destruct MD as [(A & _)|(_ & A & _)]; exact (proj1 (at_byte_true _ _ _ A))).
  assert (L2 : i2 < jlen B) by (apply (ws_lt B i2); [lia | exact L3]).
  pose proof (ws_ge B i2 ltac:(lia)) as G3. fold i3 in G3.
  pose proof (uws_rd m b B i3 BB ltac:(lia)) as RD3. pose proof (ws_byte B i3 FB) as HC3.
  unfold IMAX in Hc.
  subst sp s1 s2 s3 s4 s6 s9 s10.
  step. step. rewrite utok_imax by (unfold IMAX; lia). cbv iota.
  step. try rewrite (unsigned_lit (i2 - 1)) by lia.
  eapply evt_cut.
  { eapply uws_L15 with (b := b) (i := i2) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a0x E]. subst ms'. fold i3.
  step. rewrite ltu_lit by lia. ult_t.
  step. step. rewrite ws_zxb by lia.
  step. step. rewrite eqb_lit by lia.
  destruct MD as [(A44 & A123)|(A44 & A93 & HW)].
  - destruct (at_byte_true B i3 44 A44) as [_ C44]. rewrite C44, Z.eqb_refl. cbn [negb]. cbv iota.
    step. try rewrite (unsigned_lit i3) by lia.
    eapply evt_cut.
    { eapply uws_L16 with (b := b) (i := i3 + 1) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
    intros ms' [a0y E]. subst ms'.
    step. try rewrite (unsigned_lit count) by lia.
    step.
    apply evt_done. right. do 2 eexists. split; [exact A44|]. reflexivity.
  - destruct (at_byte_true B i3 93 A93) as [_ C93].
    replace (jbyte B i3 =? 44) with false by (rewrite C93; reflexivity). cbn [negb]. cbv iota.
    step. step. rewrite eqb_lit by lia. rewrite C93, Z.eqb_refl. cbn [negb]. cbv iota.
    step. try rewrite (unsigned_lit i3) by lia.
    step. try rewrite (unsigned_lit count) by lia. try rewrite uswrap32 by lia.
    eapply evt_cut.
    { eapply uws_L17 with (b := b) (i := i3 + 1) (B := B); first [reflexivity | (f_equal; lia) | lia | assumption]. }
    intros ms' [a0y E]. subst ms'.
    apply evt_done. left. do 2 eexists. split; [exact A44|]. reflexivity.
Qed.

Lemma uobj_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X b count i2 : Z) (B : list Z),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 (i2 - 1) -> s10 = Z_to_bv 64 32 ->
  0 <= count < IMAX -> 1 <= i2 ->
  ((at_byte B (json_ws B i2) 44 = true /\ at_byte B (json_ws B (json_ws B i2 + 1)) 123 = true) \/
   (at_byte B (json_ws B i2) 44 = false /\ at_byte B (json_ws B i2) 93 = true /\
    json_ws B (json_ws B i2 + 1) = jlen B)) ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] -> rw_cells rsegs m (X + 240) [C8 (Z_to_bv 64 count)] ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' : word,
          at_byte B (json_ws B i2) 44 = false /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 (jlen B)) s7 s8 (Z_to_bv 64 (count + 1)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs)) \/
       (exists a0' a1' : word,
          at_byte B (json_ws B i2) 44 = true /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 (json_ws B (json_ws B i2 + 1))) s7 s8 (Z_to_bv 64 (count + 1))
                        s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b70) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X b count i2 B Esp Es1 Es2 Es3 Es4 Es6 Es10 Hc Hi2 MD Hb HbB FB BB C216 C240.
  subst sp.
  step.
  eapply uobj_tail_e with (X := X) (b := b) (count := count) (i2 := i2) (B := B);
    first [reflexivity | eassumption | lia].
Qed.
