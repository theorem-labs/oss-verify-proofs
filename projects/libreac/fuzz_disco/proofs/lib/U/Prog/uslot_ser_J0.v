From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_ws slot_ser_J0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c uslot_ser_ws.
Import ListNotations.
Open Scope Z_scope.

Lemma uslot_R10 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b count : Z) (B : list Z) (os : list jobj),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) ->
  s10 = Z_to_bv 64 32 ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  json_read B 9 = Some (count, os) ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' s6' : word, count = 0 /\ os = [] /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6' s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs)) \/
       (exists (a0' a1' : word) (i1 : Z),
          0 <= i1 /\ json_objs B i1 0 9 [] (length B) = Some (count, os) /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 i1) s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b count B os
    E1 E2 E3 E4 E10 Hb HbB FB BB JR.
  destruct (jr_unfold B count os JR) as [A0 JR'].
  set (i0 := json_ws B 0) in *. set (i1 := json_ws B (i0 + 1)) in *.
  pose proof (ws_ge B 0 ltac:(lia)) as G0. fold i0 in G0.
  pose proof (ws_ge B (i0 + 1) ltac:(lia)) as G1. fold i1 in G1.
  destruct (at_byte_true B i0 91 A0) as [L0 C0].
  assert (L1 : i1 < jlen B).
  { destruct JR' as [(A1 & _)|(_ & JO)]; [exact (proj1 (at_byte_true B i1 93 A1))|].
    exact (proj1 (at_byte_true B i1 123 (jobjs_first _ _ _ _ _ _ _ JO))). }
  subst s1 s2 s3 s4 s10.
  step.
  eapply evt_cut.
  { eapply (uws_L5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b 0 B);
      first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a1' E]. subst ms'. fold i0.
  step. rewrite ltu_lit by lia. replace (i0 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  step. step. rewrite C0, eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  step.
  eapply evt_cut.
  { eapply (uws_L6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (i0 + 1) B);
      first [reflexivity | (f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia) | lia | assumption]. }
  intros ms' [a0' E]. subst ms'. fold i1.
  replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
  pose proof (uws_rd m b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia.
  destruct JR' as [(A1 & W2 & Ec & Eo)|(A1 & JO)].
  - destruct (at_byte_true B i1 93 A1) as [_ C1]. rewrite C1, Z.eqb_refl. cbn [negb]. cbv iota.
    step.
    eapply evt_cut.
    { eapply (uws_L7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (i1 + 1) B);
        first [reflexivity | (f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia) | lia | assumption]. }
    intros ms' [a0x E]. subst ms'. rewrite W2.
    step. step. rewrite !Z.lxor_nilpotent.
    replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    step. step. apply evt_done. left. do 3 eexists. split; [exact Ec|]. split; [exact Eo|]. reflexivity.
  - assert (C1 : jbyte B i1 <> 93).
    { intro C. unfold at_byte in A1. rewrite (proj2 (Z.ltb_lt _ _) L1), C in A1. discriminate. }
    rewrite (proj2 (Z.eqb_neq _ _) C1). cbn [negb]. cbv iota.
    step. apply evt_done. right. do 2 eexists. exists i1. split; [lia|]. split; [exact JO|]. reflexivity.
Qed.
