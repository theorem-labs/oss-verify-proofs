(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.

Module AXF_p5.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition e_rsv := EVar 42.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB2 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EAlu ALU_SRL e_W (ELit 5)) (ELit 1)).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition STK := SA (EVar 2) (-1024).
Definition ENDR5 := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD SLOTK (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition sr_p5 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_p5 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 160 191;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 0 3071;
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA TAB1 98984) 2 e_sz;
    KWord (SA TAB2 98984) 2 e_sz;
    KWord (SA ENDB 12) 1 (ELit 0);
    KWord (SA ENDB 8) 4 e_rsv;
    KWord (SA ENDB 7) 1 (ELit 0);
    KWord (SA ENDR5 12) 1 (ELit 0);
    KRange ENDR5 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDR5 12) (ELit 1);
    KRange ENDB 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDB 0) (ELit 13);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_p5 : scripts := SCR [true; true; true; true; false; true; true] [] [].
Definition ss_p5 := SS 0x511d0 sr_p5 [] kn_p5 43.
Definition RUN_p5 := sym_exec SEGS 300 true [0x516d0] scr_p5 ss_p5 [].

Definition RES_p5 := Eval vm_compute in RUN_p5.
Lemma RES_p5_ok : sym_exec SEGS 300 true [0x516d0] scr_p5 (SS 0x511d0 sr_p5 [] kn_p5 43) [] = RES_p5.
Proof. vm_compute. reflexivity. Qed.
End AXF_p5.

Module AXF_p5z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngFree MngFree5 AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma ext4_zero : forall x, ext_Z false 0 4 x = x mod 2^32.
Proof.
  intros x. unfold ext_Z. cbn [Z.of_nat N.of_nat]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (8 * N.pos 4)%N with 32%N. reflexivity.
Qed.

Section P5.
Context {fx : FPState}.

#[using="Type"] Theorem p5_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B rsv : Z),
  free_pre5 regs m h3 off16 G avail freed W secret sz B rsv ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B rsv FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 HIMG GIMG AG8 Rrsv Mrsv Mend5].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B; 0; rsv] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_p5 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = rsv) by exact (u_wa_small _ (rng64 _ _ _ Rrsv eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (ZTAB1 : zeval E TAB1 = 2 * Z.shiftr W 6).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37.
    assert (R52 : 0 <= 4503599627370496 * W <= 4503599627370496 * 3071) by (clear - RW; lia).
    rewrite (mod64_of_range _ _ _ R52 eq_refl eq_refl). change (58 mod 64) with 58. f_equal.
    clear - RW. rewrite !Z.shiftr_div_pow2 by lia. change (2^58) with (4503599627370496 * 64). change (2^6) with 64.
    rewrite <- Z.div_div by lia. rewrite (Z.mul_comm 4503599627370496 W), Z.div_mul by lia. reflexivity. }
  assert (ZTAB2 : zeval E TAB2 = 2 * Z.shiftr W 6).
  { cbn [zeval edenot TAB2 e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl).
    assert (RW5 : 0 <= Z.shiftr W 5 <= 95).
    { clear - RW. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
    change (5 mod 64) with 5. change (1 mod 64) with 1. rewrite (mod64_of_range _ _ _ RW5 eq_refl eq_refl).
    rewrite Z.shiftr_shiftr by (clear; lia). reflexivity. }
  assert (ZSLOTK : zeval E SLOTK = 16 * sz * Z.land h3 31).
  { change (zeval E SLOTK) with (zeval E (EMd M_MUL (ELit 16) e_sz) * zeval E (EAlu ALU_AND e_h3 (ELit 31))).
    rewrite ZIDX. cbn [zeval edenot e_sz]. rewrite Z39. reflexivity. }
  assert (ZENDB : zeval E ENDB = 16 * sz + (B + 16 * sz * Z.land h3 31)).
  { change (zeval E ENDB) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + zeval E SLOTK)).
    rewrite ZSLOTK. cbn [zeval edenot e_sz e_B]. rewrite Z39, Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * Z.shiftr W 6 <= 94).
  { clear - RW. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
    assert (0 <= W / 64 <= 47) by (split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]). lia. }
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (ZENDR5 : zeval E ENDR5 = 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv))).
  { change (zeval E ENDR5) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + (zeval E SLOTK + (-1) * zeval E (EExt false 0 4 e_rsv)))).
    rewrite ZSLOTK. cbn [zeval edenot e_sz e_B e_rsv]. rewrite Z39, Z40, Z42.
    rewrite (mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ext4_zero, (Z.mod_small rsv) by (clear - Rrsv; lia). reflexivity. }
  assert (HK : know_ok SEGS E m kn_p5).
  { unfold know_ok, kn_p5.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZTAB2, ?ZENDB, ?ZENDR5.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B e_rsv STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl); assumption).
    all: right; clear - D1; lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_p5))).
  { cbn [RES_p5 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl).
    all: rewrite ?ext4_zero, ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(Z.mod_small rsv (2^32)) by (clear - Rrsv; lia).
    - clear - A5 Rsz Roff L31h Rrsv. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite !Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite Z.mod_small by (clear - Rrsv; lia). apply Z.ltb_lt. clear - Rrsv; lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_p5 0x511d0 sr_p5 kn_p5 43 _ _ _ E m rom regs RES_p5_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_p5 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_p5 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End P5.
End AXF_p5z.


Module AXF_pd5.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition e_rsv := EVar 42.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition ML := EAlu ALU_SRL e_W (ELit 12).
Definition MSTR := EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (ELit (-16)).
Definition IDX := EAlu ALU_AND e_h3 (ELit 31).
Definition ENDM := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX)).
Definition ENDMR5 := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EAlu ALU_ADD (EMd M_MUL MSTR IDX) (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition STK := SA (EVar 2) (-1024).
Definition ENDR5 := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD SLOTK (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition sr_pd5 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_pd5 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 160 191;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange TAB1 0 126;
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA TAB1 98984) 2 e_sz;
    KWord (SA ENDM (-4)) 1 (ELit 0);
    KWord (SA ENDM (-8)) 4 e_rsv;
    KWord (SA ENDM (-9)) 1 (ELit 0);
    KRange ENDM 9 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDM (-9)) (ELit 6);
    KWord (SA ENDMR5 (-4)) 1 (ELit 0);
    KRange ENDMR5 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDMR5 (-4)) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_pd5 : scripts := SCR [true; true; true; false; true; false; true; false; true; true] [] [].
Definition ss_pd5 := SS 0x511d0 sr_pd5 [] kn_pd5 43.
Definition RUN_pd5 := sym_exec SEGS 300 true [0x516d0] scr_pd5 ss_pd5 [].

Definition scr_qd5 : scripts := SCR [true; true; true; false; true; false; true; false; true; true] [] [].
Definition RES_qd5 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_qd5 ss_pd5 [].
Lemma RES_qd5_ok : sym_exec SEGS 300 true [0x516d0] scr_qd5 (SS 0x511d0 sr_pd5 [] kn_pd5 43) [] = RES_qd5.
Proof. vm_compute. reflexivity. Qed.
End AXF_pd5.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pd5.
Import ListNotations AX2 AX2S.

Module AXF_p4m.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_p4m := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_p4m : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 0 159;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange TAB1 0 126;
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA TAB1 98984) 2 e_sz;
    KWord (SA TAB3 98984) 2 e_sz;
    KWord (SA ENDB 12) 1 (ELit 0);
    KWord (SA ENDRB 12) 1 (ELit 0);
    KRange ENDB 1 (2^63-1);
    KRange ENDRB 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDB 12) (ELit 1);
    KDisj STK (ELit 1024) (SA ENDRB 12) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_p4m : scripts := SCR [true; true; true; false; true; false; true; true; true] [] [].
Definition ss_p4m := SS 0x511d0 sr_p4m [] kn_p4m 42.
Definition RUN_p4m := sym_exec SEGS 300 true [0x516d0] scr_p4m ss_p4m [].

Definition scr_pm4 : scripts := SCR [true; true; true; false; true; false; true; true; true] [] [].
Definition RES_pm4 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_pm4 ss_p4m [].
Lemma RES_pm4_ok : sym_exec SEGS 300 true [0x516d0] scr_pm4 (SS 0x511d0 sr_p4m [] kn_p4m 42) [] = RES_pm4.
Proof. vm_compute. reflexivity. Qed.
End AXF_p4m.

Module AXF_p4mz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p4m.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record free_prem (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B : Z) : Prop := {
  fm_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fm_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fm_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fm_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fm_RB : 1 <= B <= 2^63-1 ;
  fm_AB : B mod 16 = 0 ;
  fm_Roff : 0 <= off16 <= 65535 ;
  fm_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fm_Rh3 : 0 <= h3 <= 159 ;
  fm_RG : 1 <= G <= 2^63-1 ;
  fm_Rav : 0 <= avail <= 2^32 - 1 ;
  fm_Rfr : 0 <= freed <= 2^32 - 1 ;
  fm_RW : 4096 <= W <= 2^64 - 1 ;
  fm_Rsz : 1 <= sz <= 8191 ;
  fm_Rsec : 0 <= secret <= 2^64 - 1 ;
  fm_REND : 1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ;
  fm_RENDR : 1 <= 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) <= 2^63-1 ;
  fm_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fm_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fm_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fm_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fm_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fm_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fm_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fm_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fm_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fm_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm_Mtab : rdn SEGS m (wa (2 * SCW W + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  fm_Mend : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm_Mendr : rdn SEGS m (wa (16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fm_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fm_D1 : 16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D2 : 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fm_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fm_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fm_A1 : Z.land h3 31 <= Z.land W 31 ;
  fm_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fm_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fm_A4 : sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ;
  fm_A5 : Z.shiftr h3 5 <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ;
  fm_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fm_A7 : Z.land W 31 <> 0 ;
  fm_A8 : SCW W <= 47 ;
  fm_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fm_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fm_AG : G mod 8 = 0
}.

Section P4M.
Context {fx : FPState}.

#[using="Type"] Theorem p4m_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B : Z),
  free_prem regs m h3 off16 G avail freed W secret sz B ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 A6 A7 A8 HIMG GIMG AG8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_p4m regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (S5h : 0 <= Z.shiftr h3 5 <= 4) by (clear - Rh3; apply shiftr5_bound; lia).
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (ZTAB3 : zeval E TAB3 = 2 * SCW W).
  { cbn [zeval edenot TAB3 e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). change (5 mod 64) with 5.
    apply TB1_SCW. lia. }
  assert (ZSLOTK : zeval E SLOTK = 16 * sz * Z.land h3 31).
  { change (zeval E SLOTK) with (zeval E (EMd M_MUL (ELit 16) e_sz) * zeval E (EAlu ALU_AND e_h3 (ELit 31))).
    rewrite ZIDX. cbn [zeval edenot e_sz]. rewrite Z39. reflexivity. }
  assert (ZENDB : zeval E ENDB = 16 * sz + (B + 16 * sz * Z.land h3 31)).
  { change (zeval E ENDB) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + zeval E SLOTK)).
    rewrite ZSLOTK. cbn [zeval edenot e_sz e_B]. rewrite Z39, Z40. reflexivity. }
  assert (ZENDRB : zeval E ENDRB = 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31))).
  { change (zeval E ENDRB) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + ((-1) * zeval E (EAlu ALU_SRL e_h3 (ELit 5)) + zeval E SLOTK))).
    rewrite ZSLOTK, ZRC. cbn [zeval edenot e_sz e_B]. rewrite Z39, Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (HK : know_ok SEGS E m kn_p4m).
  { unfold know_ok, kn_p4m.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZTAB3, ?ZENDB, ?ZENDRB.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: fail. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_pm4))).
  { cbn [RES_pm4 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl), ?(mod64_of_range _ _ _ S5h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    - clear - A5 Rsz Roff L31h S5h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - apply negb_true_iff, Z.eqb_neq. exact A7.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - apply Z.ltb_ge. exact A8.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_pm4 0x511d0 sr_p4m kn_p4m 42 _ _ _ E m rom regs RES_pm4_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_pm4 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_pm4 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End P4M.
End AXF_p4mz.

Module AXF_p5m.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition e_rsv := EVar 42.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition STK := SA (EVar 2) (-1024).
Definition ENDR5 := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD SLOTK (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition sr_p5m := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_p5m : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 160 191;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange TAB1 0 126;
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA TAB1 98984) 2 e_sz;
    KWord (SA TAB3 98984) 2 e_sz;
    KWord (SA ENDB 12) 1 (ELit 0);
    KWord (SA ENDB 8) 4 e_rsv;
    KWord (SA ENDB 7) 1 (ELit 0);
    KWord (SA ENDR5 12) 1 (ELit 0);
    KRange ENDR5 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDR5 12) (ELit 1);
    KRange ENDB 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDB 0) (ELit 13);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_p5m : scripts := SCR [true; true; true; false; true; false; true; true; true; true] [] [].
Definition ss_p5m := SS 0x511d0 sr_p5m [] kn_p5m 43.
Definition RUN_p5m := sym_exec SEGS 300 true [0x516d0] scr_p5m ss_p5m [].

Definition scr_pm5 : scripts := SCR [true; true; true; false; true; false; true; true; true; true] [] [].
Definition RES_pm5 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_pm5 ss_p5m [].
Lemma RES_pm5_ok : sym_exec SEGS 300 true [0x516d0] scr_pm5 (SS 0x511d0 sr_p5m [] kn_p5m 43) [] = RES_pm5.
Proof. vm_compute. reflexivity. Qed.
End AXF_p5m.

Module AXF_p5mz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5m.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record free_prem5 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B rsv : Z) : Prop := {
  fm5_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fm5_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fm5_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fm5_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fm5_RB : 1 <= B <= 2^63-1 ;
  fm5_AB : B mod 16 = 0 ;
  fm5_Roff : 0 <= off16 <= 65535 ;
  fm5_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fm5_Rh3 : 160 <= h3 <= 191 ;
  fm5_RG : 1 <= G <= 2^63-1 ;
  fm5_Rav : 0 <= avail <= 2^32 - 1 ;
  fm5_Rfr : 0 <= freed <= 2^32 - 1 ;
  fm5_RW : 4096 <= W <= 2^64 - 1 ;
  fm5_Rsz : 1 <= sz <= 8191 ;
  fm5_Rsec : 0 <= secret <= 2^64 - 1 ;
  fm5_REND : 1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ;
  fm5_RENDR : 1 <= 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) <= 2^63-1 ;
  fm5_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm5_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fm5_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fm5_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fm5_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fm5_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fm5_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fm5_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fm5_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fm5_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fm5_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm5_Mtab : rdn SEGS m (wa (2 * SCW W + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  fm5_Mend : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm5_Mendr : rdn SEGS m (wa (16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm5_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fm5_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fm5_D1 : 16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D2 : 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fm5_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fm5_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fm5_A1 : Z.land h3 31 <= Z.land W 31 ;
  fm5_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fm5_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fm5_A4 : sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ;
  fm5_A5 : rsv <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ;
  fm5_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fm5_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fm5_AG : G mod 8 = 0 ;
  fm5_Rrsv : 5 <= rsv <= 2^32 - 1 ;
  fm5_Mrsv : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 8)) 4 = Some (word_to_le_bytes 4 (wa rsv)) ;
  fm5_Mend5 : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 7)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fm5_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fm5_A7 : Z.land W 31 <> 0 ;
  fm5_A8 : SCW W <= 47
}.

Section P5M.
Context {fx : FPState}.

#[using="Type"] Theorem p5m_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B rsv : Z),
  free_prem5 regs m h3 off16 G avail freed W secret sz B rsv ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B rsv FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 HIMG GIMG AG8 Rrsv Mrsv Mend5 A6 A7 A8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B; 0; rsv] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_p5m regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = rsv) by exact (u_wa_small _ (rng64 _ _ _ Rrsv eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (ZTAB3 : zeval E TAB3 = 2 * SCW W).
  { cbn [zeval edenot TAB3 e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). change (5 mod 64) with 5.
    apply TB1_SCW. lia. }
  assert (ZSLOTK : zeval E SLOTK = 16 * sz * Z.land h3 31).
  { change (zeval E SLOTK) with (zeval E (EMd M_MUL (ELit 16) e_sz) * zeval E (EAlu ALU_AND e_h3 (ELit 31))).
    rewrite ZIDX. cbn [zeval edenot e_sz]. rewrite Z39. reflexivity. }
  assert (ZENDB : zeval E ENDB = 16 * sz + (B + 16 * sz * Z.land h3 31)).
  { change (zeval E ENDB) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + zeval E SLOTK)).
    rewrite ZSLOTK. cbn [zeval edenot e_sz e_B]. rewrite Z39, Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (ZENDR5 : zeval E ENDR5 = 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv))).
  { change (zeval E ENDR5) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + (zeval E SLOTK + (-1) * zeval E (EExt false 0 4 e_rsv)))).
    rewrite ZSLOTK. cbn [zeval edenot e_sz e_B e_rsv]. rewrite Z39, Z40, Z42.
    rewrite (mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ext4_zero, (Z.mod_small rsv) by (clear - Rrsv; lia). reflexivity. }
  assert (HK : know_ok SEGS E m kn_p5m).
  { unfold know_ok, kn_p5m.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZTAB3, ?ZENDB, ?ZENDR5.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B e_rsv STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: right; clear - D1; lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_pm5))).
  { cbn [RES_pm5 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl).
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    all: rewrite ?ext4_zero, ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(Z.mod_small rsv (2^32)) by (clear - Rrsv; lia).
    - clear - A5 Rsz Roff L31h Rrsv. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite !Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite Z.mod_small by (clear - Rrsv; lia). apply Z.ltb_lt. clear - Rrsv; lia.
    - apply negb_true_iff, Z.eqb_neq. exact A7.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - apply Z.ltb_ge. exact A8.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_pm5 0x511d0 sr_p5m kn_p5m 43 _ _ _ E m rom regs RES_pm5_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_pm5 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_pm5 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End P5M.
End AXF_p5mz.

Module AXF_pd4.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition ML := EAlu ALU_SRL e_W (ELit 12).
Definition MSTR := EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (ELit (-16)).
Definition IDX := EAlu ALU_AND e_h3 (ELit 31).
Definition ENDMR := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX))).
Definition ENDM := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_pd4 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_pd4 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 0 159;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange TAB1 0 126;
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA TAB1 98984) 2 e_sz;
    KWord (SA ENDMR (-4)) 1 (ELit 0);
    KRange ENDMR 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDMR (-4)) (ELit 1);
    KWord (SA ENDM (-4)) 1 (ELit 0);
    KRange ENDM 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDM (-4)) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_pd4 : scripts := SCR [true; true; true; false; true; false; true; false; true] [] [].
Definition ss_pd4 := SS 0x511d0 sr_pd4 [] kn_pd4 42.
Definition RUN_pd4 := sym_exec SEGS 300 true [0x516d0] scr_pd4 ss_pd4 [].

Definition scr_qd4 : scripts := SCR [true; true; true; false; true; false; true; false; true] [] [].
Definition RES_qd4 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_qd4 ss_pd4 [].
Lemma RES_qd4_ok : sym_exec SEGS 300 true [0x516d0] scr_qd4 (SS 0x511d0 sr_pd4 [] kn_pd4 42) [] = RES_qd4.
Proof. vm_compute. reflexivity. Qed.
End AXF_pd4.

Module AXF_pd4z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pd4.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record free_prd (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B : Z) : Prop := {
  fd_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fd_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fd_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fd_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fd_RB : 1 <= B <= 2^63-1 ;
  fd_AB : B mod 16 = 0 ;
  fd_Roff : 0 <= off16 <= 65535 ;
  fd_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fd_Rh3 : 0 <= h3 <= 159 ;
  fd_RG : 1 <= G <= 2^63-1 ;
  fd_Rav : 0 <= avail <= 2^32 - 1 ;
  fd_Rfr : 0 <= freed <= 2^32 - 1 ;
  fd_RW : 4096 <= W <= 2^64 - 1 ;
  fd_Rsz : 1 <= sz <= 8191 ;
  fd_Rsec : 0 <= secret <= 2^64 - 1 ;
  fd_REND : 4 <= B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) <= 2^63-1 ;
  fd_RENDR : 4 <= B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) <= 2^63-1 ;
  fd_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fd_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fd_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fd_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fd_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fd_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fd_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fd_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fd_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fd_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd_Mtab : rdn SEGS m (wa (2 * SCW W + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  fd_Mend : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd_Mendr : rdn SEGS m (wa (B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fd_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fd_D1 : B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D2 : B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fd_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fd_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fd_A1 : Z.land h3 31 <= Z.land W 31 ;
  fd_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fd_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fd_A4 : sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ;
  fd_A5 : Z.shiftr h3 5 <= -16 * off16 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -20 ;
  fd_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fd_A7 : Z.land W 31 = 0 ;
  fd_A8 : SCW W <= 47 ;
  fd_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fd_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fd_AG : G mod 8 = 0
}.

Section PD4.
Context {fx : FPState}.

#[using="Type"] Theorem pd4_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B : Z),
  free_prd regs m h3 off16 G avail freed W secret sz B ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 A6 A7 A8 HIMG GIMG AG8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_pd4 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (S5h : 0 <= Z.shiftr h3 5 <= 4) by (clear - Rh3; apply shiftr5_bound; lia).
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (ZML : zeval E ML = Z.shiftr W 12).
  { cbn [zeval edenot ML e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). reflexivity. }
  assert (ZMSTR : zeval E MSTR = 4096 * Z.shiftr W 12 - 16).
  { change (zeval E MSTR) with (zeval E (ELit 4096) * zeval E ML + zeval E (ELit (-16))). rewrite ZML. cbn [zeval edenot]. ring. }
  assert (ZENDM : zeval E ENDM = B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)).
  { change (zeval E ENDM) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (ZENDMR : zeval E ENDMR = B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31))).
  { change (zeval E ENDMR) with (zeval E e_B + ((-1) * zeval E (EAlu ALU_SRL e_h3 (ELit 5)) + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31))))).
    rewrite ZML, ZMSTR, ZIDX, ZRC. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (HK : know_ok SEGS E m kn_pd4).
  { unfold know_ok, kn_pd4.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZENDM, ?ZENDMR.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: fail. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_qd4))).
  { cbn [RES_qd4 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl), ?(mod64_of_range _ _ _ S5h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    - assert (I0 : Z.land h3 31 = 0) by (clear - A1 A7 L31h; lia). rewrite I0.
      clear - A5 RML Roff I0 S5h. rewrite I0 in A5. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite A7. reflexivity.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - apply Z.ltb_ge. exact A8.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_qd4 0x511d0 sr_pd4 kn_pd4 42 _ _ _ E m rom regs RES_qd4_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_qd4 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_qd4 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End PD4.
End AXF_pd4z.

Module AXF_pe4.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition ML := EAlu ALU_SRL e_W (ELit 12).
Definition MSTR := EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (ELit (-16)).
Definition IDX := EAlu ALU_AND e_h3 (ELit 31).
Definition ENDMR := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX))).
Definition ENDM := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_pe4 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_pe4 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 0 159;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA ENDMR (-4)) 1 (ELit 0);
    KRange ENDMR 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDMR (-4)) (ELit 1);
    KWord (SA ENDM (-4)) 1 (ELit 0);
    KRange ENDM 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDM (-4)) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_pe4 : scripts := SCR [true; true; true; true; true; true; false; true] [] [].
Definition ss_pe4 := SS 0x511d0 sr_pe4 [] kn_pe4 42.
Definition RUN_pe4 := sym_exec SEGS 300 true [0x516d0] scr_pe4 ss_pe4 [].

Definition scr_qe4 : scripts := SCR [true; true; true; true; true; true; false; true] [] [].
Definition RES_qe4 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_qe4 ss_pe4 [].
Lemma RES_qe4_ok : sym_exec SEGS 300 true [0x516d0] scr_qe4 (SS 0x511d0 sr_pe4 [] kn_pe4 42) [] = RES_qe4.
Proof. vm_compute. reflexivity. Qed.
End AXF_pe4.

Module AXF_pe4z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe4.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record free_pre_e (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B : Z) : Prop := {
  fe_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fe_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fe_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fe_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fe_RB : 1 <= B <= 2^63-1 ;
  fe_AB : B mod 16 = 0 ;
  fe_Roff : 0 <= off16 <= 65535 ;
  fe_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fe_Rh3 : 0 <= h3 <= 159 ;
  fe_RG : 1 <= G <= 2^63-1 ;
  fe_Rav : 0 <= avail <= 2^32 - 1 ;
  fe_Rfr : 0 <= freed <= 2^32 - 1 ;
  fe_RW : 4096 <= W <= 2^64 - 1 ;
  fe_Rsz : 1 <= sz <= 8191 ;
  fe_Rsec : 0 <= secret <= 2^64 - 1 ;
  fe_REND : 4 <= B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) <= 2^63-1 ;
  fe_RENDR : 4 <= B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) <= 2^63-1 ;
  fe_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fe_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fe_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fe_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fe_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fe_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fe_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fe_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fe_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fe_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe_Mend : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe_Mendr : rdn SEGS m (wa (B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fe_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fe_D1 : B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D2 : B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fe_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fe_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fe_A1 : Z.land h3 31 <= Z.land W 31 ;
  fe_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fe_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fe_A5 : Z.shiftr h3 5 <= -16 * off16 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -20 ;
  fe_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fe_A7 : Z.land W 31 = 0 ;
  fe_A8 : SCW W = 63 ;
  fe_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fe_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fe_AG : G mod 8 = 0
}.

Section PE4.
Context {fx : FPState}.

#[using="Type"] Theorem pe4_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B : Z),
  free_pre_e regs m h3 off16 G avail freed W secret sz B ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A5 A6 A7 A8 HIMG GIMG AG8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_pe4 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (S5h : 0 <= Z.shiftr h3 5 <= 4) by (clear - Rh3; apply shiftr5_bound; lia).
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (ZML : zeval E ML = Z.shiftr W 12).
  { cbn [zeval edenot ML e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). reflexivity. }
  assert (ZMSTR : zeval E MSTR = 4096 * Z.shiftr W 12 - 16).
  { change (zeval E MSTR) with (zeval E (ELit 4096) * zeval E ML + zeval E (ELit (-16))). rewrite ZML. cbn [zeval edenot]. ring. }
  assert (ZENDM : zeval E ENDM = B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)).
  { change (zeval E ENDM) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (ZENDMR : zeval E ENDMR = B + (-1 * Z.shiftr h3 5 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31))).
  { change (zeval E ENDMR) with (zeval E e_B + ((-1) * zeval E (EAlu ALU_SRL e_h3 (ELit 5)) + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31))))).
    rewrite ZML, ZMSTR, ZIDX, ZRC. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (HK : know_ok SEGS E m kn_pe4).
  { unfold know_ok, kn_pe4.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZENDM, ?ZENDMR.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: fail. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_qe4))).
  { cbn [RES_qe4 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl), ?(mod64_of_range _ _ _ S5h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    - assert (I0 : Z.land h3 31 = 0) by (clear - A1 A7 L31h; lia). rewrite I0.
      clear - A5 RML Roff I0 S5h. rewrite I0 in A5. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite A7. reflexivity.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite A8. reflexivity.
    - rewrite A8. reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_qe4 0x511d0 sr_pe4 kn_pe4 42 _ _ _ E m rom regs RES_qe4_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_qe4 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_qe4 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End PE4.
End AXF_pe4z.

Module AXF_pe5.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_h3 := EVar 32.
Definition e_off16 := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_W := EVar 37.
Definition e_secret := EVar 38.
Definition e_sz := EVar 39.
Definition e_B := EVar 40.
Definition e_canary := EVar 41.
Definition e_rsv := EVar 42.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_off16) e_B.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_G (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58)).
Definition TAB3 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition ML := EAlu ALU_SRL e_W (ELit 12).
Definition MSTR := EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (ELit (-16)).
Definition IDX := EAlu ALU_AND e_h3 (ELit 31).
Definition ENDM := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EMd M_MUL MSTR IDX)).
Definition ENDMR5 := EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit 4096) ML) (EAlu ALU_ADD (EMd M_MUL MSTR IDX) (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition STK := SA (EVar 2) (-1024).
Definition ENDR5 := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD SLOTK (EMd M_MUL (ELit (-1)) (EExt false 0 4 e_rsv)))).
Definition sr_pe5 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_pe5 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_B 1 (2^63-1);
    KAlign e_B 16;
    KRange e_off16 0 65535;
    KRange PB 1 (2^63-1);
    KRange e_h3 160 191;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_W 4096 (2^64-1);
    KRange e_sz 1 8191;
    KWord (SA PB 12) 1 (ELit 0);
    KWord (SA PB 13) 1 e_h3;
    KWord (SA PB 14) 2 e_off16;
    KWord (SA e_B 0) 8 e_G;
    KWord (SA e_G 16) 8 e_B;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA AREA 0) 8 e_secret;
    KWord (SA (ELit 0) 0x95ed8) 8 e_secret;
    KWord (SA ENDM (-4)) 1 (ELit 0);
    KWord (SA ENDM (-8)) 4 e_rsv;
    KWord (SA ENDM (-9)) 1 (ELit 0);
    KRange ENDM 9 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDM (-9)) (ELit 6);
    KWord (SA ENDMR5 (-4)) 1 (ELit 0);
    KRange ENDMR5 4 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDMR5 (-4)) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_pe5 : scripts := SCR [true; true; true; true; true; true; false; true; true] [] [].
Definition ss_pe5 := SS 0x511d0 sr_pe5 [] kn_pe5 43.
Definition RUN_pe5 := sym_exec SEGS 300 true [0x516d0] scr_pe5 ss_pe5 [].

Definition scr_qe5 : scripts := SCR [true; true; true; true; true; true; false; true; true] [] [].
Definition RES_qe5 := Eval vm_compute in sym_exec SEGS 300 true [0x516d0] scr_qe5 ss_pe5 [].
Lemma RES_qe5_ok : sym_exec SEGS 300 true [0x516d0] scr_qe5 (SS 0x511d0 sr_pe5 [] kn_pe5 43) [] = RES_qe5.
Proof. vm_compute. reflexivity. Qed.
End AXF_pe5.

Module AXF_pe5z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ AXF_ff3 AXF_p4z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record free_pre_e5 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B rsv : Z) : Prop := {
  fe5_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fe5_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fe5_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fe5_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fe5_RB : 1 <= B <= 2^63-1 ;
  fe5_AB : B mod 16 = 0 ;
  fe5_Roff : 0 <= off16 <= 65535 ;
  fe5_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fe5_Rh3 : 160 <= h3 <= 191 ;
  fe5_RG : 1 <= G <= 2^63-1 ;
  fe5_Rav : 0 <= avail <= 2^32 - 1 ;
  fe5_Rfr : 0 <= freed <= 2^32 - 1 ;
  fe5_RW : 4096 <= W <= 2^64 - 1 ;
  fe5_Rsz : 1 <= sz <= 8191 ;
  fe5_Rsec : 0 <= secret <= 2^64 - 1 ;
  fe5_REND : 9 <= B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) <= 2^63-1 ;
  fe5_RENDR : 4 <= B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) <= 2^63-1 ;
  fe5_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe5_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fe5_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fe5_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fe5_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fe5_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fe5_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fe5_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fe5_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fe5_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fe5_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe5_Mend : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe5_Mendr : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe5_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fe5_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fe5_D1 : B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -9 + 6 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D2 : B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fe5_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fe5_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fe5_A1 : Z.land h3 31 <= Z.land W 31 ;
  fe5_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fe5_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fe5_A5 : rsv <= -16 * off16 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -20 ;
  fe5_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fe5_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fe5_AG : G mod 8 = 0 ;
  fe5_Rrsv : 5 <= rsv <= 2^32 - 1 ;
  fe5_Mrsv : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -8)) 4 = Some (word_to_le_bytes 4 (wa rsv)) ;
  fe5_Mend5 : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -9)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fe5_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fe5_A7 : Z.land W 31 = 0 ;
  fe5_A8 : SCW W = 63
}.

Section PE5.
Context {fx : FPState}.

#[using="Type"] Theorem pe5_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B rsv : Z),
  free_pre_e5 regs m h3 off16 G avail freed W secret sz B rsv ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B rsv FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A5 HIMG GIMG AG8 Rrsv Mrsv Mend5 A6 A7 A8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B; 0; rsv] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_pe5 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = rsv) by exact (u_wa_small _ (rng64 _ _ _ Rrsv eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (ZML : zeval E ML = Z.shiftr W 12).
  { cbn [zeval edenot ML e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). reflexivity. }
  assert (ZMSTR : zeval E MSTR = 4096 * Z.shiftr W 12 - 16).
  { change (zeval E MSTR) with (zeval E (ELit 4096) * zeval E ML + zeval E (ELit (-16))). rewrite ZML. cbn [zeval edenot]. ring. }
  assert (ZENDM : zeval E ENDM = B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)).
  { change (zeval E ENDM) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (ZENDMR5 : zeval E ENDMR5 = B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv))).
  { change (zeval E ENDMR5) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + (zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)) + (-1) * zeval E (EExt false 0 4 e_rsv)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B e_rsv]. rewrite Z40, Z42.
    rewrite (mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ext4_zero, (Z.mod_small rsv) by (clear - Rrsv; lia). reflexivity. }
  assert (HK : know_ok SEGS E m kn_pe5).
  { unfold know_ok, kn_pe5.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZENDM, ?ZENDMR5.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B e_rsv STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: right; clear - D1; lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_qe5))).
  { cbn [RES_qe5 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl).
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    all: rewrite ?ext4_zero, ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(Z.mod_small rsv (2^32)) by (clear - Rrsv; lia).
    - assert (I0 : Z.land h3 31 = 0) by (clear - A1 A7 L31h; lia). rewrite I0.
      clear - A5 RML Roff I0 Rrsv. rewrite I0 in A5. rewrite !Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite Z.mod_small by (clear - Rrsv; lia). apply Z.ltb_lt. clear - Rrsv; lia.
    - rewrite A7. reflexivity.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite A8. reflexivity.
    - rewrite A8. reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_qe5 0x511d0 sr_pe5 kn_pe5 43 _ _ _ E m rom regs RES_qe5_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_qe5 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_qe5 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End PE5.
End AXF_pe5z.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Record free_prd5 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B rsv : Z) : Prop := {
  fd5_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fd5_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fd5_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fd5_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fd5_RB : 1 <= B <= 2^63-1 ;
  fd5_AB : B mod 16 = 0 ;
  fd5_Roff : 0 <= off16 <= 65535 ;
  fd5_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fd5_Rh3 : 160 <= h3 <= 191 ;
  fd5_RG : 1 <= G <= 2^63-1 ;
  fd5_Rav : 0 <= avail <= 2^32 - 1 ;
  fd5_Rfr : 0 <= freed <= 2^32 - 1 ;
  fd5_RW : 4096 <= W <= 2^64 - 1 ;
  fd5_Rsz : 1 <= sz <= 8191 ;
  fd5_Rsec : 0 <= secret <= 2^64 - 1 ;
  fd5_REND : 9 <= B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) <= 2^63-1 ;
  fd5_RENDR : 4 <= B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) <= 2^63-1 ;
  fd5_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd5_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fd5_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fd5_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fd5_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fd5_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fd5_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fd5_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fd5_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fd5_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fd5_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd5_Mtab : rdn SEGS m (wa (2 * SCW W + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  fd5_Mend : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd5_Mendr : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd5_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fd5_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fd5_D1 : B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -9 + 6 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D2 : B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv)) + -4 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fd5_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fd5_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fd5_A1 : Z.land h3 31 <= Z.land W 31 ;
  fd5_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fd5_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fd5_A4 : sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ;
  fd5_A5 : rsv <= -16 * off16 + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -20 ;
  fd5_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fd5_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fd5_AG : G mod 8 = 0 ;
  fd5_Rrsv : 5 <= rsv <= 2^32 - 1 ;
  fd5_Mrsv : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -8)) 4 = Some (word_to_le_bytes 4 (wa rsv)) ;
  fd5_Mend5 : rdn SEGS m (wa (B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31) + -9)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fd5_A6 : off16 <= 256 * Z.shiftr W 12 - 1 ;
  fd5_A7 : Z.land W 31 = 0 ;
  fd5_A8 : SCW W <= 47
}.

Section PD5.
Context {fx : FPState}.

#[using="Type"] Theorem pd5_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B rsv : Z),
  free_prd5 regs m h3 off16 G avail freed W secret sz B rsv ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B rsv FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 HIMG GIMG AG8 Rrsv Mrsv Mend5 A6 A7 A8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B; 0; rsv] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_pd5 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB e_off16 e_B]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (mod64_of_range off16 _ _ Roff eq_refl eq_refl), (mod64_of_range B _ _ RB eq_refl eq_refl). ring. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = off16) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = secret) by exact (u_wa_small _ (rng64 _ _ _ Rsec eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = B) by exact (u_wa_small _ (rng64 _ _ _ RB eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = rsv) by exact (u_wa_small _ (rng64 _ _ _ Rrsv eq_refl)).
  assert (L31h : 0 <= Z.land h3 31 <= 31) by (clear - Rh3; pose proof (land31_bound h3 ltac:(lia)); lia).
  assert (ZIDX : zeval E (EAlu ALU_AND e_h3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL e_h3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot e_h3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB e_off16 e_B]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA e_G]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; lia).
  assert (ZTAB1 : zeval E TAB1 = 2 * SCW W).
  { cbn [zeval edenot TAB1 e_W]. rewrite Z37. change (58 mod 64) with 58. reflexivity. }
  assert (RML : 1 <= Z.shiftr W 12 <= 2^52) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (ZML : zeval E ML = Z.shiftr W 12).
  { cbn [zeval edenot ML e_W]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl). reflexivity. }
  assert (ZMSTR : zeval E MSTR = 4096 * Z.shiftr W 12 - 16).
  { change (zeval E MSTR) with (zeval E (ELit 4096) * zeval E ML + zeval E (ELit (-16))). rewrite ZML. cbn [zeval edenot]. ring. }
  assert (ZENDM : zeval E ENDM = B + (4096 * Z.shiftr W 12 + (4096 * Z.shiftr W 12 - 16) * Z.land h3 31)).
  { change (zeval E ENDM) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B]. rewrite Z40. reflexivity. }
  assert (RTAB : 0 <= 2 * SCW W <= 126) by (clear - RSC; lia).
  assert (RA : 0 <= 4096 * (G / 4096) <= 2^63-1).
  { clear - RG. pose proof (Z.mul_div_le G 4096 ltac:(lia)). pose proof (Z.mod_pos_bound G 4096 ltac:(lia)).
    pose proof (Z.div_mod G 4096 ltac:(lia)). lia. }
  assert (RSK : 0 <= 1024 <= spz) by (clear - Rsp; lia).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (L31h32 : 0 <= Z.land h3 31 < 32) by (clear - L31h; lia).
  assert (ZENDMR5 : zeval E ENDMR5 = B + (4096 * Z.shiftr W 12 + ((4096 * Z.shiftr W 12 - 16) * Z.land h3 31 + -1 * rsv))).
  { change (zeval E ENDMR5) with (zeval E e_B + (zeval E (ELit 4096) * zeval E ML + (zeval E MSTR * zeval E (EAlu ALU_AND e_h3 (ELit 31)) + (-1) * zeval E (EExt false 0 4 e_rsv)))).
    rewrite ZML, ZMSTR, ZIDX. cbn [zeval edenot e_B e_rsv]. rewrite Z40, Z42.
    rewrite (mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ext4_zero, (Z.mod_small rsv) by (clear - Rrsv; lia). reflexivity. }
  assert (HK : know_ok SEGS E m kn_pd5).
  { unfold know_ok, kn_pd5.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZENDM, ?ZENDMR5.
    all: cbn [zeval edenot e_h3 e_off16 e_G e_avail e_freed e_W e_secret e_sz e_B e_rsv STK a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply Wmeta]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite (mod64_of_range _ _ _ Rsp eq_refl eq_refl); assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RPB eq_refl eq_refl), ?(mod64_of_range _ _ _ REND eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RENDR eq_refl eq_refl), ?(mod64_of_range _ _ _ RB eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(mod64_of_range _ _ _ RTAB eq_refl eq_refl); assumption).
    all: right; clear - D1; lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_qd5))).
  { cbn [RES_qd5 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z42.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl).
    all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
    all: rewrite ?(mod64_of_range _ _ _ RSC eq_refl eq_refl), ?(mod64_of_range _ _ _ RML eq_refl eq_refl).
    all: rewrite ?ext4_zero, ?(mod64_of_range _ _ _ Rrsv eq_refl eq_refl), ?(Z.mod_small rsv (2^32)) by (clear - Rrsv; lia).
    - assert (I0 : Z.land h3 31 = 0) by (clear - A1 A7 L31h; lia). rewrite I0.
      clear - A5 RML Roff I0 Rrsv. rewrite I0 in A5. rewrite !Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite Z.mod_small by (clear - Rrsv; lia). apply Z.ltb_lt. clear - Rrsv; lia.
    - rewrite A7. reflexivity.
    - clear - A6 RML Roff. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - apply Z.ltb_ge. exact A8.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_qd5 0x511d0 sr_pd5 kn_pd5 43 _ _ _ E m rom regs RES_qd5_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_qd5 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_qd5 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End PD5.
