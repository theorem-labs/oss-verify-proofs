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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngFree AXF_ff3.

Module AXF_p4.
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
Definition TAB2 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EAlu ALU_SRL e_W (ELit 5)) (ELit 1)).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_AND e_h3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_sz) (EAlu ALU_ADD e_B (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL e_h3 (ELit 5))) SLOTK)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_p4 := (sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16))).
Definition kn_p4 : list kentry :=
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
    KWord (SA ENDRB 12) 1 (ELit 0);
    KRange ENDB 1 (2^63-1);
    KRange ENDRB 1 (2^63-1);
    KDisj STK (ELit 1024) (SA ENDB 12) (ELit 1);
    KDisj STK (ELit 1024) (SA ENDRB 12) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA e_B 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8) ].
Definition scr_p4 : scripts := SCR [true; true; true; true; false; true] [] [].
Definition ss_p4 := SS 0x511d0 sr_p4 [] kn_p4 42.
Definition RUN_p4 := sym_exec SEGS 300 true [0x516d0] scr_p4 ss_p4 [].

Definition RES_p4 := Eval vm_compute in RUN_p4.
Lemma RES_p4_ok : sym_exec SEGS 300 true [0x516d0] scr_p4 (SS 0x511d0 sr_p4 [] kn_p4 42) [] = RES_p4.
Proof. vm_compute. reflexivity. Qed.
End AXF_p4.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z.AXF_p4.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section P4.
Context {fx : FPState}.

Definition p4_mem (m : word -> option byte) (regs : bvmap 5 word) : word -> option byte :=
  let sp := getr regs 2 in
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (v_addi sp (-8)) (word_to_le_bytes 8 (getr regs 1)))
    (v_addi sp (-16)) (word_to_le_bytes 8 (getr regs 8)))
    (v_addi sp (-24)) (word_to_le_bytes 8 (getr regs 9)))
    (v_addi sp (-32)) (word_to_le_bytes 8 (getr regs 18)))
    (v_addi sp (-40)) (word_to_le_bytes 8 (getr regs 19)).

Definition pro_regs (R regs : bvmap 5 word) (G W idx p : Z) : Prop :=
  getr R 8 = wa idx /\ getr R 9 = wa p /\ getr R 10 = wa G /\ getr R 11 = wa W /\
  getr R 2 = v_addi (getr regs 2) (-48) /\
  (forall n, In n [3;4;18;19;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).

#[using="Type"] Theorem p4_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B : Z),
  free_pre regs m h3 off16 G avail freed W secret sz B ->
  exists R, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R (wa 0x516d0) (p4_mem m regs) rom)
         /\ pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B FP.
  destruct FP as [HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 HIMG GIMG AG8].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_p4 regs).
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
  assert (ZENDRB : zeval E ENDRB = 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31))).
  { change (zeval E ENDRB) with (zeval E (EMd M_MUL (ELit 16) e_sz) + (zeval E e_B + ((-1) * zeval E (EAlu ALU_SRL e_h3 (ELit 5)) + zeval E SLOTK))).
    rewrite ZSLOTK, ZRC. cbn [zeval edenot e_sz e_B]. rewrite Z39, Z40. reflexivity. }
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
  assert (HK : know_ok SEGS E m kn_p4).
  { unfold know_ok, kn_p4.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZTAB2, ?ZENDB, ?ZENDRB.
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
                 ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl); assumption).
    all: fail. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_p4))).
  { cbn [RES_p4 fst snd].
    assert (L31W : 0 <= Z.land W 31 <= 31) by (clear - RW; pose proof (land31_bound W ltac:(lia)); lia).
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range W _ _ RW eq_refl eq_refl),
                 ?(mod64_of_range off16 _ _ Roff eq_refl eq_refl), ?(mod64_of_range sz _ _ Rsz eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small (Z.land h3 31) 32 L31h32), ?(mod64_of_range _ _ _ L31h eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ L31W eq_refl eq_refl), ?(mod64_of_range _ _ _ S5h eq_refl eq_refl).
    - clear - A5 Rsz Roff L31h S5h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [0x516d0] scr_p4 0x511d0 sr_p4 kn_p4 42 _ _ _ E m rom regs RES_p4_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_p4 fst snd s_pc s_log s_regs] in Hms. exact Hms.
  - cbn [RES_p4 fst snd s_regs] in HR'. clear Hms. unfold pro_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; rewrite zeval_sound; change (EVar 32) with e_h3; rewrite ZIDX; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; cbn [zeval edenot]; rewrite Z33, Z40; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End P4.
