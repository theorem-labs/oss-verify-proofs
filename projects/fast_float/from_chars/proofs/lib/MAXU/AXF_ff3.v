(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition eH3 := EVar 32. Definition eOff := EVar 33. Definition eG := EVar 34.
Definition eAv := EVar 35. Definition eFr := EVar 36. Definition eW := EVar 37. Definition eSec := EVar 38.
Definition eSz := EVar 39. Definition eB := EVar 40.
Definition PB := EAlu ALU_ADD (EMd M_MUL (ELit 16) eOff) eB.
Definition sr_ff3 := sr_upd sr_id 10 (EAlu ALU_ADD PB (ELit 16)).
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL eG (ELit 12)).
Definition TAB1 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) eW) (ELit 58)).
Definition TAB2 := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EAlu ALU_SRL eW (ELit 5)) (ELit 1)).
Definition SLOTK := EMd M_MUL (EMd M_MUL (ELit 16) eSz) (EAlu ALU_AND eH3 (ELit 31)).
Definition ENDB := EAlu ALU_ADD (EMd M_MUL (ELit 16) eSz) (EAlu ALU_ADD eB SLOTK).
Definition ENDRB := EAlu ALU_ADD (EMd M_MUL (ELit 16) eSz) (EAlu ALU_ADD eB (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL eH3 (ELit 5))) SLOTK)).
Definition STK := SA (EVar 2) (-1024).
Definition kn_ff3 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47); KAlign (EVar 2) 16; KWr STK (ELit 1024);
    KRange eB 1 (2^63-1); KAlign eB 16; KRange eOff 0 65535; KRange PB 1 (2^63-1);
    KRange eH3 0 159; KRange eG 1 (2^63-1);
    KRange eAv 0 (2^32-1); KRange eFr 0 (2^32-1); KRange eW 0 3071; KRange eSz 1 8191;
    KWord (SA PB 12) 1 (ELit 0); KWord (SA PB 13) 1 eH3; KWord (SA PB 14) 2 eOff;
    KWord (SA eB 0) 8 eG;
    KWord (SA eG 16) 8 eB; KWord (SA eG 24) 4 eAv; KWord (SA eG 28) 4 eFr; KWord (SA eG 32) 8 eW;
    KWord (SA AREA 0) 8 eSec; KWord (SA (ELit 0) 0x97c98) 8 eSec; KWord (SA (ELit 0) 0x97c23) 1 (ELit 0);
    KWord (SA TAB1 98984) 2 eSz; KWord (SA TAB2 98984) 2 eSz;
    KWord (SA ENDB 12) 1 (ELit 0); KWord (SA ENDRB 12) 1 (ELit 0); KRange ENDB 1 (2^63-1); KRange ENDRB 1 (2^63-1);
    KWr (SA PB 12) (ELit 4); KWr (SA eG 24) (ELit 8);
    KDisj STK (ELit 1024) (SA ENDB 12) (ELit 1); KDisj STK (ELit 1024) (SA ENDRB 12) (ELit 1);
    KDisj STK (ELit 1024) (SA PB 12) (ELit 4);
    KDisj STK (ELit 1024) (SA eB 0) (ELit 8);
    KDisj STK (ELit 1024) (SA eG 0) (ELit 40);
    KDisj STK (ELit 1024) (SA AREA 0) (ELit 8);
    KDisj (SA eG 0) (ELit 40) (SA PB 12) (ELit 4);
    KDisj (SA (ELit 0) 0x97c23) (ELit 1) (SA PB 12) (ELit 4)
  ].
Definition scr_ff3 : scripts := SCR [true; true; true; true; false; true; true; false; false] [] [].

(* [comment removed for export] *)
Definition RES_ff3 := Eval vm_compute in sym_exec SEGS 300 true [] scr_ff3 (SS 0x533ac sr_ff3 [] kn_ff3 41) [].
Lemma RES_ff3_ok : sym_exec SEGS 300 true [] scr_ff3 (SS 0x533ac sr_ff3 [] kn_ff3 41) [] = RES_ff3.
Proof. vm_compute. reflexivity. Qed.

Section FF.
Context {fx : FPState}.

Definition callee_same (R regs : bvmap 5 word) : Prop :=
  forall n, In n [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat ->
    getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n)).

Definition ff3_mem (m : word -> option byte) (regs : bvmap 5 word) (p G fnew : Z) : word -> option byte :=
  let sp := getr regs 2 in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (v_addi sp (-8)) (word_to_le_bytes 8 (getr regs 1)))
    (v_addi sp (-16)) (word_to_le_bytes 8 (getr regs 8)))
    (v_addi sp (-24)) (word_to_le_bytes 8 (getr regs 9)))
    (v_addi sp (-32)) (word_to_le_bytes 8 (getr regs 18)))
    (v_addi sp (-40)) (word_to_le_bytes 8 (getr regs 19)))
    (wa (p - 3)) (word_to_le_bytes 1 (wa 255)))
    (wa (p - 2)) (word_to_le_bytes 2 (wa 0)))
    (wa (G + 28)) (word_to_le_bytes 4 (wa fnew)).

#[using="Type"] Theorem ff3_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte)
    (h3 off16 G avail freed W secret sz B : Z),
  let spz := bv_unsigned (getr regs 2) in
  getr regs 10 = wa (16 * off16 + B + 16) ->
  2^20 <= spz <= 2^47 -> spz mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  1 <= B <= 2^63-1 -> B mod 16 = 0 -> 0 <= off16 <= 65535 -> 1 <= 16 * off16 + B <= 2^63-1 ->
  0 <= h3 <= 159 -> 1 <= G <= 2^63-1 ->
  0 <= avail <= 2^32 - 1 -> 0 <= freed <= 2^32 - 1 -> 0 <= W <= 3071 -> 1 <= sz <= 8191 -> 0 <= secret <= 2^64 - 1 ->
  1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ->
  1 <= 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) <= 2^63-1 ->
  rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ->
  rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ->
  rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ->
  rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ->
  rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ->
  rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ->
  rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ->
  rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ->
  rdn SEGS m (wa (0 + 621720)) 8 = Some (word_to_le_bytes 8 (wa secret)) ->
  rdn SEGS m (wa (0 + 621603)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  rdn SEGS m (wa (2 * Z.shiftr W 6 + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ->
  rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  rdn SEGS m (wa (16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ->
  16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= spz + -1024 ->
  16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12 + 1 <= spz + -1024 ->
  16 * off16 + B + 12 + 4 <= spz + -1024 ->
  B + 0 + 8 <= spz + -1024 ->
  G + 0 + 40 <= spz + -1024 ->
  4096 * (G / 4096) + 0 + 8 <= spz + -1024 ->
  (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ->
  (0 + 621603 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 621603) ->
  (* [comment removed for export] *)
  Z.land h3 31 <= Z.land W 31 ->
  Z.testbit avail (Z.land h3 31) = false -> Z.testbit freed (Z.land h3 31) = false ->
  sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ->
  Z.shiftr h3 5 <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ->
  freed <> 0 ->
  Z.lor avail freed + 2 ^ Z.land h3 31 <> 2 ^ (Z.land W 31 + 1) - 1 ->
  exists R, msteps SEGS (mkst regs (wa 0x533ac) m rom)
                        (mkst R (wa 0x53574) (ff3_mem m regs (16 * off16 + B + 16) G (freed + 2 ^ Z.land h3 31)) rom)
         /\ callee_same R regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom h3 off16 G avail freed W secret sz B spz.
  intros HP Rsp Asp HSTK RB AB Roff RPB Rh3 RG Rav Rfr RW Rsz Rsec REND RENDR
         Mh4 Mh3 Moff Mmeta Mmem Mav Mfr MW Marea Mctx Mnl Mtab Mend Mendr Whdr Wmeta
         D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 A4 A5 F1 F2.
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [h3; off16; G; avail; freed; W; secret; sz; B] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_ff3 regs).
  { apply (regs_ok_pin E sr_id regs 10). { apply regs_ok_id. } rewrite HP, zeval_sound. f_equal.
    cbn [zeval edenot PB eOff eB]. change (bv_unsigned (ev E 33)) with (bv_unsigned (wa off16)).
    change (bv_unsigned (ev E 40)) with (bv_unsigned (wa B)). rewrite !u_wa.
    rewrite (Z.mod_small off16 (2^64)), (Z.mod_small B (2^64)) by lia. ring. }
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
  assert (ZIDX : zeval E (EAlu ALU_AND eH3 (ELit 31)) = Z.land h3 31).
  { cbn [zeval edenot eH3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZRC : zeval E (EAlu ALU_SRL eH3 (ELit 5)) = Z.shiftr h3 5).
  { cbn [zeval edenot eH3]. rewrite Z32, (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl). reflexivity. }
  assert (ZPB : zeval E PB = 16 * off16 + B) by (cbn [zeval edenot PB eOff eB]; rewrite Z33, Z40; reflexivity).
  assert (ZAREA : zeval E AREA = 4096 * (G / 4096)).
  { cbn [zeval edenot AREA eG]. rewrite Z34, (mod64_of_range G _ _ RG eq_refl eq_refl).
    change (12 mod 64) with 12. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity. }
  assert (ZTAB1 : zeval E TAB1 = 2 * Z.shiftr W 6).
  { cbn [zeval edenot TAB1 eW]. rewrite Z37.
    assert (R52 : 0 <= 4503599627370496 * W <= 4503599627370496 * 3071) by (clear - RW; lia).
    rewrite (mod64_of_range _ _ _ R52 eq_refl eq_refl). change (58 mod 64) with 58. f_equal.
    clear - RW. rewrite !Z.shiftr_div_pow2 by lia. change (2^58) with (4503599627370496 * 64). change (2^6) with 64.
    rewrite <- Z.div_div by lia. rewrite (Z.mul_comm 4503599627370496 W), Z.div_mul by lia. reflexivity. }
  assert (ZTAB2 : zeval E TAB2 = 2 * Z.shiftr W 6).
  { cbn [zeval edenot TAB2 eW]. rewrite Z37, (mod64_of_range W _ _ RW eq_refl eq_refl).
    assert (RW5 : 0 <= Z.shiftr W 5 <= 95).
    { clear - RW. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
    change (5 mod 64) with 5. change (1 mod 64) with 1. rewrite (mod64_of_range _ _ _ RW5 eq_refl eq_refl).
    rewrite Z.shiftr_shiftr by (clear; lia). reflexivity. }
  assert (ZSLOTK : zeval E SLOTK = 16 * sz * Z.land h3 31).
  { change (zeval E SLOTK) with (zeval E (EMd M_MUL (ELit 16) eSz) * zeval E (EAlu ALU_AND eH3 (ELit 31))).
    rewrite ZIDX. cbn [zeval edenot eSz]. rewrite Z39. reflexivity. }
  assert (ZENDB : zeval E ENDB = 16 * sz + (B + 16 * sz * Z.land h3 31)).
  { change (zeval E ENDB) with (zeval E (EMd M_MUL (ELit 16) eSz) + (zeval E eB + zeval E SLOTK)).
    rewrite ZSLOTK. cbn [zeval edenot eSz eB]. rewrite Z39, Z40. reflexivity. }
  assert (ZENDRB : zeval E ENDRB = 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31))).
  { change (zeval E ENDRB) with (zeval E (EMd M_MUL (ELit 16) eSz) + (zeval E eB + ((-1) * zeval E (EAlu ALU_SRL eH3 (ELit 5)) + zeval E SLOTK))).
    rewrite ZSLOTK, ZRC. cbn [zeval edenot eSz eB]. rewrite Z39, Z40. reflexivity. }
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
  assert (HK : know_ok SEGS E m kn_ff3).
  { unfold know_ok, kn_ff3.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | exact HSTK | exact RSK])
               | apply kword_z | apply krange_z | apply kalign_z | apply kdisj_z | apply kwr_z ].
    all: rewrite ?ZPB, ?ZAREA, ?ZTAB1, ?ZTAB2, ?ZENDB, ?ZENDRB.
    all: cbn [zeval edenot eH3 eOff eG eAv eFr eW eSec eSz eB STK a_base a_off].
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
  idtac "RUN".
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_ff3))).
  { cbn [RES_ff3 fst snd].
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
    - rewrite (all_cond_z avail freed (Z.land h3 31) W Rav32 Rfr32 L31h RW0 A2 A3). apply Z.eqb_neq. exact F2.
    - rewrite ext4_swrap, sx32_zero. apply Z.eqb_neq. rewrite (Z.mod_small freed _ Rfr32). exact F1.
    - rewrite !ext4_swrap, (mask2_bit_clear avail freed (Z.land h3 31) Rav32 Rfr32 L31h A2 A3). reflexivity.
    - clear - A5 Rsz Roff L31h S5h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
    - clear - A4 Rsz Roff L31h. assert (0 <= sz * Z.land h3 31 <= 8191 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
      rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
    - rewrite !ext4_swrap, (mask_bit_clear freed (Z.land h3 31) Rfr32 L31h A3). reflexivity.
    - rewrite !ext4_swrap, (mask_bit_clear avail (Z.land h3 31) Rav32 L31h A2). reflexivity.
    - apply negb_true_iff, Z.ltb_ge. exact A1. }
  destruct (run_sound SEGS 300 [] scr_ff3 0x533ac sr_ff3 kn_ff3 41 _ _ _ E m rom regs RES_ff3_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  idtac "POST".
  exists R. split.
  - cbn [RES_ff3 fst snd s_pc s_log s_regs] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) =>
      replace (ff3_mem m regs (16 * off16 + B + 16) G (freed + 2 ^ Z.land h3 31)) with M; [exact Hms|] end.
    clear Hms HR'.
    cbn [mem_denot s_log]. unfold ff3_mem.

    apply f_equal3; [ apply f_equal3; [ apply f_equal3; [ reflexivity | | ] | | ] | | ].
    + rewrite adenot_z. cbn [zeval edenot PB eOff eB]. rewrite Z33, Z40. f_equal. ring.
    + change (edenot E (ELit 18446744073709551615)) with (wa 18446744073709551615). apply le_wa_eqm; [reflexivity | apply Nat.leb_le; reflexivity].
    + rewrite adenot_z. cbn [zeval edenot PB eOff eB]. rewrite Z33, Z40. f_equal. ring.
    + reflexivity.
    + rewrite adenot_z. cbn [zeval edenot eG]. rewrite Z34. reflexivity.
    + rewrite zeval_sound. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. cbn [zeval edenot]. rewrite ?Z32, ?Z36.
      rewrite (mod64_of_range h3 _ _ Rh3 eq_refl eq_refl), (mod64_of_range _ _ _ Rfr eq_refl eq_refl).
      litmods. rewrite (Z.mod_small (Z.land h3 31) 32 L31h32). rewrite ext4_swrap.
      change (8 * Z.of_nat 4) with 32. rewrite swrap32_mod. rewrite Zplus_mod, swrap32_mod, swrap32_mod, <- Zplus_mod.
      rewrite Z.shiftl_1_l. reflexivity.
  - cbn [RES_ff3 fst snd s_regs] in HR'. clear Hms. intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End FF.
