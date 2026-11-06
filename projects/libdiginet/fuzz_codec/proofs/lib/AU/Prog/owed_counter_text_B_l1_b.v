(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v, with its module paths and module names changed; 20 of its 45 lines of code are new or changed and 686 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/owed_counter_text_B_l1.v; 379 of its 418 lines of code are new or changed and 6 lines of the source are left out. *)
(* Part b of one pass of owed_counter_text's first loop in image B (owed_counter_text_B_l1_base.v): the call of
   owed_seg7 (0x84a54) through its contract cdcU_owed_seg7_specX, then from its return address 0x84634: a1 := the
   pattern v, a0 := -11; bltz a1 (a character owed_seg7 does not draw) or beq s3,8 (a ninth digit) to 0x84840
   (E_RANGE); else the check of t[i] again (through s9), the UBSan checks of n (0x84654, 0x8465c), dot[n] := (t[i] is
   '.') (0x84660 .. 0x84680), the UBSan check of s[n] (0x84688), s[n] := v and n := n + 1 (0x8468c .. 0x846a4), s6, s4
   one on and the UBSan check of s6, back to the loop head 0x845d4. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_inv owed_counter_text_B_s0_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_s0 owed_counter_text_B_l1_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_e owed_counter_text_B_l1_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac csv := unfold acallee_saved; vm_compute; repeat (first [ left; reflexivity | right ]); split; discriminate.
(* bltz on owed_seg7's pattern: -1 or a byte below 128 *)
Lemma ocb_blt0 : forall E k v, ew E k = Z_to_bv 64 v -> -1 <= v < 128 ->
  branch_taken BC_LT (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E k v Hk Hv. rewrite YO0c.branch_lt. rewrite sv_denot_SOff0, Hk. cbn [sv_denot].
rewrite Z_to_bv_unsigned, unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec v 0).
- assert (v = -1) as -> by lia. reflexivity.
- rewrite Z.mod_small by lia. rewrite !YO0b.s64_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma ocb_U_sll2 : forall E k n, ew E k = Z_to_bv 64 n -> 0 <= n <= 8 ->
  U E (SAlu ALU_SLL (SOff k 0) (SLit 2)) = 4 * n.
Proof.
intros E k n Hk Hn. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E k n Hk) by lia.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* seqz of ch - 46 *)
Lemma ocb_den_seqz : forall E ch, ew E 35 = Z_to_bv 64 ch -> 0 <= ch < 256 ->
  sv_denot E (SAlu ALU_SLTU (SOff 35 (-46)) (SLit 1)) = Z_to_bv 64 (if ch =? 46 then 1 else 0).
Proof.
intros E ch H Hch. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, H, unsigned_lit_small by lia.
change (zcanon 1) with 1.
destruct (Z.eq_dec ch 46) as [-> | Hne].
- reflexivity.
- rewrite (proj2 (Z.eqb_neq ch 46) Hne).
  assert (Hz : zcanon (ch + -46) <> 0).
  { unfold zcanon, M64. destruct (Z_lt_le_dec ch 46).
    - replace (ch + -46) with ((ch + 2 ^ 64 - 46) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
      rewrite Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  assert (Hz0 : 0 <= zcanon (ch + -46)) by (unfold zcanon, M64; apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec (zcanon (ch + -46)) 1); [lia|]. reflexivity.
Qed.
Ltac hE33b := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hE33b_in Hb := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
(* the write windows of the run: dot[n] (atom 33) and s[n] (atom 34), inside the walk's own frame *)
Ltac awr_b :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | ewpeel; first [hE33b | hE34]; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 1; eexists;
      split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; hEfa; change (fs_frame_bytes 1) with 128; hFa; lia
    | ] ].
Ltac kwr_b :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
            first [ exfalso; lia | first [hE33b_in Hb | hE34_in Hb]; rewrite unsigned_lit_small in Hb by lia; lia ] | ]);
  destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SEG7 : cdcU_owed_seg7_specX tfibsegs B MT RLO RHI GLYPHA ROSTRS B_OSEG7.

Theorem oc_part_b_holds : oc_part_b B MT RLO RHI GLYPHA ROSTRS.
Proof.
unfold oc_part_b. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & n & ch & s & dot & Rra & R10 & R19 & R20 & R22 & R25 & Hi & Hfuel & Hch & Hch0 & Hnz & Hct1 & Hnd &
  Hl1 & Harr & Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ocl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & _).
pose proof Hpre as ((HJc & _ & _ & Hgp & Htp & _ & _ & _ & Hev & Hlive) & _ & (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Hqam & Hqcw)) &
  _ & _ & _ & Lsj & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & _ & _ & Himg).
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
assert (Hil : i < og_len g) by (unfold og_len; exact (ocl_tb_len (og_tb g) i Hi Hin0 Hnz)).
unfold og_len in Hil, Hqn, Hqam.
assert (Hch8 : 0 <= ch < 256).
{ pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & _) & _). rewrite <- Hch.
  exact (proj2 (Htb (Z.to_nat i) ltac:(lia))). }
assert (Hc8 : 0 <= oc_c ch < 256) by (unfold oc_c; destruct (ch =? 46); lia).
unfold TB_owed_counter_text, ESTACK in Hceil, Hwin, H46.
assert (Esp1 : spZ regs2 = og_sp1 g) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the call *)
eapply SRr_bind.
{ apply (SEG7 (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) regs2 (oc_c ch)).
  - apply (cpw_entry B _ _ _ _ _ _ _ _ _ (og_lyc g) (og_Sc g)); [exact HJ | | | | | | | | exact Hev | exact HP | exact Hlive].
    + rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite Rra. vm_compute. discriminate.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Esp1. pose proof (Z.div_mod (og_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D.
      rewrite D. replace (32 * (og_sp1 g / 32)) with ((2 * (og_sp1 g / 32)) * 16) by lia. apply Z_mod_mult.
    + rewrite Esp1. unfold TB_owed_seg7. lia.
    + rewrite Esp1. lia.
  - exact R10.
  - lia.
  - rewrite Esp1. exact Himg. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPm3 & HIO3 & HMLE3 & HK3 & Rv).
rewrite Esp1 in HK3. unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
fold (oc_v ch) in Rv.
(* what the walk carries across the call *)
assert (HPR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r)
  by (intros r Hr; exact (ocl_pres regs2 regs3 r HP3 Hr)).
assert (HR3 : oc_kregs regs3 regs2) by (unfold oc_kregs; repeat split; apply HPR; csv).
destruct (ocl_keep_call B LAWS g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3 Hpre HJ HP HC HK3 HR3)
  as (HC3 & KF3 & Ksj3 & Kdj3).
assert (HK3' : tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W3 mem3 (og_sp g) (oc_wr g)).
{ apply (cw_kept_cj B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W3 mem3 TB_owed_counter_text TB_owed_seg7
    (og_sp g) (og_sp1 g) (oc_wr g) cno_wr HJc HJ); [rewrite Hfr; intros x Hx; right; exact Hx | exact HP
  | unfold TB_owed_counter_text, ESTACK; lia | lia | unfold TB_owed_counter_text, TB_owed_seg7, ESTACK; lia | lia
  | intros a [] | exact HK | exact HK3]. }
destruct (cw_frame_step MT MTL B (og_lyc g) (og_Sc g) ly2 S2 ly3 S3 HP Hmo HPm3 HMLE3) as (HP3' & Hmo3).
pose proof (same_io_trans _ _ _ Hio HIO3) as Hio3.
destruct (ocl_frame B LAWS g pos ly3 S3 W3 mem3 md3 Hpre HJ3) as (Hfr3 & Efa3 & _ & _ & _ & _ & _ & HFp3).
assert (Harr3 : oc_arrays g pos W3 mem3 n s dot)
  by (apply (ocl_arrays_kept g pos W2 W3 mem2 mem3 n s dot); [exact KF3 | lia | exact Harr]).
pose proof (Ksj3 Hsj) as Hsj3. pose proof (Kdj3 Hdj) as Hdj3.
pose proof (Hnow pos ly3 S3 W3 mem3 md3 HJ3 HK3' HP3' Hni) as ((Htb3 & Htra3) & _).
pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & V56 & _ & _ & Hsh3).
clear HJ HK HP Hio Hmo HC Harr Hsj Hdj KF3 Ksj3 Kdj3 HK3 HPm3 HMLE3 HIO3 Himg.
(* the state at 0x84634 *)
set (F := og_F g pos) in *.
assert (HFa : frame_addr (og_lyc g) 1 pos = F) by reflexivity.
assert (HF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
pose proof alloc_ceiling_val as Hac.
assert (Hq47 : og_q g + Z.of_nat (length (og_tb g)) <= 2 ^ 47 - 1)
  by (unfold amem_range in Hqam; rewrite ?C3, ?C4, ?C5 in Hqam; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
pose proof (Htb3 (Z.to_nat i) ltac:(lia)) as (Vch & _). rewrite Hch, Z2Nat.id in Vch by lia.
set (xs := [F + 64 + 4 * n; F + 32 + n; ch; onot (F + 32)]).
remember (Ereg regs3 (cw_extra xs)) as E eqn:HEE.
assert (EW : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; exact (ew_Ereg_nat regs3 _ k r Hk)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (F + 64 + 4 * n)) by (subst E; exact (cw_ew_x regs3 xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (F + 32 + n)) by (subst E; exact (cw_ew_x regs3 xs 1)).
assert (E35 : ew E 35 = Z_to_bv 64 ch) by (subst E; exact (cw_ew_x regs3 xs 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (onot (F + 32))) by (subst E; exact (cw_ew_x regs3 xs 3)).
assert (E10 : ew E 10 = w64 (oc_v ch)) by (rewrite (EW 10%nat 10%bv eq_refl); exact Rv).
assert (E19 : ew E 19 = w64 n) by (rewrite (EW 19%nat 19%bv eq_refl), HPR by csv; exact R19).
assert (E20 : ew E 20 = w64 (og_q g + i)) by (rewrite (EW 20%nat 20%bv eq_refl), HPR by csv; exact R20).
assert (E22 : ew E 22 = w64 (og_q g + i - 1)) by (rewrite (EW 22%nat 22%bv eq_refl), HPR by csv; exact R22).
assert (E21 : ew E 21 = w64 (F + 64)) by (rewrite (EW 21%nat 21%bv eq_refl), HPR by csv; exact R21).
assert (E18 : ew E 18 = w64 (F + 32)) by (rewrite (EW 18%nat 18%bv eq_refl), HPR by csv; exact R18).
assert (E27 : ew E 27 = w64 (onot (F + 64))) by (rewrite (EW 27%nat 27%bv eq_refl), HPR by csv; exact R27).
assert (E9 : ew E 9 = w64 (og_sp1 g)) by (rewrite (EW 9%nat 9%bv eq_refl), HPR by csv; exact R9).
assert (U9 : bv_unsigned (ew E 9) = og_sp1 g) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = og_q g + i - 1) by (rewrite E22; unfold w64; apply unsigned_lit_small; lia).
assert (Hqw : og_q g + Z.of_nat (length (og_tb g)) <= og_sp g - 4320 \/ og_sp g <= og_q g)
  by (unfold coff_win, TB_owed_counter_text, ESTACK in Hqcw; exact Hqcw).
assert (YS : st_ok tfibsegs E
  (mkSS PC_RET7 sr_atoms
     [YP09.mkRegion (Some 22%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 35 0))];
      YP09.mkRegion (Some 9%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 36 0))]] None
     (mkFacts [(32%nat, mkAF SB SB 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 0 8 0);
               (20%nat, mkAF 1 (2 ^ 47 - 2) 0); (22%nat, mkAF 0 (2 ^ 47 - 3) 0); (33%nat, mkAF 0 (2 ^ 47 - 8) 0);
               (34%nat, mkAF 0 (2 ^ 47 - 2) 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0)] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 PC_RET7) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (og_q g + i - 1) 1 1 (SOff 35 0) ch);
      [rewrite sv_denot_SOff0; exact E35 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      replace (og_q g + i - 1 + 1) with (og_q g + i) by lia. exact Vch.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 56 8 (SOff 36 0) (onot (F + 32)));
      [rewrite sv_denot_SOff0; exact E36 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold onot; lia | cbn; lia | exact V56].
  - apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U22. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U9, E19, E20, E22, E33, E34, E35, E36. unfold w64. rewrite !unsigned_lit_small by (unfold SB, onot; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, onot. repeat split; first [exact I | exact Hsp1a | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (23%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, HPR, R23 by csv; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (24%bv : bv 5) (SLit 46) HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite HPR, R24 by csv; reflexivity)) as YS.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in YS.
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (25%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 32 0)) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite HPR, R25 by csv; unfold w64;
        apply (oc_den_sh E 20 (og_q g + i)); [exact E20 | exact E32 | lia])) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1] E (mrestrict (w_H W3) mem3)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W3 mem3 E 20 (og_q g + i) 1); [| | lia | lia | lia | exact E20 | exact E32].
  - eapply range_addressable_sub; [exact Htra3 | lia | unfold og_len; lia].
  - pose proof Hqam as Ham. unfold amem_range in Ham |- *. rewrite ?C3, ?C4, ?C5 in Ham |- *.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham |- *. lia. }
assert (R23' : getr regs3 23 = w64 SB) by (rewrite HPR by csv; exact R23).
assert (R24' : getr regs3 24 = w64 46) by (rewrite HPR by csv; exact R24).
rename HJ3 into HJ. cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros; assumption).
assert (Hvr : oc_v ch = -1 \/ 0 <= oc_v ch < 128) by (unfold oc_v; apply owed_seg7_range).
rewrite Rra. change (w64 PC_RET7) with (Z_to_bv 64 PC_RET7).
assert (Hskip : skipn (Z.to_nat i) (og_tb g) = ch :: skipn (S (Z.to_nat i)) (og_tb g))
  by (rewrite <- Hch; apply skipn_cons_nth; unfold og_len in Hil; lia).
pose proof (ocl_ct1_digit ch (skipn (S (Z.to_nat i)) (og_tb g)) n s dot Hch0 Hnd) as Hdig.
rewrite <- Hskip, Hct1 in Hdig.
cw_run_to awr_ro PC_X. ctk_keep kwr_ro.
(* bltz a1 (0x8463c): the pattern *)
cw_branch Hb1.
all: rewrite (ocb_blt0 _ 10 (oc_v ch)) in Hb1 by (first [ewpeel; exact E10 | lia]).
- (* v < 0: E_RANGE *)
  apply Z.ltb_lt in Hb1.
  assert (Hspec : owed_counter_text_spec (og_tb g) = (E_RANGE, [], 0))
    by (unfold owed_counter_text_spec; rewrite Hdig, (proj2 (Z.ltb_lt _ _) Hb1); reflexivity).
  cw_run_to awr_ro PC_X. ctk_keep kwr_ro.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (ocl_cut_close B MT LAWS g pos PC_X (P_X g) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3' Hni Hio3 Hmo3 HC3 HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj3 | exact Hdj3 | ] end.
  intros Ksj Kdj.
  unfold P_X, oc_res. rewrite Hspec.
  split; [rv0; apply bv_eq; reflexivity|].
  split; [intros Hr; exfalso; unfold E_RANGE in Hr; lia|].
  intros _. exists (og_sj g), (og_dj g). split; [exact Ksj|]. split; [exact Lsj | exact Kdj].
- (* v >= 0: beq s3,a2 (0x84644), a ninth digit *)
  apply Z.ltb_ge in Hb1.
  cw_run_to awr_ro PC_X. ctk_keep kwr_ro.
  cw_branch Hb2.
  all: rewrite branch_eq_U, (U_atom _ 19 n) in Hb2 by (first [ewpeel; exact E19 | lia]); rewrite U_lit in Hb2 by lia.
  + apply Z.eqb_eq in Hb2.
    assert (Hspec : owed_counter_text_spec (og_tb g) = (E_RANGE, [], 0))
      by (unfold owed_counter_text_spec; rewrite Hdig; replace (n =? 8) with true by (symmetry; apply Z.eqb_eq; exact Hb2);
          rewrite orb_true_r; reflexivity).
    cw_run_to awr_ro PC_X. ctk_keep kwr_ro.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos PC_X (P_X g) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3' Hni Hio3 Hmo3 HC3 HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj3 | exact Hdj3 | ] end.
    intros Ksj Kdj.
    unfold P_X, oc_res. rewrite Hspec.
    split; [rv0; apply bv_eq; reflexivity|].
    split; [intros Hr; exfalso; unfold E_RANGE in Hr; lia|].
    intros _. exists (og_sj g), (og_dj g). split; [exact Ksj|]. split; [exact Lsj | exact Kdj].
  + apply Z.eqb_neq in Hb2.
    lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
      pose proof (YP03.st_ok_add_fact tfibsegs Ex ssx msx 19 (mkAF 0 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E19; unfold w64;
              rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as YS end.
    clear HS. rename YS into HS. norm_ss HS.
    cw_run_to awr_ro 0x84664. ctk_keep kwr_ro.
    (* bltu s11,a0 (0x8465c): ~(F + 64) against 4 n *)
    cw_branch Hb3.
    all: rewrite branch_ltu_U, (U_atom _ 27 (onot (F + 64))), (ocb_U_sll2 _ 19 n) in Hb3
           by (first [ewpeel; first [exact E27 | exact E19] | unfold onot; lia | lia]).
    * exfalso. apply Z.ltb_lt in Hb3. unfold onot in Hb3. lia.
    * cw_run_to awr_ro 0x84664. ctk_keep kwr_ro.
      (* a0 = F + 64 + 4 n, the address of dot[n]: atom 33 *)
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 33 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E33; symmetry;
                apply (cw_den_dot_r Ev 21 19 (F + 64) n); [ewpeel; exact E21 | ewpeel; exact E19 | lia | lia])) as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsh4 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msv)) (SB + F / 8) OC_FRAME_SHADOW)
          by (apply (ocl_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem msv)); [|exact Hsh3];
              intros x Hx; apply KE; [unfold SB in *; cbn [length OC_FRAME_SHADOW] in Hx; lia | tauto]);
        assert (SHOK2 : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1; mkSHE 33 0 4] Ev (mrestrict (w_H W3) (ms_mem msv)))
          by (unfold sh_ok in SHOK |- *; apply Forall_cons; [exact (Forall_inv SHOK)|];
              apply Forall_cons; [|apply Forall_nil];
              apply (cw_shent_ra W3 (ms_mem msv) Ev 33 (F + 64 + 4 * n) 4);
              [ replace (F + 64 + 4 * n) with (F + (64 + 4 * n)) by lia;
                apply ocl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsh4]
              | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite ?C3, ?C4, ?C5 in *;
                unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
              | lia | lia | lia | ewpeel; exact E33 | ewpeel; exact E32 ]);
        clear SHOK; rename SHOK2 into SHOK end.
      (* the check of dot[n], the byte t[i] again: stop at 0x84678 *)
      cw_run_to awr_ro 0x84678. ctk_keep kwr_ro.
      (* drop the text byte's region; dot[n]'s region (atom 33, written next) *)
      lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
        pose proof (st_ok_submem tfibsegs Ex ssx msx
          [YP09.mkRegion (Some 9%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 36 0))]] HS
          ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hd_ok : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem msv)) (YP09.mkRegion (Some 33%nat) 0 4 0 4 []))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E33, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|];
              split; [intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp3; lia | apply Forall_nil]);
        assert (Hd_dj : all_disjoint Ev (YP09.mkRegion (Some 33%nat) 0 4 0 4 []) (ss_mem ssv))
          by (cbn [ss_mem all_disjoint]; unfold extent_disjoint;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; ewpeel; rewrite E33, U9, !unsigned_lit_small by lia;
              split; [lia | exact I]);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W3) msv) (YP09.mkRegion (Some 33%nat) 0 4 0 4 [])
          HS eq_refl Hd_ok Hd_dj) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 64 + 4 * n <= a < F + 68 + 4 * n) ->
          aview tfibsegs (w_H W3) (ms_mem msv) a = aview tfibsegs (w_H W3) mem3 a)
          by (intros a Ha _; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_b 0x84690. ctk_keep kwr_b.
      (* a0 = F + 32 + n, the address of s[n]: atom 34, its region, its shadow entry *)
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 34 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E34; symmetry;
                replace (F + 32 + n) with (n + (F + 32)) by lia;
                apply (cw_den_add_r Ev 19 18 n (F + 32)); [ewpeel; exact E19 | ewpeel; exact E18 | lia | lia | lia])) as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsh5 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msv)) (SB + F / 8) OC_FRAME_SHADOW)
          by (apply (ocl_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem msv)); [|exact Hsh3];
              intros x Hx; pose proof HFapp as Happ; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ;
              apply KE; [unfold SB in *; cbn [length OC_FRAME_SHADOW] in Hx; lia
              | unfold SB in *; cbn [length OC_FRAME_SHADOW] in Hx; lia]);
        assert (Hs_ok : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem msv)) (YP09.mkRegion (Some 34%nat) 0 1 0 1 []))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E34, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|];
              split; [intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp3; lia | apply Forall_nil]);
        assert (Hs_dj : all_disjoint Ev (YP09.mkRegion (Some 34%nat) 0 1 0 1 []) (ss_mem ssv))
          by (cbn [ss_mem all_disjoint]; unfold extent_disjoint;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; ewpeel; rewrite ?E33, ?E34, ?U9, !unsigned_lit_small by lia;
              repeat split; lia);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W3) msv) (YP09.mkRegion (Some 34%nat) 0 1 0 1 [])
          HS eq_refl Hs_ok Hs_dj) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        assert (SHOK2 : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1; mkSHE 33 0 4; mkSHE 34 0 1] Ev (mrestrict (w_H W3) (ms_mem msv)))
          by (unfold sh_ok in SHOK |- *; apply Forall_app with (l1 := [mkSHE 20 0 1; mkSHE 33 0 4]) (l2 := [mkSHE 34 0 1]);
              split; [exact SHOK|]; apply Forall_cons; [|apply Forall_nil];
              apply (cw_shent_ra W3 (ms_mem msv) Ev 34 (F + 32 + n) 1);
              [ replace (F + 32 + n) with (F + (32 + n)) by lia;
                apply ocl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | left; lia | exact Hsh5]
              | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite ?C3, ?C4, ?C5 in *;
                unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
              | lia | lia | lia | ewpeel; exact E34 | ewpeel; exact E32 ]);
        clear SHOK; rename SHOK2 into SHOK;
        assert (KE' : forall a, 0 <= a < 2 ^ 64 ->
          ~ (F + 64 + 4 * n <= a < F + 68 + 4 * n \/ F + 32 + n <= a < F + 33 + n) ->
          aview tfibsegs (w_H W3) (ms_mem msv) a = aview tfibsegs (w_H W3) mem3 a)
          by (intros a Ha Hz; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_b PC_L1. ctk_keep kwr_b.
      set (bd := if ch =? 46 then 1 else 0).
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        let i33 := oc_ridx HS 33%nat in let i34 := oc_ridx HS 34%nat in
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W3) msv) i33 _ HS eq_refl) as HR33;
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W3) msv) i34 _ HS eq_refl) as HR34 end.
      cbn [ms_mem restrict] in HR33, HR34.
      lazymatch type of HR33 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR33 end.
      lazymatch type of HR34 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR34 end.
      pose proof (field_of_region _ _ 34 (F + 32 + n) _ _ _ _ _ 0 1%N (SOff 10 0) (oc_v ch) HR34
        ltac:(ewpeel; rewrite E34; apply unsigned_lit_small; lia) ltac:(oc_in)
        ltac:(rewrite sv_denot_SOff0; ewpeel; exact E10) ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Vs.
      pose proof (field_of_region _ _ 33 (F + 64 + 4 * n) _ _ _ _ _ 0 4%N (SAlu ALU_SLTU (SOff 35 (-46)) (SLit 1)) bd HR33
        ltac:(ewpeel; rewrite E33; apply unsigned_lit_small; lia) ltac:(oc_in)
        ltac:(apply ocb_den_seqz; [ewpeel; exact E35 | lia]) ltac:(unfold bd; destruct (ch =? 46); cbn; lia) ltac:(cbn; lia)) as Vd.
      rewrite Z.add_0_r in Vs, Vd. change (N.to_nat 1) with 1%nat in Vs. change (N.to_nat 4) with 4%nat in Vd.
      assert (Hct1' : ct1_owe (skipn (Z.to_nat (i + 1)) (og_tb g)) (n + 1) (s ++ [oc_v ch]) (upd_at dot n bd) =
                      ct1_owe (og_tb g) 0 [] (repeat 0 8)).
      { rewrite Hdig, (proj2 (Z.ltb_ge _ _) Hb1), (proj2 (Z.eqb_neq _ _) Hb2).
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. }
      apply SRr_ret. cbv beta. left.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (ocl_cut_close B MT LAWS g pos PC_L1 (P_L1 g pos fuel) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3' Hni Hio3 Hmo3 HC3 HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
        | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold oc_zv; lia] | exact KP | exact Hsj3 | exact Hdj3 | ] end.
      intros Ksj Kdj.
      exists (i + 1), (n + 1), (s ++ [oc_v ch]), (upd_at dot n bd).
      split; [reg_off E19 n 1|]. split; [reg_off E20 (og_q g + i) 1|]. split; [reg_off E22 (og_q g + i - 1) 1|].
      split; [lia|]. split; [unfold og_len in *; lia|].
      split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia;
              rewrite (ocl_firstn_S (og_tb g) (Z.to_nat i)) by lia; apply Forall_app; split;
              [exact Hnz | constructor; [rewrite Hch; exact Hch0 | constructor]]|].
      split; [exact Hct1'|].
      split; [split; [exact (ct_inv_next n dot bd (conj Hn0 (conj Hdl Hdz)) ltac:(lia))|];
              split; [apply ocl_Forall_upd_at; [exact Hd01 | unfold bd; destruct (ch =? 46); lia]|];
              split; [rewrite length_app, Hsl; cbn [length]; lia|];
              apply Forall_app; split; [exact Hs128 | constructor; [lia | constructor]]|].
      split; [|split; [exact Ksj | exact Kdj]].
      apply (ocl_arrays_next g pos W3 mem3 _ n s dot (oc_v ch) bd ltac:(lia) Hsl Hdl);
        [ intros a Ha Hne Hnd'; apply KE; [lia | intros [Hz | Hz]; lia] | exact Vs | exact Vd | exact Harr3 ].
Qed.
End d.
