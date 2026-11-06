(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 294 of its 321 lines of code are new or changed and 42 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_P2 : Z := 0xcc.
Definition RBN_P3 : Z := 0x1f4.
Definition RBN_P4 : Z := 0x304.
Definition RBN_P5 : Z := 0x370.
Definition RBN_P6 : Z := 0x4b8.
Definition RBN_P7 : Z := 0x56c.
Definition RBN_P8 : Z := 0x650.
Definition RBN_P9 : Z := 0x7a4.
Definition RBN_P10 : Z := 0x8f8.
Definition rbn_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition rbn_sh (w4 nb tb db : bool) : list Z :=
  [241; 241; 241; 241] ++ [if w4 then 5 else 248] ++ [242; 242; 242] ++ repeat (if nb then 0 else 248) 3 ++
  [242; 242; 242; 242; 242] ++ repeat (if tb then 0 else 248) 3 ++ [242; 242; 242; 242; 242] ++
  repeat (if db then 0 else 248) 6 ++ repeat 243 6 ++ repeat 0 28.
Definition rbm_ovf (cap : Z) (l : list Z) : Z := if cap <? Z.of_nat (length l) then 1 else 0.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Record rbn_in : Type := RbnIn {
  ri_fq : YK11.FPState; ri_STK : Z; ri_sp0 : Z; ri_FP : list (Z * Z); ri_ly : alayout; ri_S : astate;
  ri_W0 : world SEGS; ri_mem0 : word -> option byte; ri_md0 : Model; ri_own : list (Z * Z);
  ri_lyc : alayout; ri_Sc : astate; ri_W : world SEGS; ri_memc : word -> option byte; ri_mdc : Model; ri_k : Z;
  ri_regs : bvmap 5 word; ri_ch : list (Z * Z * Z);
  ri_f : Z; ri_said : Z; ri_i : Z; ri_o : Z; ri_name : Z; ri_name_len : Z; ri_token : Z; ri_token_len : Z;
  ri_display : Z; ri_display_len : Z; ri_sd : list Z }.
Definition rbn_SP (X : rbn_in) : Z := spZ (ri_regs X).
Definition rbn_A (X : rbn_in) : Z := 32 * ((rbn_SP X - 288) / 32).
Definition rbn_F (X : rbn_in) (pos : Z) : Z := frame_addr (ri_lyc X) 3 pos.
Definition rbn_FL (X : rbn_in) (pos : Z) : Z := flag_addr (ri_lyc X) 3 pos.
Definition rbn_SH (X : rbn_in) (pos : Z) : Z := shadow_addr (rbn_F X pos).
Definition rbm_stem (X : rbn_in) : list Z := bn_stem (ri_f X) (ri_sd X).
Definition rbm_w4 (X : rbn_in) : list Z := bn_w4 (ri_i X) (ri_o X).
Definition rbm_NM (X : rbn_in) : list Z := bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X).
Definition rbm_NB (X : rbn_in) : list Z := firstn 23 (rbm_NM X).
Definition rbm_TB (X : rbn_in) : list Z := firstn 23 (bn_TK (rbm_NB X)).
Definition rbm_tok (X : rbn_in) : Z := 1 - rbm_ovf 23 (bn_TK (rbm_NB X)).
Definition rbm_D9 (X : rbn_in) : list Z :=
  rbm_NB X ++ [32; 40] ++ bn_dec (ri_i X) 1 ++ [32; 105; 110; 32; 47; 32] ++ bn_dec (ri_o X) 1.
Definition rbm_acc (X : rbn_in) : bool :=
  reac_box_name_c.bn_accept (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X)
    (ri_token_len X) (ri_display X) (ri_display_len X).
Definition rbm_args (X : rbn_in) : Prop :=
  reac_box_name_c.bn_args_ok (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
    (ri_display_len X) (ri_i X) (ri_o X) = true.
Fixpoint rbn_cells (m : word -> option byte) (l : list (Z * nat * Z)) : Prop :=
  match l with [] => True | (a, n, v) :: t => val_mem SEGS m a n v /\ rbn_cells m t end.
Definition rbn_locs4 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  [(rbn_A X + 8, 8%nat, ri_display X); (rbn_A X + 16, 8%nat, ri_name X); (rbn_A X + 32, 8%nat, ri_token_len X);
   (rbn_A X + 56, 8%nat, ri_display_len X); (rbn_A X + 64, 8%nat, ri_name_len X);
   (rbn_A X + 80, 8%nat, ri_i X); (rbn_A X + 88, 8%nat, ri_o X);
   (rbn_A X + 152, 8%nat, rbn_F X pos + 32); (rbn_A X + 160, 8%nat, 5); (rbn_A X + 168, 8%nat, 4);
   (rbn_A X + 176, 4%nat, 0)].
Definition rbn_locs6 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  rbn_locs4 X pos ++
  [(rbn_A X + 24, 8%nat, ri_token X); (rbn_A X + 48, 8%nat, rbn_F X pos + 128); (rbn_A X + 72, 8%nat, rbn_F X pos)].
Definition rbn_rec2 (X : rbn_in) (pos : Z) (s : list Z) : list (Z * nat * Z) :=
  [(rbn_A X + 120, 8%nat, rbn_F X pos + 192); (rbn_A X + 128, 8%nat, 48);
   (rbn_A X + 136, 8%nat, Z.min (Z.of_nat (length s)) 47); (rbn_A X + 144, 4%nat, rbm_ovf 47 s)].
Definition rbn_shadow_at (W1 : world SEGS) (m : word -> option byte) (q : Z) (l : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W1) m (q + j) = Some (nth (Z.to_nat j) l 0).
Section h.
Variable B : asyms.
Definition rbn_cx (X : rbn_in) : Prop :=
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X) (ri_own X)
    (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) (ri_k X) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (ri_W X)) (ri_memc X)) /\
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI (ri_W X) (ri_memc X) /\
  YK0s.ret_ok (getr (ri_regs X) 1) /\ 4096 <= raZ (ri_regs X) /\
  getr (ri_regs X) 3 = w64 (as_gp B) /\ getr (ri_regs X) 4 = w64 (as_tp B) /\
  achain (ri_lyc X) (aview SEGS (w_H (ri_W X)) (ri_memc X)) (spZ (ri_regs X)) (s0Z (ri_regs X)) (ri_ch X) /\
  spZ (ri_regs X) mod 16 = 0 /\ ri_sp0 X - ri_STK X <= spZ (ri_regs X) - REAC_BOX_NAME_STK /\
  spZ (ri_regs X) + 16 <= ri_sp0 X /\
  Z.of_nat (length (frames (ri_Sc X))) <= 8 /\
  getr (ri_regs X) 10 = w64 (ri_f X) /\ -2 ^ 31 <= ri_f X < 2 ^ 31 /\
  getr (ri_regs X) 11 = w64 (ri_said X) /\ 0 <= ri_said X < 2 ^ 64 /\
  getr (ri_regs X) 12 = w64 (ri_i X) /\ -2 ^ 31 <= ri_i X < 2 ^ 31 /\
  getr (ri_regs X) 13 = w64 (ri_o X) /\ -2 ^ 31 <= ri_o X < 2 ^ 31 /\
  getr (ri_regs X) 14 = w64 (ri_name X) /\ 0 <= ri_name X < 2 ^ 64 /\
  getr (ri_regs X) 15 = w64 (ri_name_len X) /\ 0 <= ri_name_len X < 2 ^ 64 /\
  getr (ri_regs X) 16 = w64 (ri_token X) /\ 0 <= ri_token X < 2 ^ 64 /\
  getr (ri_regs X) 17 = w64 (ri_token_len X) /\ 0 <= ri_token_len X < 2 ^ 64 /\
  val_mem SEGS (mrestrict (w_H (ri_W X)) (ri_memc X)) (spZ (ri_regs X)) 8 (ri_display X) /\
  0 <= ri_display X < 2 ^ 64 /\
  val_mem SEGS (mrestrict (w_H (ri_W X)) (ri_memc X)) (spZ (ri_regs X) + 8) 8 (ri_display_len X) /\
  0 <= ri_display_len X < 2 ^ 64 /\
  rbn_img (ri_W X) (ri_memc X) /\
  (rbm_args X ->
     rbn_said B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (spZ (ri_regs X)) (ri_sp0 X) (ri_said X) (ri_sd X) /\
     rbn_bufs B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X)
       (ri_memc X) (spZ (ri_regs X)) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
       (ri_display_len X)).
Definition rbn_post (X : rbn_in) : world SEGS -> config -> Prop :=
  treac_box_name_post B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
    (ri_md0 X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_k X) (ri_regs X)
    (ri_f X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
    (ri_display_len X) (ri_sd X).
Definition rbn_kept (X : rbn_in) (W1 : world SEGS) (memc1 : word -> option byte) (Er : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) -> ~ Er a ->
     aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a) /\
  (forall b m j, In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) -> 0 <= j < req_size m -> ~ Er (b + j) ->
     aview SEGS (w_H W1) memc1 (b + j) = aview SEGS (w_H (ri_W X)) (ri_memc X) (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a) /\
  (forall cid pos a, In (cid, pos) (frames (ri_Sc X)) ->
     (in_zr a (frame_rng (ri_lyc X) (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr (ri_lyc X) cid pos), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) ->
     apresent (w_H (ri_W X)) (ri_memc X) a -> apresent (w_H W1) memc1 a) /\
  (forall a, rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X -> apresent (w_H W1) memc1 a).
Definition rbn_frame (X : rbn_in) (m : word -> option byte) : Prop :=
  forall j r, nth_error rbn_saved_regs j = Some r ->
    val_mem SEGS m (rbn_SP X - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (ri_regs X) (Z_to_bv 5 r))).
Definition rbn_mid (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (memc1 : word -> option byte) (mdc1 : Model) (Er : Z -> Prop) (sh : list Z) : Prop :=
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) /\
  frames Sc1 = (3, pos) :: frames (ri_Sc X) /\
  Permutation (ablocks B lyc1 Sc1) (ablocks B (ri_lyc X) (ri_Sc X)) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) memc1) /\
  rbn_kept X W1 memc1 Er /\
  rbn_frame X (mrestrict (w_H W1) memc1) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 504) 8 (rbn_FL X pos) /\
  rbn_shadow_at W1 memc1 (rbn_SH X pos) sh.
Definition rbn_rbase (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = w64 (rbn_A X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (rbn_SP X) /\ getr regs1 9 = w64 (rbn_A X) /\ getr regs1 19 = w64 (rbn_F X pos) /\
  getr regs1 22 = w64 SHADOW_OFF.
Definition rbn_stp (X : rbn_in) (pos : Z) (W1 : world SEGS) (memc1 : word -> option byte) (P : Z) : Prop :=
  rbn_str W1 memc1 P (rbm_stem X) /\
  (forall a, P <= a < P + Z.of_nat (length (rbm_stem X)) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)).
Definition rbn_st2 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (repeat 0 64) /\
  rbn_rbase X pos regs1 /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 (ri_said X) /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 25 = w64 (ri_f X) /\ getr regs1 27 = w64 (ri_token_len X) /\
  getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\
  getr regs1 15 = w64 (ri_name_len X) /\ getr regs1 16 = w64 (ri_display_len X).
Definition rbn_st3 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh false false false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 (ri_said X) /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 25 = w64 (ri_f X) /\ getr regs1 27 = w64 (ri_token_len X) /\
  getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\ getr regs1 14 = w64 (ri_display X) /\
  getr regs1 15 = w64 (ri_name_len X) /\ getr regs1 16 = w64 (ri_display_len X) /\
  rbm_args X.
Definition rbn_st4 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 P /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 25 = w64 (rbn_F X pos + 32) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 0 /\ getr regs1 30 = w64 0 /\
  getr regs1 15 = w64 (hd 0 (rbm_stem X)) /\ getr regs1 13 = w64 (P + 1) /\ getr regs1 10 = w64 (P + 1) /\
  getr regs1 14 = w64 23 /\ getr regs1 12 = w64 4 /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs4 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  rbn_stp X pos W1 memc1 P /\ rbm_args X.
Definition rbn_st5 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 P /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 25 = w64 (rbn_F X pos + 32) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\
  getr regs1 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_stem X)) /\ getr regs1 12 = w64 4 /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs4 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) /\
  rbn_stp X pos W1 memc1 P /\ rbm_args X.
Definition rbn_st6 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 29 = w64 (rbn_F X pos + 128) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  rbm_args X.
Definition rbn_st7 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 29 = w64 (rbn_F X pos + 128) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 (rbm_tok X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X) /\
  rbm_args X.
Definition rbn_st8 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true true) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 25 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 20 = w64 (rbn_F X pos + 192) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 (rbm_tok X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos ++ rbn_rec2 X pos (rbm_NB X)) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 192) (firstn 47 (rbm_NB X)) /\
  rbm_args X.
Definition rbn_st9 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true true) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 25 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 20 = w64 (rbn_F X pos + 192) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 1 /\
  rbn_cells (mrestrict (w_H W1) memc1)
    (rbn_locs6 X pos ++ rbn_rec2 X pos (rbm_D9 X) ++ [(rbn_A X + 40, 8%nat, rbm_tok X)]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 192) (firstn 47 (rbm_D9 X)) /\
  rbm_args X.
Definition rbn_st10 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1
    (rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
       (ri_display X) (ri_display_len X))
    (rbn_sh false false false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 21 = w64 (if rbm_acc X then 0 else -1) /\
  (rbm_acc X = true ->
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_name X) (rbm_NM X ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_token X) (bn_TK (rbm_NM X) ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_display X) (bn_DP (rbm_NM X) (ri_i X) (ri_o X) ++ [0])).
Definition rbn_cfg (X : rbn_in) (off : Z) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model)
  : config :=
  cfg_at (fx := ri_fq X) SEGS (BASE + AF_reac_box_name + off) regs1 memc1 mdc1.
Definition rbn_at2 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P2 regs1 memc1 mdc1 /\ rbn_st2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at3 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P3 regs1 memc1 mdc1 /\ rbn_st3 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at4 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg X RBN_P4 regs1 memc1 mdc1 /\ rbn_st4 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn_at5 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg X RBN_P5 regs1 memc1 mdc1 /\ rbn_st5 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn_at6 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P6 regs1 memc1 mdc1 /\ rbn_st6 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at7 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P7 regs1 memc1 mdc1 /\ rbn_st7 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at8 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P8 regs1 memc1 mdc1 /\ rbn_st8 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at9 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P9 regs1 memc1 mdc1 /\ rbn_st9 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at10 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_P10 regs1 memc1 mdc1 /\ rbn_st10 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_seg1_stmt : Prop :=
  forall X : rbn_in, rbn_cx X ->
  SRr SEGS (ri_W X) (cfg_at (fx := ri_fq X) SEGS (BASE + AF_reac_box_name) (ri_regs X) (ri_memc X) (ri_mdc X))
    (rbn_at2 X).
Definition rbn_seg2_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P2 regs1 memc1 mdc1) (fun W2 c2 => rbn_at3 X W2 c2 \/ rbn_at10 X W2 c2).
Definition rbn_seg3_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st3 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P3 regs1 memc1 mdc1) (rbn_at4 X).
Definition rbn_seg4_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx X -> rbn_st4 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg X RBN_P4 regs1 memc1 mdc1) (rbn_at5 X).
Definition rbn_seg5_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx X -> rbn_st5 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg X RBN_P5 regs1 memc1 mdc1) (rbn_at6 X).
Definition rbn_seg6_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st6 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P6 regs1 memc1 mdc1) (rbn_at7 X).
Definition rbn_seg7_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st7 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P7 regs1 memc1 mdc1) (rbn_at8 X).
Definition rbn_seg8_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st8 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P8 regs1 memc1 mdc1) (rbn_at9 X).
Definition rbn_seg9_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st9 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P9 regs1 memc1 mdc1) (rbn_at10 X).
Definition rbn_seg10_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st10 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P10 regs1 memc1 mdc1) (rbn_post X).
End h.
End f.
End d.
