(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module paths and module names changed; 313 of its 359 lines of code are new or changed and 587 lines of the source are left out. *)
(* check_bytes (fuzz_codec.c:316-344) at image B 0x84d40, 83 instructions, real frame 32, the bcmp wrapper at 0x84da4,
   against lib/AU/Prog/CPgChkU.v's cdcU_check_bytes_specX. a0 = q = &k, the 184-byte call record.
   The image-A walk (lib/A/Prog/check_bytes_A.v) at image B's addresses, with one more step: image B checks that q is
   8-aligned (0x84d54 andi a0,a0,7; 0x84d58 bnez -> the UBSan trap at 0x84e30); the contract's q mod 8 = 0 is atom 10's
   alignment fact (al2 = 3), so the engine takes the not-taken side. Image B also checks each field's shadow before its
   load and orders some compares the other way; the engine's run and the branch rewrites below take either order.
   0x84d40-0x84d50 save ra, s0, s1 and keep q in s0; 0x84d5c-0x84d64 load the shadow offset into s1; the walk then drops
   the .got slot and the cell and adds the record's region (atom 10 = q) with the fields read: out.len (q + 132),
   out.display (q + 133), out.key (q + 136), want_len (q + 168), want_key (q + 176), want_display (q + 180).
   0x84d98 bne want_len,len -> abort, refuted by want_len = out.len; bcmp(q + 108, q + 144, len) through
   cw_bcmp_at, reseat at 0x84da8, bnez a0 -> abort, refuted by the first len bytes agreeing; 0x84ddc bne key,want_key
   and 0x84e10 bne want_display,display -> abort, refuted by the premises; else the return. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkStrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_BYTES : Z := 0x84d40.
Definition B_BCMP : Z := 0x42430.
Definition cb_rec : YP09.region := YP09.mkRegion (Some 10%nat) 0 184 0 0
[YP09.mkChunk 132 (CVal 1 (SOff 33 0)); YP09.mkChunk 133 (CVal 1 (SOff 37 0)); YP09.mkChunk 136 (CVal 4 (SOff 35 0));
 YP09.mkChunk 168 (CVal 8 (SOff 34 0)); YP09.mkChunk 176 (CVal 4 (SOff 36 0)); YP09.mkChunk 180 (CVal 4 (SOff 38 0))].
Definition cb_xs (kc : kcallZ) : list Z :=
[cmd_lenZ (kz_out kc); kz_want_len kc; cmd_keyZ (kz_out kc); kz_want_key kc; cmd_displayZ (kz_out kc);
 kz_want_display kc mod 2 ^ 32].
Definition cb_AF : list (nat * afact) :=
[(10%nat, mkAF 0 (2 ^ 47 - 185) 3); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 (2 ^ 64 - 1) 0);
 (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0); (37%nat, mkAF 0 255 0);
 (38%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition cb_SH : list shent := [mkSHE 10 0 184].
(* `lw` of a 4-byte field s: the sign-extended value *)
Lemma cg_U_sx32 : forall E n s, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if s <? 2 ^ 31 then s else s + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n s Hn Hs. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* two sign-extended 4-byte fields compare as the fields do *)
Lemma cg_U_sx32_eqb2 : forall E n m s t, ew E n = Z_to_bv 64 s -> ew E m = Z_to_bv 64 t ->
0 <= s < 2 ^ 32 -> 0 <= t < 2 ^ 32 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SExt true 32 (SOff m 0))) = (s =? t).
Proof.
intros E n m s t Hn Hm Hs Ht. rewrite (cg_U_sx32 E n s Hn Hs), (cg_U_sx32 E m t Hm Ht).
destruct (Z.eqb_spec s t) as [Hst | Hst].
- subst t. apply Z.eqb_refl.
- apply Z.eqb_neq. destruct (Z.ltb_spec s (2 ^ 31)); destruct (Z.ltb_spec t (2 ^ 31)); lia.
Qed.
(* an int field read modulo 2 ^ 32 *)
Lemma cg_int_mod : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
(v mod 2 ^ 32 = w mod 2 ^ 32 <-> v = w).
Proof.
intros v w Hv Hw. split; [|intros ->; reflexivity]. intros H.
pose proof (Z.div_mod v (2 ^ 32) ltac:(lia)). pose proof (Z.div_mod w (2 ^ 32) ltac:(lia)).
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound w (2 ^ 32) ltac:(lia)). lia.
Qed.

(* four little-endian bytes as the value a 4-byte load reads *)
Lemma cb_le4 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
forall k, (k < 4)%nat -> YO0f.le_byte (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) 4 k = nth k [b0; b1; b2; b3] 0.
Proof.
intros b0 b1 b2 b3 H0 H1 H2 H3 k Hk. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; cbn [nth]; [| | | | lia].
- change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. symmetry.
  apply (Z.mod_unique _ 256 (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))); lia.
- change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite <- (Z.div_unique _ 256 (b1 + 256 * (b2 + 256 * (b3 + 256 * 0))) b0) by lia. symmetry.
  apply (Z.mod_unique _ 256 (b2 + 256 * (b3 + 256 * 0))); lia.
- change (2 ^ (8 * Z.of_nat 2)) with 65536.
  rewrite <- (Z.div_unique _ 65536 (b2 + 256 * (b3 + 256 * 0)) (b0 + 256 * b1)) by lia. symmetry.
  apply (Z.mod_unique _ 256 (b3 + 256 * 0)); lia.
- change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  rewrite <- (Z.div_unique _ 16777216 (b3 + 256 * 0) (b0 + 256 * b1 + 65536 * b2)) by lia. symmetry.
  apply (Z.mod_unique _ 256 0); lia.
Qed.
(* a garr8 of 32 bytes read as the key: bytes 28 .. 31 little-endian (cmd_keyZ) *)
Lemma cb_key_mem : forall (m : word -> option byte) a o, length o = 32%nat -> garr8 tfibsegs m a o ->
val_mem tfibsegs m (a + 28) 4 (cmd_keyZ o).
Proof.
intros m a o Hl Hg k Hk.
assert (Hb : forall j, (j < 32)%nat ->
  mbyte tfibsegs m (a + Z.of_nat j) = Some (Z_to_bv 8 (nth j o 0)) /\ 0 <= nth j o 0 < 256).
{ intros j Hj. destruct (Hg j ltac:(lia)) as [V R]. split; [|exact R].
  specialize (V 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in V. rewrite Z.add_0_r in V. rewrite V.
  f_equal. f_equal. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (Hkey : cmd_keyZ o = nth 28 o 0 + 256 * (nth 29 o 0 + 256 * (nth 30 o 0 + 256 * (nth 31 o 0 + 256 * 0)))).
{ clear - Hl. do 32 (destruct o as [|? o]; [discriminate Hl|]). destruct o; [|discriminate Hl]. reflexivity. }
rewrite Hkey.
destruct (Hb 28%nat ltac:(lia)) as [V0 R0]. destruct (Hb 29%nat ltac:(lia)) as [V1 R1].
destruct (Hb 30%nat ltac:(lia)) as [V2 R2]. destruct (Hb 31%nat ltac:(lia)) as [V3 R3].
rewrite (cb_le4 _ _ _ _ R0 R1 R2 R3 k Hk).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth].
- replace (a + 28 + Z.of_nat 0) with (a + Z.of_nat 28) by lia. exact V0.
- replace (a + 28 + Z.of_nat 1) with (a + Z.of_nat 29) by lia. exact V1.
- replace (a + 28 + Z.of_nat 2) with (a + Z.of_nat 30) by lia. exact V2.
- replace (a + 28 + Z.of_nat 3) with (a + Z.of_nat 31) by lia. exact V3.
Qed.

Lemma cb_key_range : forall o, length o = 32%nat -> (forall j, (j < 32)%nat -> 0 <= nth j o 0 < 256) ->
0 <= cmd_keyZ o < 2 ^ 32.
Proof.
intros o Hl Hb. pose proof (Hb 28%nat ltac:(lia)) as R0. pose proof (Hb 29%nat ltac:(lia)) as R1.
pose proof (Hb 30%nat ltac:(lia)) as R2. pose proof (Hb 31%nat ltac:(lia)) as R3.
do 32 (destruct o as [|? o]; [discriminate Hl|]). destruct o; [|discriminate Hl].
unfold cmd_keyZ. cbn [skipn firstn fold_right]. cbn [nth] in R0, R1, R2, R3. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ABCMP : abcmp_realizes tfibsegs B B_BCMP.
Theorem check_bytes_B_holds : cdcU_check_bytes_specX tfibsegs B MT B_CHECK_BYTES.
Proof using MTL TL LAWS ML ABCMP.
unfold cdcU_check_bytes_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q kc HE H10 Hq8 Hkc Hwf Hcrd Hlen Hl24 Hfirst Hkey Hdisp.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
unfold TB_check_bytes in *. assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (32 + 2 * 4096) HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wwl & Wwk & Wwd & _ & _ & Lout & Lwant).
pose proof Hcrd as (Hq0 & Hq63 & Hqv & Hqra & Hqhull & Hqam & Hqwin).
assert (Hq47 : q + 184 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqam. rewrite C4, C5 in Hqam. destruct Hqam as [Hl | [_ Hh]]; lia. }
pose proof Hkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vout & _ & Vwant & Vwl & Vwk & Vwd).
(* the fields read, as bytes and words *)
assert (GL : forall j, (j < 32)%nat -> val_mem tfibsegs (mrestrict (w_H W) memc) (q + 108 + Z.of_nat j) 1 (nth j (kz_out kc) 0)
  /\ 0 <= nth j (kz_out kc) 0 < 256) by (intros j Hj; apply Vout; lia).
destruct (GL 24%nat ltac:(lia)) as [Vlen Rlen]. destruct (GL 25%nat ltac:(lia)) as [Vdisp Rdisp].
change (Z.of_nat 24) with 24 in Vlen. change (Z.of_nat 25) with 25 in Vdisp.
replace (q + 108 + 24) with (q + 132) in Vlen by lia. replace (q + 108 + 25) with (q + 133) in Vdisp by lia.
pose proof (cb_key_mem _ (q + 108) (kz_out kc) Lout Vout) as Vkey. replace (q + 108 + 28) with (q + 136) in Vkey by lia.
assert (Rkey : 0 <= cmd_keyZ (kz_out kc) < 2 ^ 32) by (apply cb_key_range; [exact Lout | intros j Hj; apply (GL j Hj)]).
set (xs := cb_xs kc).
change (w64 q) with (Z_to_bv 64 q) in H10.
pose proof (Z.mod_pos_bound (kz_want_display kc) (2 ^ 32) ltac:(lia)) as Mwd.
assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (cmd_lenZ (kz_out kc))) by exact (cw_ew_x regs xs 0).
assert (X34 : ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (kz_want_len kc)) by exact (cw_ew_x regs xs 1).
assert (X35 : ew (Ereg regs (cw_extra xs)) 35 = Z_to_bv 64 (cmd_keyZ (kz_out kc))) by exact (cw_ew_x regs xs 2).
assert (X36 : ew (Ereg regs (cw_extra xs)) 36 = Z_to_bv 64 (kz_want_key kc)) by exact (cw_ew_x regs xs 3).
assert (X37 : ew (Ereg regs (cw_extra xs)) 37 = Z_to_bv 64 (cmd_displayZ (kz_out kc))) by exact (cw_ew_x regs xs 4).
assert (X38 : ew (Ereg regs (cw_extra xs)) 38 = Z_to_bv 64 (kz_want_display kc mod 2 ^ 32)) by exact (cw_ew_x regs xs 5).
unfold cmd_lenZ, cmd_displayZ in *.
assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) cb_AF).
{ unfold cb_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10, X33, X34, X35, X36, X37, X38.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS B_CHECK_BYTES 32 xs cb_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  (32 + 2 * 4096) HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 := X33). assert (E34 := X34). assert (E35 := X35). assert (E36 := X36). assert (E37 := X37). assert (E38 := X38).
clear HEE X33 X34 X35 X36 X37 X38.
assert (SHOK : sh_ok tfibsegs CW_Bx cb_SH E (mrestrict (w_H W) memc)).
{ unfold cb_SH. apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_crd W memc (spZ regs) (32 + 2 * 4096) E 10 q 184 Hcrd E10 E32 ltac:(lia)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 B_CHECK_BYTES) with (Z_to_bv 64 B_CHECK_BYTES).
(* 0x84d40-0x84d64: the saves, q into s0, the alignment check of q (not taken), the shadow offset into s1 *)
cw_run_to cw_awr_stk 0x84d68. cw_keep cw_kwr_stk.
cw_drop_gb.
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  val_mem tfibsegs (mrestrict (w_H W) memc) (q + o) n v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms)); [|exact Hv].
  intros x Hx. apply KE; [lia | cbv beta; unfold coff_win in Hqwin; lia]. }
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  assert (Hrok : region_ok tfibsegs Ev (ms_mem msv) cb_rec);
  [ unfold region_ok, cb_rec; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite E10, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    repeat apply Forall_cons; try apply Forall_nil;
    [ apply (chunk_ok_val tfibsegs E _ q 132 1 (SOff 33 0) (nth 24 (kz_out kc) 0));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 132 1%nat); [lia | cbn; lia | exact Vlen]
    | apply (chunk_ok_val tfibsegs E _ q 133 1 (SOff 37 0) (nth 25 (kz_out kc) 0));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 133 1%nat); [lia | cbn; lia | exact Vdisp]
    | apply (chunk_ok_val tfibsegs E _ q 136 4 (SOff 35 0) (cmd_keyZ (kz_out kc)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 136 4%nat); [lia | cbn; lia | exact Vkey]
    | apply (chunk_ok_val tfibsegs E _ q 168 8 (SOff 34 0) (kz_want_len kc));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 168 8%nat); [lia | cbn; lia | exact Vwl]
    | apply (chunk_ok_val tfibsegs E _ q 176 4 (SOff 36 0) (kz_want_key kc));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 176 4%nat); [lia | cbn; lia | exact Vwk]
    | apply (chunk_ok_val tfibsegs E _ q 180 4 (SOff 38 0) (kz_want_display kc mod 2 ^ 32));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 180 4%nat); [lia | cbn; lia|];
      exact (cw_val_mem_mod (mrestrict (w_H W) memc) (q + 180) 4%nat (kz_want_display kc) Vwd) ]
  | ];
  assert (Hdj : all_disjoint Ev cb_rec (ss_mem ssv));
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cb_rec;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, B2, unsigned_lit_small by lia;
    unfold coff_win in Hqwin; split; [lia | exact I]
  | ];
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv cb_rec HS eq_refl Hrok Hdj) as HS2;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS Hrok Hdj; rename HS2 into HS end.
(* 0x84d68 ..: the checks of len's and want_len's shadow, to bne want_len,len at 0x84d98 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
(* 0x84d98 bne want_len,len *)
cw_branch Hb1.
all: rewrite branch_ne_U, (cw_U_atom0 E 34 _ E34 ltac:(lia)), (cw_U_atom0 E 33 _ E33 ltac:(lia)) in Hb1.
- (* taken: want_len <> len, the abort call: refuted by want_len = out.len *)
  exfalso. apply negb_true_iff, Z.eqb_neq in Hb1. exact (Hb1 Hlen).
- (* bcmp(out.bytes, want, len) *)
  clear Hb1.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  rename HJ into HJ1.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H W) ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc] end.
  rreg HS (1%bv : bv 5) Gra. rreg HS (2%bv : bv 5) Gsp. rreg HS (3%bv : bv 5) Ggp. rreg HS (4%bv : bv 5) Gtp.
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rewrite B2 in Gsp. rewrite E10, unsigned_lit_small in Ga0, Ga1 by lia. rewrite E3 in Ggp. rewrite E4 in Gtp.
  rewrite E33 in Ga2.
  set (len := nth 24 (kz_out kc) 0) in *.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
  pose proof (cw_crd_kept W memc (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (spZ regs - 32) (spZ regs) Hcrd KE
    ltac:(lia) ltac:(unfold coff_win in Hqwin; lia)) as Hcrd1.
  pose proof (cw_crd_sub W (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (q + 108) len Hcrd1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hx0 & Hxn & Hxv & Hxra & Hxhull & Hxam & Hxwin).
  pose proof (cw_crd_sub W (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (q + 144) len Hcrd1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hy0 & Hyn & Hyv & Hyra & Hyhull & Hyam & Hywin).
  (* the first len bytes of out and want agree, at the call's memory *)
  assert (Hbytes : forall i, 0 <= i < len ->
    aview tfibsegs (w_H W) (ms_mem ms1) (q + 108 + i) = aview tfibsegs (w_H W) (ms_mem ms1) (q + 144 + i)).
  { intros i Hi. rewrite (KE (q + 108 + i)) by (first [lia | cbv beta; unfold coff_win in Hqwin; lia]).
    rewrite (KE (q + 144 + i)) by (first [lia | cbv beta; unfold coff_win in Hqwin; lia]).
    assert (Hn : nth (Z.to_nat i) (kz_out kc) 0 = nth (Z.to_nat i) (kz_want kc) 0).
    { rewrite <- (firstn_skipn (Z.to_nat (kz_want_len kc)) (kz_out kc)).
      rewrite <- (firstn_skipn (Z.to_nat (kz_want_len kc)) (kz_want kc)).
      rewrite !app_nth1 by (rewrite length_firstn; lia). rewrite Hfirst. reflexivity. }
    destruct (Vout (Z.to_nat i) ltac:(lia)) as [V1 _]. destruct (Vwant (Z.to_nat i) ltac:(lia)) as [V2 _].
    specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
    rewrite Z2Nat.id in V1, V2 by lia. change (Z.of_nat 0) with 0 in V1, V2. rewrite Z.add_0_r in V1, V2.
    unfold aview. rewrite V1, V2, Hn. reflexivity. }
  set (o := spZ regs - 32 - sp0).
  eapply SRr_bind.
  { eapply (cw_bcmp_at B LAWS B_BCMP ABCMP W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0
      own lyc Sc _ k (q + 108) (q + 144) len o (Z_to_bv 64 0x84da8)).
    - exact HJ1.
    - exact Ga0.
    - exact Ga1.
    - exact Ga2.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold spZ. rewrite Gsp, unsigned_lit_small by lia. unfold o. fold (spZ regs). lia.
    - unfold o. pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
      rewrite Hal16, Z.add_0_r in D1. rewrite Hsp0al, Z.add_0_r in D2.
      replace (spZ regs - 32 - sp0) with ((spZ regs / 16 - 2 - sp0 / 16) * 16) by lia. apply Z_mod_mult.
    - unfold o. lia.
    - rewrite Hes. unfold o. lia.
    - rewrite Ggp. exact Hgp.
    - rewrite Gtp. exact Htp.
    - exact Gra.
    - apply ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [apply Hxv; lia|]. unfold spZ. rewrite Gsp, unsigned_lit_small by lia. fold (spZ regs).
      rewrite Hes. unfold coff_win in Hqwin. lia.
    - intros a Ha. split; [apply Hyv; lia|]. unfold spZ. rewrite Gsp, unsigned_lit_small by lia. fold (spZ regs).
      rewrite Hes. unfold coff_win in Hqwin. lia.
    - intros a Ha. rewrite Hes. unfold o. unfold coff_win in Hqwin. lia.
    - intros a Ha. rewrite Hes. unfold o. unfold coff_win in Hqwin. lia.
    - exact Hxam.
    - exact Hyam.
    - exact Hxra.
    - exact Hxhull.
    - exact Hyra.
    - exact Hyhull. }
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hkept & Hpres2 & Hsame).
  rewrite Hes in Hkept.
  lazymatch type of HS with st_ok _ _ ?ssv _ =>
    let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
    jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2 end.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_aview; [rewrite E10; apply unsigned_lit_small; lia | | exact Hpres2].
      intros a Ha. apply Hkept; [lia | unfold o; unfold coff_win in Hqwin; lia].
    - eapply region_kept_aview; [exact B2 | | exact Hpres2].
      intros a Ha. apply Hkept; [lia | unfold o; lia]. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok _ ?En _ _ => remember En as E' eqn:HE' in HS end.
  assert (E1' : ew E' 1 = getr regs 1) by (rewrite HE', ew_havoc_old by lia; exact E1).
  assert (B2' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite HE', ew_havoc_old by lia; exact B2).
  assert (E10' : ew E' 10 = Z_to_bv 64 q) by (rewrite HE', ew_havoc_old by lia; exact E10).
  assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite HE', ew_havoc_old by lia; exact E32).
  assert (E35' : ew E' 35 = Z_to_bv 64 (cmd_keyZ (kz_out kc))) by (rewrite HE', ew_havoc_old by lia; exact E35).
  assert (E36' : ew E' 36 = Z_to_bv 64 (kz_want_key kc)) by (rewrite HE', ew_havoc_old by lia; exact E36).
  assert (E37' : ew E' 37 = Z_to_bv 64 (nth 25 (kz_out kc) 0)) by (rewrite HE', ew_havoc_old by lia; exact E37).
  assert (E38' : ew E' 38 = Z_to_bv 64 (kz_want_display kc mod 2 ^ 32)) by (rewrite HE', ew_havoc_old by lia; exact E38).
  assert (HAE' : env_agree 32 (Ereg regs (cw_extra xs)) E') by (rewrite HE'; env_agree_chain HAE).
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8224 <= a < spZ regs) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hz. rewrite (Hkept a Ha ltac:(unfold o; lia)). apply KE; [exact Ha | cbv beta; lia]. }
  rreg HS (10%bv : bv 5) Ga0'.
  assert (Hv43 : ew E' 43 = Z_to_bv 64 (bv_unsigned v)) by (rewrite <- Ga0', Hv; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 v) as Hvr. change (bv_modulus 64) with (2 ^ 64) in Hvr.
  pose proof (cw_crd_kept W memc mem2 (spZ regs) (32 + 2 * 4096) q 184 (spZ regs - 8224) (spZ regs) Hcrd KE2
    ltac:(lia) ltac:(unfold coff_win in Hqwin; lia)) as Hcrd2.
  clear SHOK.
  assert (SHOK : sh_ok tfibsegs CW_Bx cb_SH E' (mrestrict (w_H W) mem2)).
  { unfold cb_SH. apply Forall_cons; [|apply Forall_nil].
    exact (cw_shent_crd W mem2 (spZ regs) (32 + 2 * 4096) E' 10 q 184 Hcrd2 E10' E32' ltac:(lia)). }
  clear E1 B2 E10 E32 E33 E34 E35 E36 E37 E38 E3 E4 HAE KE HJ1 Ga0'.
  rename E1' into E1. rename B2' into B2. rename E10' into E10. rename E32' into E32. rename E35' into E35.
  rename E36' into E36. rename E37' into E37. rename E38' into E38. rename HAE' into HAE. rename KE2 into KE.
  (* 0x84da8 bnez a0 *)
  cw_branch Hb2.
  all: rewrite branch_ne_U, (cw_U_atom0 E' 43 (bv_unsigned v) Hv43 Hvr), U_lit in Hb2 by lia.
  + (* taken: a0 <> 0, the abort call: refuted, the first len bytes agree *)
    exfalso. apply negb_true_iff, Z.eqb_neq in Hb2. apply Hb2. rewrite (proj2 Hcmp Hbytes). reflexivity.
  + (* the checks of key's and want_key's shadow, lw both, to bne key,want_key at 0x84ddc *)
    clear Hb2.
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_branch Hb3.
    all: rewrite branch_ne_U in Hb3;
      first [ rewrite (cg_U_sx32_eqb2 _ 35 36 _ _ E35 E36 ltac:(lia) ltac:(lia)) in Hb3
            | rewrite (cg_U_sx32_eqb2 _ 36 35 _ _ E36 E35 ltac:(lia) ltac:(lia)) in Hb3 ].
    * (* taken: the abort call, refuted by key = want_key *)
      exfalso. rewrite Hkey, Z.eqb_refl in Hb3. discriminate Hb3.
    * (* the checks of display's and want_display's shadow, to bne want_display,display at 0x84e10 *)
      clear Hb3.
      assert (Wd : kz_want_display kc mod 2 ^ 32 = nth 25 (kz_out kc) 0) by (rewrite <- Hdisp; apply Z.mod_small; lia).
      rewrite Wd in E38.
      cw_run cw_awr_stk. cw_keep cw_kwr_stk.
      cw_branch Hb4.
      all: rewrite branch_ne_U in Hb4;
        lazymatch type of Hb4 with context [U ?Ex (SExt true 32 (SOff 38 0))] =>
          assert (E38x : ew Ex 38 = Z_to_bv 64 (nth 25 (kz_out kc) 0)) by (rewrite ?ew_ewset_other by lia; exact E38);
          assert (E37x : ew Ex 37 = Z_to_bv 64 (nth 25 (kz_out kc) 0)) by (rewrite ?ew_ewset_other by lia; exact E37) end;
        rewrite (cg_U_sx32 _ 38 _ E38x ltac:(lia)), (cw_U_atom0 _ 37 _ E37x ltac:(lia)) in Hb4;
        rewrite ?(proj2 (Z.ltb_lt (nth 25 (kz_out kc) 0) (2 ^ 31))) in Hb4 by lia; rewrite ?Z.eqb_refl in Hb4.
      -- (* taken: the abort call, refuted by want_display = display *)
         exfalso. discriminate Hb4.
      -- (* the return *)
         clear Hb4.
         cw_run cw_awr_stk. cw_keep cw_kwr_stk.
         cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros ? []) ltac:(intros ? Hz; left; cbv beta in Hz; lia)) ltac:(exact I).
Qed.
End d.
End b.
