(* LLVMFuzzerTestOneInput_seg_exit: u_exit_ok : u_exit_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the exit of
   the image-B walk of fuzz_uci.asan-ubsan's LLVMFuzzerTestOneInput, in the form of the image-A twin's turn_b segment
   (a run of the Pa engine to a call, the callee contract at the call, the run from its return address) and
   proofs/libreac/fuzz_decode's image-B teardown LLVMFuzzerTestOneInput_segX_exit_td.v (the reloads, the return and
   the slot post out of the journal).

   Two runs of the Pa engine, each from a seat with the registers as atoms (Ereg regs extra):
   - ux_A, +0x1c8 .. +0x21c: one region on sp (atom 2 = sp1) over [sp1 + 8, sp1 + 0x30), the five results at
     sp1 + 0x1c + 4 j read only (extra atoms 32 .. 36, each result mod 2 ^ 32) and the 20 bytes [sp1 + 8, sp1 + 0x1c)
     writable; the fact sp1 in [2 ^ 46, 2 ^ 47] decides the four UBSan wrap checks of a0 = sp + 0x1c (+0x1d8
     `beq a0, -4`, +0x1e8 `bltu -9, a0`, +0x1f8 `bltu -0xd, a0`, +0x208 `bltu -0x11, a0`, each to `unimp` at +0x25c)
     as not taken, so the engine runs over them; the five `lw` / `sw` copy the results to sp1 + 8 + 4 j and the run
     stops at the call of check_clamp (+0x21c, a0 = sp1 + 8, a1 = s2 = margin_max, ra = +0x220), which ux_call takes
     by u_prem's contract (lib/B/Prog/check_clamp_cg.v) to ux_st at +0x220;
   - ux_B, +0x220 .. +0x258: one read-only region on sp holding the twelve saved words (extra atoms 32 .. 43, the
     caller's registers in uci_saved_at's order); a0 = 0, the twelve reloads, sp += 0x90; the return at +0x258 goes to
     the caller's ra = RA_LLVMF, and the slot post (u_post) comes out of the journal. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YE01 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import PaJournal UciPSyms UciPList UciPAddr UciPPa
  UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Cells Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module LC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib.Cells.
Module LM := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib.Mem.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Values and bytes                                                 *)
(* ------------------------------------------------------------------ *)

(* The int `lw` loads from four bytes cu (unsigned little-endian): its sign extension. *)
Definition ux_cur (cu : Z) : Z := if cu <? 2 ^ 31 then cu else cu - 2 ^ 32.
Lemma ux_cur_mod : forall v, INT_MIN <= v <= INT_MAX -> ux_cur (v mod 2 ^ 32) = v.
Proof.
intros v Hv. unfold ux_cur, INT_MIN, INT_MAX in *.
destruct (Z.ltb_spec (v mod 2 ^ 32) (2 ^ 31)); destruct (Z.lt_ge_cases v 0); lia.
Qed.
Lemma ux_swrap : forall cu, 0 <= cu < 2 ^ 32 -> bv_swrap 32 cu = ux_cur cu.
Proof.
intros cu Hcu. unfold ux_cur, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
destruct (Z.ltb_spec cu (2 ^ 31)); cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]; lia.
Qed.
Lemma ux_w64_canon : forall z, Z_to_bv 64 (zcanon z) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma ux_sext_denot : forall E (n : nat) cu, ew E n = Z_to_bv 64 cu -> 0 <= cu < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = w64 (ux_cur cu).
Proof.
intros E n cu Hn Hcu.
assert (Hx : U E (SExt true 32 (SOff n 0)) = zcanon (ux_cur cu)).
{ rewrite U_SExt, (U_atom E n cu Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. rewrite ux_swrap by lia. reflexivity. }
rewrite denot_lit_U, Hx. apply ux_w64_canon.
Qed.
Lemma ux_soff_denot : forall E (a : nat) w, ew E a = w -> sv_denot E (SOff a 0) = w.
Proof. intros E a w Ha. cbn [sv_denot]. rewrite Ha, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* A stored 4-byte chunk holds the four little-endian bytes of the value of its register. *)
Lemma ux_mod_div : forall v M d, 0 < d -> 0 < M -> M mod (d * 256) = 0 -> ((v mod M) / d) mod 256 = (v / d) mod 256.
Proof.
intros v M d Hd HM HMd.
assert (EM : M = d * 256 * (M / (d * 256))) by (pose proof (Z.div_mod M (d * 256) ltac:(lia)); lia).
rewrite (Z.mod_eq v M) by lia.
set (q := M / (d * 256)) in *. set (w := v / M) in *. clearbody q w.
rewrite EM.
replace (v - d * 256 * q * w) with (v + (- (256 * q * w)) * d) by ring.
rewrite Z.div_add by lia.
replace (v / d + - (256 * q * w)) with (v / d + (- (q * w)) * 256) by ring.
apply Z.mod_add. lia.
Qed.
Lemma ux_le_byte4 : forall v k, (k < 4)%nat ->
  Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k) mod 256 = YG0f.le_byte v 4 k.
Proof.
intros v k Hk. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia. change (8 * Z.of_nat 4) with 32.
rewrite (ux_mod_div v (2 ^ 64) (2 ^ (8 * Z.of_nat k))), (ux_mod_div v (2 ^ 32) (2 ^ (8 * Z.of_nat k))); try lia;
  do 4 (destruct k as [|k]; [reflexivity|]); lia.
Qed.
Lemma ux_store_val : forall segs E m base off e v,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) 4 v.
Proof.
intros segs E m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [c_len YP09.c_val cv_len]; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Hm. injection Hb as <-. f_equal.
unfold byte_of_word. rewrite He. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
rewrite (ux_le_byte4 v k Hk). unfold YO0f.le_byte, YG0f.le_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* Four bytes of a value are the four bytes of the value mod 2 ^ 32. *)
Lemma ux_val_mem_mod32 : forall segs m a v, val_mem segs m a 4 v -> val_mem segs m a 4 (v mod 2 ^ 32).
Proof.
intros segs m a v Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The struct the call reads: five little-endian int fields, as garr8 of the image view (check_clamp_cg.v
   uci_hot_bytes). *)
Lemma ux_garr8_c4z : forall segs m a v, val_mem segs m a 4 v ->
  garr8 segs m a (map (fun b : byte => bv_unsigned b) (LC.cbytes (PHC.c4z v))).
Proof.
intros segs m a v Hv j Hj. cbn [PHC.c4z LC.cbytes] in *. unfold LM.le4 in *.
rewrite length_map, LM.length_Z_to_le_bytes in Hj.
assert (Hb : forall k, (k < 4)%nat ->
  nth k (map (fun b : byte => bv_unsigned b) (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v)))) 0 =
  Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k) mod 256).
{ intros k Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  set (z := v mod 2 ^ 64). do 4 (destruct k as [|k];
    [cbn [Z_to_le_bytes map nth]; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
     rewrite ?Z.shiftr_shiftr by lia; cbn [Z.add Z.of_nat Z.mul]; rewrite ?Z.shiftr_0_r; reflexivity|]). lia. }
rewrite (Hb j Hj). rewrite (ux_le_byte4 v j Hj). split.
- intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (Hv j Hj). f_equal. f_equal. unfold YO0f.le_byte, YG0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite !Z.mod_mod by lia. reflexivity.
- unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma ux_hot_garr8 : forall segs m a v0 v1 v2 v3 v4,
  val_mem segs m a 4 v0 -> val_mem segs m (a + 4) 4 v1 -> val_mem segs m (a + 8) 4 v2 ->
  val_mem segs m (a + 12) 4 v3 -> val_mem segs m (a + 16) 4 v4 ->
  garr8 segs m a (PK.uci_hot_bytes (RpHot v0 v1 v2 v3 v4)).
Proof.
intros segs m a v0 v1 v2 v3 v4 H0 H1 H2 H3 H4. unfold PK.uci_hot_bytes, PHC.hot_cells.
cbn [LC.cells_bytes prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm]. rewrite app_nil_r.
assert (L : forall v, length (map (fun b : byte => bv_unsigned b) (LC.cbytes (PHC.c4z v))) = 4%nat)
  by (intros v; rewrite length_map; cbn [PHC.c4z LC.cbytes]; apply LM.length_le4).
rewrite !map_app.
apply garr8_app. split; [exact (ux_garr8_c4z segs m a v0 H0)|]. rewrite L.
replace (a + Z.of_nat 4) with (a + 4) by lia.
apply garr8_app. split; [exact (ux_garr8_c4z segs m _ v1 H1)|]. rewrite L.
replace (a + 4 + Z.of_nat 4) with (a + 8) by lia.
apply garr8_app. split; [exact (ux_garr8_c4z segs m _ v2 H2)|]. rewrite L.
replace (a + 8 + Z.of_nat 4) with (a + 12) by lia.
apply garr8_app. split; [exact (ux_garr8_c4z segs m _ v3 H3)|]. rewrite L.
replace (a + 12 + Z.of_nat 4) with (a + 16) by lia.
exact (ux_garr8_c4z segs m _ v4 H4).
Qed.

(* The stack's shadow is zero (AR's zero-shadow range of the stack): a range well inside the stack is addressable,
   and the eight-byte shadow groups around its shadow are visible. *)
Lemma ux_stk_shadow : forall (rd : reader) lo hi x n,
  zero_shadow rd SHADOW_OFF lo (hi - lo) -> 0 <= lo -> lo + 64 <= x -> 0 < n -> x + n + 100 <= hi ->
  range_addressable rd SHADOW_OFF x n /\ shadow_hull_vis rd x n.
Proof.
intros rd lo hi x n HZ Hlo Hx Hn Hhi. split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
    by (unfold shadow_of_addr; lia).
  apply HZ. lia.
- intros s Hs Hn0. unfold shadow_addr, SHADOW_OFF in Hs.
  replace s with (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) in Hn0 by lia.
  rewrite (HZ (s - shadow_of_addr SHADOW_OFF lo)) in Hn0; [discriminate|].
  unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.

(* What a run whose regions all write only [base + 8, base + 0x1c) of atom 2 leaves of the memory. *)
Lemma ux_frame : forall E rs (m m' : word -> option byte) sp1,
  frame_of E rs m m' ->
  forallb (fun r => match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end &&
    (YP09.r_wlo r =? 8) && (YP09.r_whi r =? 0x1c))%bool rs = true ->
  bv_unsigned (ew E 2) = sp1 -> forall x, ~ (sp1 + 8 <= bv_unsigned x < sp1 + 0x1c) -> m' x = m x.
Proof.
intros E rs m m' sp1 HF Hb HR x Hx. apply HF. intros (r & Hin & Ha). rewrite forallb_forall in Hb.
specialize (Hb r Hin). destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb].
rewrite !andb_true_iff in Hb. destruct Hb as ((Hn & Hlo) & Hhi).
apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hlo, Hhi. subst n.
cbn [base_val] in Ha. rewrite HR, Hlo, Hhi in Ha. lia.
Qed.

(* A callee-saved register through aregs_preserved. *)
Lemma ux_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac ux_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; unfold acallee_saved; lia end.
Ltac ux_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* 2. The two seats                                                    *)
(* ------------------------------------------------------------------ *)

(* +0x1c8: the region [sp1 + 8, sp1 + 0x30) of atom 2 = sp1, the five results read only at sp1 + 0x1c + 4 j
   (atoms 32 .. 36), the 20 bytes below them writable. *)
Definition ux_res : list YP09.chunk :=
  [YP09.mkChunk 0x1c (CVal 4 (SOff 32 0)); YP09.mkChunk 0x20 (CVal 4 (SOff 33 0));
   YP09.mkChunk 0x24 (CVal 4 (SOff 34 0)); YP09.mkChunk 0x28 (CVal 4 (SOff 35 0));
   YP09.mkChunk 0x2c (CVal 4 (SOff 36 0))].
Definition ux_fr1 : YP09.region := YP09.mkRegion (Some 2%nat) 8 0x30 8 0x1c ux_res.
Definition ux_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_x1 : sstate := mkSS U_EXIT sr_atoms [ux_fr1] None ux_facts.
Definition ux_ex1 (v0 v1 v2 v3 v4 : Z) : list word :=
  [Z_to_bv 64 (v0 mod 2 ^ 32); Z_to_bv 64 (v1 mod 2 ^ 32); Z_to_bv 64 (v2 mod 2 ^ 32); Z_to_bv 64 (v3 mod 2 ^ 32);
   Z_to_bv 64 (v4 mod 2 ^ 32)].

(* +0x220: the twelve saved words of [sp1 + 0x30, sp1 + 0x90), read only (atoms 32 .. 43 in uci_saved_at's order). *)
Definition ux_sv : list YP09.chunk :=
  [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x78 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x68 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 37 0));
   YP09.mkChunk 0x58 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 39 0));
   YP09.mkChunk 0x48 (CVal 8 (SOff 40 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 41 0));
   YP09.mkChunk 0x38 (CVal 8 (SOff 42 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 43 0))].
Definition ux_fr2 : YP09.region := YP09.mkRegion (Some 2%nat) 0x30 0x90 0 0 ux_sv.
Definition ss_x2 : sstate := mkSS 0x220 sr_atoms [ux_fr2] None ux_facts.
Definition ux_ex2 (regs0 : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs0 (Z_to_bv 5 (snd o))) uci_saved_at.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Lemma ux_seat1 : forall (W : world SEGS) (regs : bvmap 5 word) mem sp1 v0 v1 v2 v3 v4,
  spZ regs = sp1 -> 2 ^ 46 <= sp1 -> sp1 + 0x90 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
  (forall a, sp1 + 8 <= a < sp1 + 0x1c -> apresent (w_H W) mem a) ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 0x1c) v0 -> rd32 (aview SEGS (w_H W) mem) (sp1 + 0x20) v1 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 0x24) v2 -> rd32 (aview SEGS (w_H W) mem) (sp1 + 0x28) v3 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 0x2c) v4 ->
  st_ok_pi SEGS VAL (Eimg (PI := PI_uci) (Ereg regs (ux_ex1 v0 v1 v2 v3 v4))) ss_x1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + U_EXIT)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 v0 v1 v2 v3 v4 Hsp Hlo Hhi H16 Hpres R0 R1 R2 R3 R4.
rewrite restrict_mkst_fx. unfold ss_x1.
set (E := Eimg (PI := PI_uci) (Ereg regs (ux_ex1 v0 v1 v2 v3 v4))).
assert (E2 : bv_unsigned (ew E 2) = sp1)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ux_ex1 v0 v1 v2 v3 v4) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, ux_fr1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
  unfold ux_res.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 4 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 32)%nat in
    let v := eval cbn in (nth j [v0; v1; v2; v3; v4] 0) in
    apply (chunk_ok_val SEGS E _ sp1 off 4 (SOff n 0) (v mod 2 ^ 32));
    [ cbn [sv_denot]; let Ej := fresh "Ej" in pose proof (EX j ltac:(lia)) as Ej; cbn [Nat.add] in Ej; rewrite Ej;
      cbn [nth ux_ex1]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 4) with 32; apply Z.mod_pos_bound; lia
    | cbn; lia
    | apply ux_val_mem_mod32, val_mem_of_rd32; assumption ]
  end.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [ux_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. lia.
Qed.

Lemma ux_seat2 : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem sp0,
  spZ regs = sp0 - 0x90 -> 2 ^ 46 <= sp0 - 0x90 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  Forall (fun o : Z * Z => rdword (aview SEGS (w_H W) mem) (sp0 - fst o) =
    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (snd o))))) uci_saved_at ->
  st_ok_pi SEGS VAL (Eimg (PI := PI_uci) (Ereg regs (ux_ex2 regs0))) ss_x2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x220)) mem (seg_rom SEGS))).
Proof.
intros W regs regs0 mem sp0 Hsp Hlo Hhi H16 Hsv.
rewrite restrict_mkst_fx. unfold ss_x2.
set (E := Eimg (PI := PI_uci) (Ereg regs (ux_ex2 regs0))).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 0x90)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (ux_ex2 regs0) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
unfold uci_saved_at in Hsv. cbn [fst snd] in Hsv.
repeat match type of Hsv with Forall _ (_ :: _) =>
  apply Forall_cons_iff in Hsv; let H := fresh "Hw" in destruct Hsv as [H Hsv]; cbn [fst snd] in H end.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, ux_fr2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold ux_sv.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 32)%nat in
    let o := eval vm_compute in (0x90 - off) in
    lazymatch goal with Hw : rdword _ (sp0 - o) = Some ?v |- _ =>
      apply (chunk_ok_val SEGS E _ (sp0 - 0x90) off 8 (SOff n 0) v);
      [ cbn [sv_denot]; let Ej := fresh "Ej" in pose proof (EX j ltac:(lia)) as Ej; cbn [Nat.add] in Ej; rewrite Ej;
        cbn [nth ux_ex2 map uci_saved_at snd];
        rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 8) with 64; apply bv_unsigned_in_range
      | cbn; lia
      | replace (sp0 - 0x90 + off) with (sp0 - o) by lia; exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw) ]
    end
  end.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [ux_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. lia.
Qed.
End seat.

(* ------------------------------------------------------------------ *)
(* 3. Tactics of the runs                                              *)
(* ------------------------------------------------------------------ *)

(* A register's symbolic value at a state (st_ok_pi, or st_ok at a call). *)
Ltac ux_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?sg ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* The write rights of the run of ux_A: the copy's 20 bytes, at -0x90 + [8, 0x1c) of the entry sp. *)
Ltac ux_awr U2 :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-144));
    [reflexivity | rewrite U2; unfold u_sp1, U_FRAME; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |] ].
Ltac ux_awr_ro :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* The model after a run, named. *)
Ltac ux_md md2 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in *; clearbody md2 end.

(* The five results of u_st_exit, one by one. *)
Lemma ux_res5 : forall cx r vs, u_res cx r 5 vs ->
  exists v0 v1 v2 v3 v4, vs = [v0; v1; v2; v3; v4] /\ PHC.hot_int (RpHot v0 v1 v2 v3 v4) /\
  rd32 r (u_sp1 cx + 0x1c) v0 /\ rd32 r (u_sp1 cx + 0x20) v1 /\ rd32 r (u_sp1 cx + 0x24) v2 /\
  rd32 r (u_sp1 cx + 0x28) v3 /\ rd32 r (u_sp1 cx + 0x2c) v4.
Proof.
intros cx r vs (Hl & Hf & Hw).
destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 vs]]]]]]; try (cbn [length] in Hl; lia).
exists v0, v1, v2, v3, v4. split; [reflexivity|].
apply Forall_cons_iff in Hf as [F0 Hf]. apply Forall_cons_iff in Hf as [F1 Hf].
apply Forall_cons_iff in Hf as [F2 Hf]. apply Forall_cons_iff in Hf as [F3 Hf].
apply Forall_cons_iff in Hf as [F4 _].
split; [unfold PHC.hot_int; cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm];
  exact (conj F0 (conj F1 (conj F2 (conj F3 F4))))|].
pose proof (Hw 0 ltac:(lia)) as H0. pose proof (Hw 1 ltac:(lia)) as H1. pose proof (Hw 2 ltac:(lia)) as H2.
pose proof (Hw 3 ltac:(lia)) as H3. pose proof (Hw 4 ltac:(lia)) as H4.
change (Z.to_nat 0) with 0%nat in H0. change (Z.to_nat 1) with 1%nat in H1. change (Z.to_nat 2) with 2%nat in H2.
change (Z.to_nat 3) with 3%nat in H3. change (Z.to_nat 4) with 4%nat in H4.
cbn [nth] in H0, H1, H2, H3, H4.
replace (u_sp1 cx + 0x1c + 4 * 0) with (u_sp1 cx + 0x1c) in H0 by lia.
replace (u_sp1 cx + 0x1c + 4 * 1) with (u_sp1 cx + 0x20) in H1 by lia.
replace (u_sp1 cx + 0x1c + 4 * 2) with (u_sp1 cx + 0x24) in H2 by lia.
replace (u_sp1 cx + 0x1c + 4 * 3) with (u_sp1 cx + 0x28) in H3 by lia.
replace (u_sp1 cx + 0x1c + 4 * 4) with (u_sp1 cx + 0x2c) in H4 by lia.
exact (conj H0 (conj H1 (conj H2 (conj H3 H4)))).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The frame and the call                                           *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc YE2k.tfib_sink_head segs B).

(* The state at +0x220, after check_clamp: the frame invariant at the events of five turns and the call, the meter of
   five turns (the call charges nothing). *)
Definition ux_st (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = u_cfg cx 0x220 regs' mem' md' /\
    u_core B cx ly' S' W' regs' mem' md' (5 * U_EV_TURN + PK.CC_EV) /\
    u_meter MT XL cx S' 5.

(* The stack facts of the journal: the entry sp's alignment and bounds, the stack window present, and the layout's
   stack range around it. *)
Lemma ux_J_facts : forall cx ly' S' W mem md k,
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  u_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47 /\
  (forall a, u_sp0 cx - LLVMF_STK <= a < u_sp0 cx -> apresent (w_H W) mem a) /\
  ly_stk_lo (u_ly cx) + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= ly_stk_hi (u_ly cx) /\ alloc_ceiling <= ly_stk_lo (u_ly cx).
Proof.
intros cx ly' S' W mem md k HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
refine (conj H16 (conj _ (conj _ (conj Hpres (conj Hlo (conj Hhi Hceil)))))); lia.
Qed.

(* The copy's 20 bytes are addressable in the shadow and their shadow groups visible: AR's zero-shadow range of the
   stack (the layout's stack range, which the journal keeps) covers them. *)
Lemma ux_frame_shadow : forall cx lyc Sc W memc mdc k,
  u_prem B MT XL RLO RHI ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] lyc Sc W memc mdc k ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF (u_sp1 cx + 8) PHC.RP_HOT_SIZE /\
  shadow_hull_vis (aview segs (w_H W) memc) (u_sp1 cx + 8) PHC.RP_HOT_SIZE.
Proof.
intros cx lyc Sc W memc mdc k HP HJ.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HJ as (HAR & Hly & _).
destruct (ux_J_facts cx _ _ _ _ _ _ HJ) as (H16 & Hc & H47 & _ & Hlo & Hhi & Hceil).
pose proof alloc_ceiling_val as Hce.
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
cbn [fst snd] in HZ.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hslo & Hshi & _).
apply (ux_stk_shadow _ (ly_stk_lo lyc) (ly_stk_hi lyc)); [exact HZ | ..];
  rewrite ?Hslo, ?Hshi; unfold u_sp1, U_FRAME, PHC.RP_HOT_SIZE, LLVMF_STK in *; lia.
Qed.

(* The saved words lie in [sp0 - 96, sp0): a view that keeps those bytes keeps them. *)
Lemma ux_saved_kept : forall cx (r r' : reader), u_saved cx r ->
  (forall a, u_sp0 cx - 96 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r'.
Proof.
intros cx r r' Hs Hk. unfold u_saved in *. rewrite Forall_forall in *. intros o Ho.
rewrite <- (Hs o Ho). apply rdword_kept. intros k Hk8.
assert (Hf : 8 <= fst o <= 96).
{ unfold uci_saved_at in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply Hk. lia.
Qed.

(* A run that kept sp, gp, tp, s11 and the saved words keeps the frame invariant. *)
Lemma ux_core_kept : forall cx ly' S' (W : world segs) regs regs' mem mem' md md' k,
  u_core B cx ly' S' W regs mem md k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem' md' k ->
  (forall r : bv 5, In r [2; 3; 4; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  (forall a, u_sp0 cx - 96 <= a < u_sp0 cx -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  u_core B cx ly' S' W regs' mem' md' k.
Proof.
intros cx ly' S' W regs regs' mem mem' md md' k (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm) HJ' KA KV.
refine (conj HJ' (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj _ Hperm))))))).
- unfold spZ in *. rewrite (KA 2%bv ltac:(ux_in)). exact Hsp.
- rewrite (KA 3%bv ltac:(ux_in)). exact Hgp.
- rewrite (KA 4%bv ltac:(ux_in)). exact Htp.
- rewrite (KA 27%bv ltac:(ux_in)). exact H27.
- exact (ux_saved_kept cx _ _ Hsv KV).
Qed.

(* A call's post (callee-saved registers, the callee's stack window [spT - STKc, spT) the only bytes written, the
   journal extended) moved to the frame invariant. *)
Lemma ux_after_call : forall cx (W W2 : world segs) regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 k EV STKc,
  u_core B cx ly' S' W regsT memT mdT k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly2 S2 W2 mem2 md2 (k + EV) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  @acall_kept rc segs B ly' S' W memT W2 mem2 (spZ regsT - STKc) (spZ regsT) (fun _ => False) ->
  u_core B cx ly2 S2 W2 regs2 mem2 md2 (k + EV).
Proof.
intros cx W W2 regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 k EV STKc HC HJ2 HPr Hfr2 Hperm2 HK.
destruct HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (ux_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
assert (KV : forall a, u_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. destruct HK as (K1 & _). apply K1; [unfold u_sp1, U_FRAME, LLVMF_STK in *; lia | rewrite Hsp; lia]. }
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (ux_pres regsT regs2 r HPr Hr)).
refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- rewrite Hfr2. exact Hfrs.
- unfold spZ in *. rewrite (P 2%bv ltac:(ux_cs)). exact Hsp.
- rewrite (P 3%bv ltac:(ux_cs)). exact Hgp.
- rewrite (P 4%bv ltac:(ux_cs)). exact Htp.
- rewrite (P 27%bv ltac:(ux_cs)). exact H27.
- apply (ux_saved_kept cx _ _ Hsv). intros a Ha. apply KV. unfold u_sp1, U_FRAME in *. lia.
- exact (Permutation_trans Hperm2 Hperm).
Qed.

(* check_clamp (sp1 + 8, margin_max) at +0x21c by u_prem's contract; its return +0x220 is ux_st. Each premise of
   lib/B/Prog/check_clamp_cg.v uci_check_clamp_cg, in its order: the caller's journal (u_core); ra = +0x220, a return
   address >= 4096; gp, tp (u_core); a0 = pin = sp1 + 8, a1 = mm; sp1 mod 16 = 0 and sp0 - LLVMF_STK <= sp1 - CC_STK,
   sp1 <= sp0 (the journal's astk_ok, frame 0x90); hot_int (u_res); 0 <= mm <= INT_MAX (mm is 1984 or 16320);
   pin mod 4 = 0, sp1 <= pin, pin + 20 < sp0; garr8 of the 20 bytes (the copy); range_addressable and
   shadow_hull_vis (ux_frame_shadow); count_cid 1 (frames S') = 0 < fs_frames 1 (frames S' = [] by u_core); the
   event bound (the slot pre's st_nev S + EV_LIB <= EV_MAX, five turns and CC_EV = 0 below EV_LIB). *)
Lemma ux_call : forall cx (W : world segs) regsT memT mdT ly' S' mm v0 v1 v2 v3 v4,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  u_core B cx ly' S' W regsT memT mdT (5 * U_EV_TURN) -> u_meter MT XL cx S' 5 ->
  YK11.getr regsT 1 = w64 (UCI_A_LLVMF + 0x220) ->
  YK11.getr regsT 10 = w64 (u_sp1 cx + 8) -> YK11.getr regsT 11 = w64 mm -> (mm = U_MM0 \/ mm = U_MM1) ->
  PHC.hot_int (RpHot v0 v1 v2 v3 v4) ->
  garr8 segs (mrestrict (w_H W) memT) (u_sp1 cx + 8) (PK.uci_hot_bytes (RpHot v0 v1 v2 v3 v4)) ->
  SRr segs W (@cfg_at (u_fx cx) segs (uci_sigma US_check_clamp) regsT memT mdT) (ux_st cx).
Proof.
intros cx W regsT memT mdT ly' S' mm v0 v1 v2 v3 v4 HP HB HC (Hle & Hmo) R1 R10 R11 Hmm Hhot Hg.
pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
assert (Hnev : st_nev (u_S cx) + EV_LIB <= EV_MAX)
  by (unfold u_base, tfib_lib_pre_x in HB; destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev & _); exact Hnev).
destruct (ux_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
destruct (ux_frame_shadow cx _ _ _ _ _ _ HP HJ) as (HRA & HHV).
assert (Hraz : raZ regsT = UCI_A_LLVMF + 0x220)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
eapply SRr_bind.
{ refine (up_cc _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT (5 * U_EV_TURN) regsT (u_sp1 cx + 8) mm (RpHot v0 v1 v2 v3 v4)
    HJ _ _ Hgp Htp R10 R11 _ _ _ Hhot _ _ _ _ Hg HRA HHV _ _).
  - rewrite R1. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME, PK.CC_STK, PK.CC_FRAME, PK.CC_ALIGN, ESTACK, LLVMF_STK. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - destruct Hmm as [-> | ->]; unfold U_MM0, U_MM1, INT_MAX; lia.
  - unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. lia.
  - unfold u_sp1, U_FRAME, PHC.RP_HOT_SIZE. lia.
  - rewrite Hfrs. vm_compute. reflexivity.
  - unfold U_EV_TURN, PN.CNO_EV, PV.CV_EV, PK.CC_EV, EV_LIB in *. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hperm2 & HK & Hmle).
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2.
refine (conj _ (conj _ (conj _ _))).
- unfold u_cfg. rewrite R1. reflexivity.
- exact (ux_after_call cx W W2 regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 _ _ PK.CC_STK HC HJ2 HPr Hfr2 Hperm2 HK).
- rewrite <- (Z.add_0_r (5 * U_TURN_COST MT)). exact (mo_le_trans MT ML _ _ _ _ _ Hle Hmle).
- apply (mo_ok_step MT ML S' S2 0); [rewrite Z.add_0_l; exact Hmo | exact Hmle].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The two runs                                                     *)
(* ------------------------------------------------------------------ *)

(* +0x1c8 .. +0x21c and check_clamp. The run decides the four UBSan wrap checks of a0 = sp1 + 0x1c by the fact
   2 ^ 46 <= sp1 <= 2 ^ 47 on atom 2 (none of -4 = sp1 + 0x1c, -9 <u sp1 + 0x1c, -0xd <u sp1 + 0x1c,
   -0x11 <u sp1 + 0x1c holds below 2 ^ 47 + 0x1c), so `unimp` at +0x25c is never reached. *)
Lemma ux_A : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> u_st_exit B MT XL cx W c -> SRr segs W c (ux_st cx).
Proof.
intros cx W c HP HB HEX.
destruct HEX as (ly' & S' & regs & mem & md & mm & vs & -> & HC & HM & R18 & Hmm & HR).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (ux_J_facts cx ly' S' W mem md _ HJ) as (H16 & Hceil & H47 & Hpres & _).
pose proof alloc_ceiling_val as Hce.
destruct (ux_res5 cx _ vs HR) as (v0 & v1 & v2 & v3 & v4 & -> & Hhot & Rd0 & Rd1 & Rd2 & Rd3 & Rd4).
pose proof Hhot as (I0 & I1 & I2 & I3 & I4).
cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm] in I0, I1, I2, I3, I4.
pose proof (@ux_seat1 (u_fx cx) rc W regs mem (u_sp1 cx) v0 v1 v2 v3 v4 Hsp
  ltac:(unfold u_sp1, U_FRAME, LLVMF_STK in *; lia) ltac:(unfold u_sp1, U_FRAME in *; lia)
  ltac:(unfold u_sp1, U_FRAME in *; lia)
  ltac:(intros a Ha; apply Hpres; unfold u_sp1, U_FRAME, LLVMF_STK in *; lia) Rd0 Rd1 Rd2 Rd3 Rd4) as HS.
set (E0 := Eimg (PI := PI_uci) (Ereg regs (ux_ex1 v0 v1 v2 v3 v4))) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ uci_listing PI_uci) (SOff 21 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (ux_ex1 v0 v1 v2 v3 v4)) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (ux_ex1 v0 v1 v2 v3 v4) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U2 : bv_unsigned (ew E0 2) = u_sp1 cx) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
pose proof (paj_run (fx := u_fx cx) (SK := YE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + U_EXIT)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
paj_run_tok RUN HS HJ SHOK Bspan; [ux_awr U2|].
ux_md mdA.
assert (HM1 : forall x, ~ (u_sp1 cx + 8 <= bv_unsigned x < u_sp1 cx + 0x1c) -> ms_mem ms x = mem x)
  by exact (ux_frame E0 _ _ _ (u_sp1 cx) HF ltac:(vm_compute; reflexivity) U2).
clear HF HFr HG.
(* the five words the run stored at sp1 + 8 + 4 j: the sign extension of each result's four bytes *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch rr with Some ?r =>
    pose proof (st_ok_region_nth E0 ss (restrict (w_H W) ms) 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end end.
destruct HR0 as (_ & _ & _ & Hcs).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hcs. rewrite U2 in Hcs.
apply Forall_cons_iff in Hcs as [C4 Hcs]. apply Forall_cons_iff in Hcs as [C3 Hcs].
apply Forall_cons_iff in Hcs as [C2 Hcs]. apply Forall_cons_iff in Hcs as [C1 Hcs].
apply Forall_cons_iff in Hcs as [C0 _].
assert (E32 : ew E0 32 = Z_to_bv 64 (v0 mod 2 ^ 32)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E0 33 = Z_to_bv 64 (v1 mod 2 ^ 32)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E0 34 = Z_to_bv 64 (v2 mod 2 ^ 32)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E0 35 = Z_to_bv 64 (v3 mod 2 ^ 32)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E0 36 = Z_to_bv 64 (v4 mod 2 ^ 32)) by exact (EX 4%nat ltac:(lia)).
assert (V0 : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 8) 4 v0).
{ rewrite <- (ux_cur_mod v0 I0).
  exact (ux_store_val _ E0 _ (u_sp1 cx) 8 _ _ C0 (ux_sext_denot E0 32 _ E32 ltac:(apply Z.mod_pos_bound; lia))). }
assert (V1 : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 12) 4 v1).
{ rewrite <- (ux_cur_mod v1 I1).
  exact (ux_store_val _ E0 _ (u_sp1 cx) 12 _ _ C1 (ux_sext_denot E0 33 _ E33 ltac:(apply Z.mod_pos_bound; lia))). }
assert (V2 : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 16) 4 v2).
{ rewrite <- (ux_cur_mod v2 I2).
  exact (ux_store_val _ E0 _ (u_sp1 cx) 16 _ _ C2 (ux_sext_denot E0 34 _ E34 ltac:(apply Z.mod_pos_bound; lia))). }
assert (V3 : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 20) 4 v3).
{ rewrite <- (ux_cur_mod v3 I3).
  exact (ux_store_val _ E0 _ (u_sp1 cx) 20 _ _ C3 (ux_sext_denot E0 35 _ E35 ltac:(apply Z.mod_pos_bound; lia))). }
assert (V4 : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 24) 4 v4).
{ rewrite <- (ux_cur_mod v4 I4).
  exact (ux_store_val _ E0 _ (u_sp1 cx) 24 _ _ C4 (ux_sext_denot E0 36 _ E36 ltac:(apply Z.mod_pos_bound; lia))). }
assert (Hg : garr8 segs (mrestrict (w_H W) (ms_mem ms)) (u_sp1 cx + 8) (PK.uci_hot_bytes (RpHot v0 v1 v2 v3 v4))).
{ apply ux_hot_garr8; [exact V0 | | | |].
  - replace (u_sp1 cx + 8 + 4) with (u_sp1 cx + 12) by lia. exact V1.
  - replace (u_sp1 cx + 8 + 8) with (u_sp1 cx + 16) by lia. exact V2.
  - replace (u_sp1 cx + 8 + 12) with (u_sp1 cx + 20) by lia. exact V3.
  - replace (u_sp1 cx + 8 + 16) with (u_sp1 cx + 24) by lia. exact V4. }
(* the registers at the call *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ uci_listing PI_uci) E0 ss (restrict (w_H W) ms) regs
    (ux_ex1 v0 v1 v2 v3 v4) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
ux_reg HS (1%bv : bv 5) R1'. ux_reg HS (10%bv : bv 5) R10'. ux_reg HS (11%bv : bv 5) R11'.
cbn [ms_regs restrict] in R1', R10', R11'.
assert (R1 : YK11.getr (ms_regs ms) 1 = w64 (UCI_A_LLVMF + 0x220)) by (rewrite R1'; exact (codeptr_val E0 544 HEI)).
assert (R10 : YK11.getr (ms_regs ms) 10 = w64 (u_sp1 cx + 8)) by (rewrite R10'; cbn [sv_denot]; rewrite U2; reflexivity).
assert (R11 : YK11.getr (ms_regs ms) 11 = w64 mm)
  by (rewrite R11', (ux_soff_denot E0 18 _ (EL 18%nat 18%bv eq_refl)); exact R18).
pmkst HS.
apply (ux_call cx W (ms_regs ms) (ms_mem ms) mdA ly' S' mm v0 v1 v2 v3 v4 HP HB).
- apply (ux_core_kept cx ly' S' W regs (ms_regs ms) mem (ms_mem ms) md mdA _ HC HJ).
  + intros r Hr. apply KA. cbn [In] in Hr |- *. intuition.
  + intros a Ha. apply (aview_eq_of segs). unfold mrestrict.
    assert (Hx : ~ (u_sp1 cx + 8 <= bv_unsigned (Z_to_bv 64 a) < u_sp1 cx + 0x1c))
      by (rewrite unsigned_lit_small by (unfold u_sp1, U_FRAME, LLVMF_STK in *; lia); unfold u_sp1, U_FRAME in *; lia).
    rewrite (HM1 _ Hx). reflexivity.
- exact HM.
- exact R1.
- exact R10.
- exact R11.
- exact Hmm.
- exact Hhot.
- exact Hg.
Qed.

(* The register r of the return state against the caller's: sp = atom 2 + 0x90 = sp0, gp / tp / s11 kept by the
   frame invariant, ra and s0 .. s10 the saved words (atoms 32 .. 43). *)
Local Ltac ux_post_reg E0 EL EX U2 Hgp Htp H27 Hgp0 Htp0 :=
  lazymatch goal with
  | |- sv_denot _ (SOff 2 144) = _ =>
    cbn [sv_denot]; rewrite U2; unfold u_sp1, U_FRAME, u_sp0, spZ; rewrite Z.sub_add, Z_to_bv_bv_unsigned;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 3 0) = _ =>
    rewrite (ux_soff_denot E0 3 _ (EL 3%nat 3%bv eq_refl)), Hgp, <- Hgp0;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 4 0) = _ =>
    rewrite (ux_soff_denot E0 4 _ (EL 4%nat 4%bv eq_refl)), Htp, <- Htp0;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 27 0) = _ =>
    rewrite (ux_soff_denot E0 27 _ (EL 27%nat 27%bv eq_refl)), H27;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff ?n 0) = _ =>
    let j := eval vm_compute in (n - 32)%nat in
    let Ej := fresh "Ej" in pose proof (EX j ltac:(lia)) as Ej;
    cbn [Nat.add nth ux_ex2 map uci_saved_at snd] in Ej; rewrite (ux_soff_denot E0 n _ Ej);
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  end.

(* +0x220 .. +0x258: a0 = 0, the twelve reloads, sp += 0x90, the return; the slot post out of the journal: the journal
   with the sink token's range (t_fp_token), at most EV_LIB events, the callee-saved registers, a0 = 0, the blocks, the
   file descriptors and the file system kept (t_journal_io), the leaf LL 0 (m_fs md) [], the sink and the metadata
   kept (u_prem's up_sink_kept / up_meta_kept), the meter within XL n (u_meter 5 and up_cost), the input bytes kept
   (the journal's block clause). *)
Lemma ux_B : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> ux_st cx W c -> SRr segs W c (u_post B MT XL cx).
Proof.
intros cx W c HP HB (ly' & S' & regs & mem & md & -> & HC & Hle & Hmo).
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (ux_J_facts cx ly' S' W mem md _ HJ) as (H16 & Hceil & H47 & Hpres & _).
pose proof alloc_ceiling_val as Hce.
pose proof (@ux_seat2 (u_fx cx) rc W regs (u_regs cx) mem (u_sp0 cx) Hsp
  ltac:(unfold LLVMF_STK in *; lia) H47 H16 Hsv) as HS.
set (E0 := Eimg (PI := PI_uci) (Ereg regs (ux_ex2 (u_regs cx)))) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ uci_listing PI_uci) (SOff 21 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
assert (EX : forall j, (j < 12)%nat -> ew E0 (32 + j) = nth j (ux_ex2 (u_regs cx)) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U2 : bv_unsigned (ew E0 2) = u_sp1 cx) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
pose proof (paj_run_to (fx := u_fx cx) (SK := YE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUNTO.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + 0x220)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 600; [ux_awr_ro|].
ux_md mdB.
clear HF HFr HG.
eapply paj_ret_at; [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
unfold u_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs0 & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta
  & Hmo0).
pose proof HAFN as (HAR0 & Hret & Hra4 & Hgp0 & Htp0 & _).
ux_reg HS (1%bv : bv 5) R1'. cbn [ms_regs restrict] in R1'.
assert (E32 : ew E0 32 = YK11.getr (u_regs cx) (Z_to_bv 5 1)) by exact (EX 0%nat ltac:(lia)).
assert (R1 : YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_LLVMF).
{ rewrite R1', (ux_soff_denot E0 32 _ E32), <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned.
  first [reflexivity | f_equal; apply bv_eq; reflexivity]. }
pose proof (ajournal_materialize segs B LAWS uci_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ) as HJ3.
destruct (t_journal_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (Efd & Efs).
exists ly', S', (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdB) mat' mdB), (5 * U_EV_TURN + PK.CC_EV).
split.
{ unfold cfg_at. rewrite R1, v_jalr_lit_even by (unfold RA_LLVMF; lia). reflexivity. }
unfold tfib_lib_post_x.
refine (conj (t_fp_token _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) _).
split; [unfold U_EV_TURN, PN.CNO_EV, PV.CV_EV, PK.CC_EV, EV_LIB; lia|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr' as [->|Hr']); try subst r;
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?rr) = _ =>
    let Hq := fresh "Hq" in ux_reg HS (Z_to_bv 5 rr) Hq; cbn [ms_regs restrict] in Hq; rewrite Hq end;
  ux_post_reg E0 EL EX U2 Hgp Htp H27 Hgp0 Htp0. }
split; [ux_reg HS (10%bv : bv 5) R10'; cbn [ms_regs restrict] in R10'; rewrite R10'; reflexivity|].
split; [exact Hperm|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [cbn [YO09.ll_fs]; exact Efs|].
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [YO09.ll_fs]; exact Hfs|].
split; [exact (up_sink_kept _ _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3
  ltac:(unfold YI16.sink_open_fp, YI16.in_fp; intros (? & [] & _)) Hsink)|].
split; [exact (up_meta_kept _ _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta)|].
split.
{ apply (mo_le_mono MT ML _ _ _ _ Hle).
  assert (Hn0 : 0 <= u_n cx) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
  pose proof (up_cost _ _ _ _ _ HP (u_n cx) Hn0) as Hc. unfold uci_llvmf_cost in Hc. unfold U_TURN_COST. lia. }
intros i Hi. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 (u_p cx) (u_n cx) i Hinp).
- exact (Permutation_in _ (Permutation_sym Hperm) Hinp).
- unfold req_size. destruct (Z.eqb_spec (u_n cx) 0); lia.
- intros (rg & [] & _).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Theorem u_exit_ok : u_exit_stmt B MT XL RLO RHI.
Proof.
intros HP cx W c HB HEX.
eapply SRr_bind; [exact (ux_A cx W c HP HB HEX)|].
intros W1 c1 _ H1.
exact (ux_B cx W1 c1 HP HB H1).
Qed.
End sg.
