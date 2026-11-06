(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupC), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AD27.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedSetupC.v, with its module paths and module names changed; 1421 of its 1480 lines of code are new or changed and 596 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the skip phase, the
   walk of 0x81814 .. 0x818b4 (the cut pcs NP_sk1, NP_sk0, NP_sk_ra, NP_empty of lib/B's PcapSourceNextDefs.v).

   The record at q is longer than the caller's buffer (cap < incl). The phase starts at NP_sk1 with the predicate
   nx_sk1_inv of PcapSourceNextSkipDefs.v and ends in one of two later phases:
   - cap = 0 (`beqz s7` 0x81818, a KBig0 record): the exit join NP_exit 0x818b4, result -1, the stream at q + 16;
   - cap <> 0: the skip loop 0x8181c .. 0x81854 reads the record in chunks of min (cap, rest) bytes into the
     caller's buffer (`fread(buf, 1, chunk, f)` 0x81848). A short read (`bne a0,s8` 0x8184c, a KCutBig record) goes
     to the exit join with result -1 and the stream at its end; when the rest is 0 (`bnez s6` 0x81854 not taken, a
     KBig record) the frame's object goes out of scope (0x81858 .. 0x81860) and the run goes back to the record
     loop's head NP_loop 0x8174c with the stream at q + 16 + incl.
   The skip loop is proved by induction on the bytes of the record still to read (nx_sk0_inv).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...), disassembly nxb-next.dis (sha256 7213b94e2690; internal record). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality Zwf.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import
PcapSyms PcapList PcapAddr PcapPa PcapPaLib YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextSeat PcapSourceNextSkipDefs.
(* PcapSourceNextSkipCall.v's sk_fread_buf_post / sk_body_call: the middle state across the chunk fread. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextSkipCall.
(* PcapSourceNextHdrA.v's hdA_chain (the frame chain a body callee is handed) and hdA_keep (callee-saved registers). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrA.
(* PcapSourceNextHdrBKeep.v's hb_out / hb_kept_step / hb_body_keep / hb_mid_keep: the NP_empty landing (sk_mid_empty). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrBKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. The model's oversize records                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nxs_incl_range : forall sw F q, 0 <= PSN.incl sw F q < 2 ^ 32.
Proof.
intros sw F q. unfold PSN.incl, PSN.hw, PSN.w32le, PSN.fb.
assert (R : forall (b : byte), 0 <= bv_unsigned b < 256)
  by (intros b; pose proof (bv_unsigned_in_range 8 b) as Hb; change (bv_modulus 8) with 256 in Hb; exact Hb).
destruct sw; repeat match goal with |- context [bv_unsigned ?x] =>
  lazymatch goal with H : 0 <= bv_unsigned x < 256 |- _ => fail | _ => pose proof (R x) end end; lia.
Qed.

(* A record longer than the buffer is one of three kinds. *)
Lemma nxs_kind_big : forall sw F cap q,
  16 <= PSN.flen F - q -> PSN.incl sw F q <> 0 -> cap < PSN.incl sw F q ->
  (cap = 0 /\ PSN.kind sw F cap q = PSN.KBig0) \/
  (cap <> 0 /\ q + 16 + PSN.incl sw F q <= PSN.flen F /\ PSN.kind sw F cap q = PSN.KBig) \/
  (cap <> 0 /\ PSN.flen F < q + 16 + PSN.incl sw F q /\ PSN.kind sw F cap q = PSN.KCutBig).
Proof.
intros sw F cap q H16 Hnz Hcap. unfold PSN.kind.
destruct (Z.eqb_spec (PSN.flen F - q) 0); [lia|].
destruct (Z.ltb_spec (PSN.flen F - q) 16); [lia|].
destruct (Z.eqb_spec (PSN.incl sw F q) 0); [lia|].
destruct (Z.leb_spec (PSN.incl sw F q) cap); [lia|].
destruct (Z.eqb_spec cap 0); [left; split; [assumption | reflexivity]|].
destruct (Z.leb_spec (q + 16 + PSN.incl sw F q) (PSN.flen F)).
- right; left. auto.
- right; right. auto.
Qed.


(* The record at q ends the call (KBig0, KCutBig): the model does not go on from q. lib/A's nxs_chain_nbig /
   nxs_exit_model (lib/A/Prog/PcapSourceNextSkip.v:72-105, a working branch da0818b5f51), image-free. *)
Lemma nxs_chain_nbig : forall sw F cap f q lh,
  PSN.kind sw F cap q = PSN.KBig0 \/ PSN.kind sw F cap q = PSN.KCutBig ->
  PSN.chain sw F cap (S f) q lh = (q, [], Some q).
Proof. intros sw F cap f q lh [K|K]; cbn [PSN.chain]; rewrite K; reflexivity. Qed.

Lemma nxs_exit_model : forall sw C cap p q lh lol lvt lvid tsv,
  nx_chain_inv sw (nxF C) cap p q lh -> q <= Z.of_nat (length C) ->
  PSN.kind sw (nxF C) cap q = PSN.KBig0 \/ PSN.kind sw (nxF C) cap q = PSN.KCutBig ->
  nx_res sw C cap p = -1 /\ nx_pos sw C cap p = PSN.pos_of sw (nxF C) cap q /\
  nx_orig sw C cap p lol = PSN.orig sw (nxF C) q /\ nx_fit sw C cap p = false /\
  nx_vtag sw C cap p lvt = lvt /\ nx_vid sw C cap p lvid = lvid /\ nx_tsv sw C cap p tsv = tsv.
Proof.
intros sw C cap p q lh lol lvt lvid tsv HI Hq HK.
assert (Hq' : q <= Z.of_nat (length (nxF C))) by (rewrite nxF_length; exact Hq).
assert (K1 : PSN.kind sw (nxF C) cap q <> PSN.KEmpty) by (destruct HK as [K|K]; rewrite K; discriminate).
assert (K2 : PSN.kind sw (nxF C) cap q <> PSN.KBig) by (destruct HK as [K|K]; rewrite K; discriminate).
destruct (nx_chain_stop _ _ _ _ _ _ HI Hq' K1 K2) as [EQ ELH].
assert (ELH' : PSN.psn_lh sw (nxF C) cap p = Some q) by (rewrite ELH; destruct HK as [K|K]; rewrite K; reflexivity).
assert (EK : nx_kind sw C cap p = PSN.kind sw (nxF C) cap q) by (unfold nx_kind, nx_q; rewrite EQ; reflexivity).
assert (EF : nx_fit sw C cap p = false) by (unfold nx_fit; rewrite EK; destruct HK as [K|K]; rewrite K; reflexivity).
unfold nx_res, nx_pos, nx_orig, nx_vtag, nx_vid, nx_tsv, nx_lh, nx_q. rewrite EQ, ELH'. rewrite EF.
unfold nx_fit in EF.
split; [unfold PSN.res_of; destruct HK as [K|K]; rewrite K; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 2. Image-free helpers of the runs                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

(* A run whose regions are all read-only leaves the memory alone. *)
Lemma sk_mem_eq : forall (E : env) rs (m m' : word -> option byte),
  frame_of E rs m m' -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

(* An 8-aligned granule whose last byte is addressable has shadow byte 0 (YG0v.saddr_ok). *)
Lemma sk_shadow0 : forall (rd : Z -> option Z) a, a mod 8 = 0 ->
  range_addressable rd SHADOW_OFF a 8 -> rd (shadow_of_addr SHADOW_OFF a) = Some 0.
Proof.
intros rd a Ha HR. destruct (HR (a + 7) ltac:(lia)) as (s & Hs & Hok).
replace (shadow_of_addr SHADOW_OFF (a + 7)) with (shadow_of_addr SHADOW_OFF a) in Hs.
- destruct Hok as [-> | [H1 H2]]; [exact Hs|]. exfalso.
  assert ((a + 7) mod 8 = 7) by (rewrite Zplus_mod, Ha; reflexivity). lia.
- unfold shadow_of_addr. f_equal.
  apply (Z.div_unique (a + 7) 8 (a / 8) 7); [lia|].
  pose proof (Z_div_mod_eq_full a 8) as D. rewrite Ha, Z.add_0_r in D. lia.
Qed.

(* The shadow of an address below 2^47 lies in [SHADOW_OFF, kHighMemBeg), away from application memory. *)
Lemma sk_shadow_apart : forall x y n m, 0 <= x -> 0 <= m -> x + 8 * m <= 2 ^ 47 -> amem_range y n -> 0 <= n ->
  y + n <= shadow_of_addr SHADOW_OFF x \/ shadow_of_addr SHADOW_OFF x + m <= y.
Proof.
intros x y n m Hx0 Hm Hx Hy Hn.
assert (x / 8 <= 2 ^ 44 - m) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
unfold amem_range, shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 3. The symbolic states of the three runs                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

(* The atoms past the registers: 32 = buf, 33 = F, 34 = h (the stream). *)
Definition sk_extra (buf F h : Z) : list word := map (Z_to_bv 64) [buf; F; h].

(* The spill slots the phase reads, above the realigned stack pointer s1 (atom 9), read-only. *)
Definition SKspill : YP09.region :=
  YP09.mkRegion (Some 9%nat) NS_F0 (NS_FK + 8) 0 0
    [YP09.mkChunk NS_F0 (CVal 8 (SOff 33 0)); YP09.mkChunk NS_BUF (CVal 8 (SOff 32 0));
     YP09.mkChunk NS_FK (CVal 8 (SOff 33 0))].
(* The shadow byte of ps (atom 26 = s10), read: it is 0. *)
Definition SKshps : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* The caller's struct's FILE pointer at ps (atom 21 = s5), read. *)
Definition SKps : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
(* The frame's shadow bytes 4 and 5 (atom 25 = s9), written by NP_empty (0xf8: `ph` out of scope). *)
Definition SKfsh : YP09.region := YP09.mkRegion (Some 25%nat) 4 6 4 6 [].

Definition sk_ss_spill (pc : Z) : sstate := mkSS pc sr_atoms [SKspill] None (mkFacts [] [] []).
Definition ss_sk1 : sstate := sk_ss_spill NP_sk1.
Definition ss_sk0 : sstate := mkSS NP_sk0 sr_atoms [SKshps; SKps] None (mkFacts [] [] []).
Definition ss_skra : sstate := sk_ss_spill NP_sk_ra.

(* The registers each run leaves alone. *)
Definition SK_K_exit1 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SK_K_sk0 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SK_K_call : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SK_K_exit2 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SK_K_back : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SK_K_mid : list (bv 5) := [2; 3; 4; 8; 9; 21; 23; 25; 26; 27]%bv.
Definition SK_K_loop : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Ltac inkeep := cbv delta [SK_K_exit1 SK_K_sk0 SK_K_call SK_K_exit2 SK_K_back SK_K_loop SK_K_mid]; cbn [In];
  repeat match goal with |- _ \/ _ => first [left; reflexivity | right] end.
(* every region of a read-only run's state is read-only *)
Ltac skro := repeat first [ apply Forall_nil | apply Forall_cons;
  [cbv [SKspill SKshps SKps YP09.r_whi YP09.r_wlo]; lia|] ].
(* a register the run left holding the atom En's value, and a register holding a literal *)
Ltac skvat En := cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?En;
  first [ reflexivity | unfold w64; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity ].
Ltac skvlit := cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; apply bv_eq; vm_compute; reflexivity.
(* the struct's field offsets, for the arithmetic of a transport *)
Ltac psoff := unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia.

(* A wrapper lia does not look into: a disjunctive fact in the context makes every lia call split on it, and a
   phase context holds a dozen of them. Facts are packed when stated and unpacked where a goal needs one. *)
Definition sk_keep (P : Prop) : Prop := P.
Lemma sk_pack : forall P : Prop, P -> sk_keep P.
Proof. intros P H. exact H. Qed.
Lemma sk_unpack : forall P : Prop, sk_keep P -> P.
Proof. intros P H. exact H. Qed.

(* ---- the arithmetic of the engine's values the skip phase needs ---- *)

Lemma sk_shadow_addr_eq : forall a, shadow_addr a = shadow_of_addr SHADOW_OFF a.
Proof. intros a. reflexivity. Qed.

Lemma sk_mod64_32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. pose proof (Z_div_mod_eq_full x (2 ^ 64)) as D.
replace (x mod 2 ^ 64) with (x + (- (2 ^ 32 * (x / 2 ^ 64))) * 2 ^ 32) by lia.
apply Z_mod_plus_full.
Qed.

Lemma sk_swrap32_mod : forall y, bv_swrap 32 y mod 2 ^ 32 = y mod 2 ^ 32.
Proof.
intros y. unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* `subw a,b`: its low word is the difference of the low words. *)
Lemma sk_subw_lo : forall E a b, U E (SAluw ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite U_of_S, S_SAluw. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite sk_mod64_32, sk_swrap32_mod. cbn [zalu_raw].
rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma sk_subw_zero : forall E a b, U E a mod 2 ^ 32 = U E b mod 2 ^ 32 -> U E (SAluw ALU_SUB a b) = 0.
Proof.
intros E a b H. rewrite U_of_S, S_SAluw, H. cbn [zalu_raw].
replace (U E b mod 2 ^ 32 - U E b mod 2 ^ 32) with 0 by lia. reflexivity.
Qed.

(* x << 32: the low word of x, shifted up. *)
Lemma sk_hi32 : forall E n, U E (SAlu ALU_SLL (SOff n 0) (SLit 32)) = (bv_unsigned (ew E n) mod 2 ^ 32) * 2 ^ 32.
Proof.
intros E n. rewrite U_SAlu, U_SOff, U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 32) 63) with 32. rewrite Z.add_0_r.
pose proof (u64_range (ew E n)) as Hx.
rewrite (zcanon_id (bv_unsigned (ew E n))) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). apply Z.mul_mod_distr_r; lia.
Qed.

(* (x << 32) >> 32: the low word of x (0x8181c, 0x81820). *)
Lemma sk_lo32 : forall E n,
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = bv_unsigned (ew E n) mod 2 ^ 32.
Proof.
intros E n. rewrite U_SAlu, sk_hi32, U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 32) 63) with 32.
pose proof (Z.mod_pos_bound (bv_unsigned (ew E n)) (2 ^ 32) ltac:(lia)) as Hm.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. lia.
Qed.

(* the same values at the bit-vector level (the shape prreg leaves) *)
Lemma sk_wrap64 : forall z, bv_wrap 64 z = z mod 2 ^ 64.
Proof. intros z. reflexivity. Qed.

Lemma sk_sll_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SLL a (Z_to_bv 64 k)) = (bv_unsigned a * 2 ^ k) mod 2 ^ 64.
Proof.
intros a k Hk. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !sk_wrap64.
rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma sk_srl_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SRL a (Z_to_bv 64 k)) = bv_unsigned a / 2 ^ k.
Proof.
intros a k Hk. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !sk_wrap64.
rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma sk_add_u : forall a b : word,
  bv_unsigned (alu64 ALU_ADD a b) = (bv_unsigned a + bv_unsigned b) mod 2 ^ 64.
Proof. intros a b. unfold alu64, alu. rewrite bv_add_unsigned, sk_wrap64. reflexivity. Qed.

Lemma sk_add0_bv : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
intros x. apply bv_eq. rewrite sk_add_u, Z_to_bv_unsigned, sk_wrap64.
change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r.
pose proof (u64_range x) as Hx. apply Z.mod_small. unfold M64 in Hx. lia.
Qed.

(* (x << 32) >> 32 at the bit-vector level: the low word of x. *)
Lemma sk_lo32_bv : forall (x : word) v, bv_unsigned x mod 2 ^ 32 = v ->
  alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 32)) (Z_to_bv 64 32) = w64 v.
Proof.
intros x v Hv. apply bv_eq. rewrite sk_srl_u, sk_sll_u by lia.
pose proof (u64_range x) as Hx. unfold M64 in Hx.
pose proof (Z.mod_pos_bound (bv_unsigned x) (2 ^ 32) ltac:(lia)) as Hm.
replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by (vm_compute; reflexivity).
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
unfold w64. rewrite Z_to_bv_unsigned, sk_wrap64, Hv.
symmetry. apply Z.mod_small. rewrite <- Hv. replace (2 ^ 32 * 2 ^ 32) with (2 ^ 64) by (vm_compute; reflexivity). lia.
Qed.

Lemma sk_add0 : forall E a, U E (SAlu ALU_ADD a (SLit 0)) = U E a.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. pose proof (U_range E a). unfold M64 in *. lia.
Qed.

(* `subw x,y` at the bit-vector level: its low word is the difference of the low words. *)
Lemma sk_subw_bv : forall x y : word,
  bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) (low32 y))) mod 2 ^ 32
  = (bv_unsigned x - bv_unsigned y) mod 2 ^ 32.
Proof.
intros x y. unfold sext, alu32, alu, low32.
rewrite bv_sign_extend_unsigned. unfold bv_signed.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite sk_mod64_32.
rewrite sk_swrap32_mod.
rewrite bv_sub_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_mod by lia. rewrite <- Zminus_mod. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation VAL := (pa_val).
#[local] Abbreviation SIGMA := (pa_sigma).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNP := SRr_run_pi_AJ (PL := PL_pcap) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (PL := PL_pcap) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_pcap) B LAWS.
Let BR := paj_branch (PI := PI).

(* The machine state of a cut, in the shape the engine's seeding asks for. *)
Lemma sk_restr : forall (W3 : world SEGS) (ms3 : machine_state) pc,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  restrict (w_H W3) ms3 =
  mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS).
Proof.
intros W3 ms3 pc Hpc Hresv Hpend Hrom Hfr Hfc.
destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
  in Hpc, Hresv, Hpend, Hrom, Hfr, Hfc.
subst. reflexivity.
Qed.

(* A one-byte cell of the engine's state, as the walk's aview reads it. *)
Lemma sk_aview_of_val1 : forall (W : world SEGS) (m : word -> option byte) a v,
  0 <= v < 256 -> val_mem SEGS (rdW W m) a 1 v -> aview SEGS (w_H W) m a = Some v.
Proof.
intros W m a v Hv HV. pose proof (HV 0%nat ltac:(lia)) as H0.
cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* The model a run materializes keeps the descriptor table and the file system. *)
Lemma sk_wvb : forall vl mat md,
  m_fds (with_vm_backing vl mat md) = m_fds md /\ m_fs (with_vm_backing vl mat md) = m_fs md.
Proof. intros vl mat md. destruct md as [f [mp lz mt] io fs pr li ti]. split; reflexivity. Qed.

(* ---- the seat of a cut that reads the three spill slots (NP_sk1 0x81814, NP_sk_ra 0x8184c) ---- *)
Lemma sk_seed_spill : forall (W3 : world SEGS) (ms3 : machine_state) (pc sp1 buf F h : Z),
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 112 <= 2 ^ 64 ->
  0 <= buf < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_F0) = Some F ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_BUF) = Some buf ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_FK) = Some F ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))) (sk_ss_spill pc) (restrict (w_H W3) ms3).
Proof.
intros W3 ms3 pc sp1 buf F h Hpc Hresv Hpend Hrom Hfr Hfc R9 Hsp0 Hsp1 Hbuf HFr Hf0 Hbf Hfk.
rewrite (sk_restr W3 ms3 pc Hpc Hresv Hpend Hrom Hfr Hfc).
set (E := Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))).
assert (E9 : ew E 9 = w64 sp1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = w64 buf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = w64 F)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
unfold sk_ss_spill. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold SKspill, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  fold E. rewrite U9. unfold NS_F0, NS_BUF, NS_FK.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
      | exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hf0)].
  + apply (chunk_ok_val SEGS E _ sp1 96 8 (SOff 32 0) buf);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
      | exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hbf)].
  + apply (chunk_ok_val SEGS E _ sp1 104 8 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
      | exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hfk)].
- cbn. auto.
- split; [cbn; exact I|]. split; cbn; exact I.
Qed.

(* ---- the run 0x81814 .. (cap = 0) NP_exit / (cap <> 0) NP_sk0 ---- *)
Lemma sk_run_sk1 : forall (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
  STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 (sp1 buf F h cap : Z) (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + NP_sk1) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 112 <= 2 ^ 64 ->
  getr (ms_regs ms3) 23 = w64 cap -> 0 <= cap < 2 ^ 64 ->
  0 <= buf < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_F0) = Some F ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_BUF) = Some buf ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_FK) = Some F ->
  (cap = 0 -> forall (regs' : bvmap 5 word) (md' : Model),
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r, In r SK_K_exit1 -> getr regs' r = getr (ms_regs ms3) r) ->
     getr regs' 11 = w64 (-1) -> getr regs' 16 = w64 F -> getr regs' 19 = w64 F ->
     SRr SEGS W3 (mkCfg (mkst regs' (w64 (BASE + NP_exit)) (ms_mem ms3) (seg_rom SEGS)) md') Q) ->
  (cap <> 0 -> forall (regs' : bvmap 5 word) (md' : Model),
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r, In r SK_K_sk0 -> getr regs' r = getr (ms_regs ms3) r) ->
     getr regs' 18 = w64 buf ->
     SRr SEGS W3 (mkCfg (mkst regs' (w64 (BASE + NP_sk0)) (ms_mem ms3) (seg_rom SEGS)) md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros W3 ms3 md3 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 sp1 buf F h cap Q
  HJ Hpc Hresv Hpend Hrom Hfr Hfc R9 Hsp0 Hsp1 R23 Hcap Hbuf HFv Hf0 Hbf Hfk HK0 HK1.
pose proof (sk_seed_spill W3 ms3 NP_sk1 sp1 buf F h Hpc Hresv Hpend Hrom Hfr Hfc R9 Hsp0 Hsp1 Hbuf HFv Hf0 Hbf Hfk)
  as HS. change (sk_ss_spill NP_sk1) with ss_sk1 in HS.
set (E := Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (sk_extra buf F h)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E23 : ew E 23 = w64 cap)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 23 23%bv eq_refl); exact R23).
assert (E33 : ew E 33 = w64 F)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E32 : ew E 32 = w64 buf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
clearbody E.
paj_run_sh RUNP HS HJ.
- unfold ss_sk1, SKspill. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Hm1 : ms_mem ms = ms_mem ms3) by (apply (sk_mem_eq E _ _ _ HF); skro).
  psrr_branch_pi RUNP BR HS.
  + (* cap = 0: the exit join *)
    hc_bool Hc ltac:(fun H => rewrite (U_atom E 23 cap E23) in H by lia).
    apply Z.eqb_eq in Hc.
    paj_run_to_sh RUNTOP HS HJ NP_exit.
    * cbn [ss_mem add_cond ss_mem]. unfold ss_sk1, SKspill. cbn [ss_mem].
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      rewrite Hm2, Hm1 in HJ.
      pmkst HS. rewrite Hm2, Hm1.
      prreg HS (11%bv : bv 5) Q11. prreg HS (16%bv : bv 5) Q16. prreg HS (19%bv : bv 5) Q19.
      apply (HK0 Hc (ms_regs ms0)).
      -- exact HJ.
      -- repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
      -- repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
      -- intros r Hr. exact (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_exit1 HS HAE
           ltac:(vm_compute; reflexivity) r Hr).
      -- rewrite Q11. skvlit.
      -- rewrite Q16. skvat E33.
      -- rewrite Q19. skvat E33.
  + (* cap <> 0: the skip loop's head *)
    hc_bool Hc ltac:(fun H => rewrite (U_atom E 23 cap E23) in H by lia).
    apply Z.eqb_neq in Hc.
    paj_run_to_sh RUNTOP HS HJ NP_sk0.
    * cbn [ss_mem add_cond]. unfold ss_sk1, SKspill. cbn [ss_mem].
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      rewrite Hm2, Hm1 in HJ.
      pmkst HS. rewrite Hm2, Hm1.
      prreg HS (18%bv : bv 5) Q18.
      apply (HK1 Hc (ms_regs ms0)).
      -- exact HJ.
      -- repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
      -- repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
      -- intros r Hr. exact (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_sk0 HS HAE
           ltac:(vm_compute; reflexivity) r Hr).
      -- rewrite Q18. skvat E32.
Qed.

(* ---- the seat of NP_sk0 (0x8181c): the shadow byte of ps and the struct's FILE pointer ---- *)
Lemma sk_seed_sk0 : forall (W3 : world SEGS) (ms3 : machine_state) (ps buf F h : Z),
  ms_pc_val ms3 = w64 (BASE + NP_sk0) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 21 = w64 ps ->
  getr (ms_regs ms3) 26 = w64 (shadow_of_addr SHADOW_OFF ps) ->
  ps mod 8 = 0 -> 4096 <= ps -> ps + 8 <= 2 ^ 47 -> amem_range ps 8 -> 0 <= h < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF ps 8 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) ps 8 h ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))) ss_sk0 (restrict (w_H W3) ms3).
Proof.
intros W3 ms3 ps buf F h Hpc Hresv Hpend Hrom Hfr Hfc R21 R26 Hps8 Hps4 Hps47 Hamr Hh Hra Hv.
rewrite (sk_restr W3 ms3 NP_sk0 Hpc Hresv Hpend Hrom Hfr Hfc).
set (E := Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))).
assert (E21 : ew E 21 = w64 ps)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = w64 (shadow_of_addr SHADOW_OFF ps))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 26 26%bv eq_refl); exact R26).
assert (E34 : ew E 34 = w64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (Hsh47 : 0 <= shadow_of_addr SHADOW_OFF ps < 2 ^ 64).
{ unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia)).
  assert (ps / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (U21 : bv_unsigned (ew E 21) = ps) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = shadow_of_addr SHADOW_OFF ps)
  by (rewrite E26; apply unsigned_lit_small; lia).
(* the shadow byte of the 8-aligned, addressable granule at ps is 0 *)
assert (Hs0 : aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF ps) = Some 0)
  by (apply sk_shadow0; assumption).
assert (Hvs : val_mem SEGS (rdW W3 (ms_mem ms3)) (shadow_of_addr SHADOW_OFF ps + 0) 1 0).
{ intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r.
  unfold aview in Hs0.
  destruct (mbyte SEGS (rdW W3 (ms_mem ms3)) (shadow_of_addr SHADOW_OFF ps)) as [b0|] eqn:Hb;
    [|discriminate Hs0].
  cbn [option_map] in Hs0. injection Hs0 as Hs0. f_equal. apply bv_eq. rewrite Hs0. vm_compute. reflexivity. }
(* ps's bytes and their shadow byte are apart *)
pose proof (sk_shadow_apart ps ps 8 1 ltac:(lia) ltac:(lia) ltac:(lia) Hamr ltac:(lia)) as Dsp.
unfold ss_sk0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold SKshps, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    fold E. rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (shadow_of_addr SHADOW_OFF ps) 0 1 (SLit 0) 0);
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hvs].
  + unfold SKps, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    fold E. rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ ps 0 8 (SOff 34 0) h);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
      | rewrite Z.add_0_r; exact Hv].
- apply pairwise_disjoint_of_extents. unfold SKshps, SKps, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. fold E. rewrite U21, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- split; [cbn; exact I|]. split; cbn; exact I.
Qed.

(* ---- the run 0x8181c .. the fread of a chunk (0x81848): chunk := min (cap, rest) ---- *)
Lemma sk_run_sk0 : forall (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
  STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 (ps buf F h cap r : Z) (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + NP_sk0) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 18 = w64 buf -> 0 <= buf < 2 ^ 64 ->
  getr (ms_regs ms3) 21 = w64 ps ->
  getr (ms_regs ms3) 23 = w64 cap -> 0 <= cap < 2 ^ 32 ->
  getr (ms_regs ms3) 26 = w64 (shadow_of_addr SHADOW_OFF ps) ->
  bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = r ->
  ps mod 8 = 0 -> 4096 <= ps -> ps + 8 <= 2 ^ 47 -> amem_range ps 8 -> 0 <= h < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF ps 8 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) ps 8 h ->
  (forall (regs' : bvmap 5 word) (md' : Model),
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r0, In r0 SK_K_call -> getr regs' r0 = getr (ms_regs ms3) r0) ->
     getr regs' 1 = w64 (BASE + NP_sk_ra) ->
     getr regs' 10 = w64 buf -> getr regs' 11 = w64 1 ->
     getr regs' 12 = w64 (Z.min cap r) -> getr regs' 13 = w64 h ->
     getr regs' 24 = w64 (Z.min cap r) ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_fread))
       (ms_mem ms3) (seg_rom SEGS)) md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros W3 ms3 md3 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 ps buf F h cap r Q
  HJ Hpc Hresv Hpend Hrom Hfr Hfc R18 Hbuf R21 R23 Hcap R26 Hr Hps8 Hps4 Hps47 Hamr Hh Hra Hv HK.
pose proof (sk_seed_sk0 W3 ms3 ps buf F h Hpc Hresv Hpend Hrom Hfr Hfc R21 R26 Hps8 Hps4 Hps47 Hamr Hh
  Hra Hv) as HS.
set (E := Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (sk_extra buf F h)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E18 : ew E 18 = w64 buf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 18 18%bv eq_refl); exact R18).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = w64 cap)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 23 23%bv eq_refl); exact R23).
assert (E34 : ew E 34 = w64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (Ur : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 22 0) (SLit 32)) (SLit 32)) = r)
  by (rewrite sk_lo32, E22; exact Hr).
assert (Ucap : U E (SOff 23 0) = cap) by (apply (U_atom E 23 cap E23); lia).
assert (Hr0 : 0 <= r < 2 ^ 32) by (rewrite <- Hr; apply Z.mod_pos_bound; lia).
clearbody E.
paj_run_sh RUNP HS HJ.
- unfold ss_sk0, SKshps, SKps. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Hm1 : ms_mem ms = ms_mem ms3) by (apply (sk_mem_eq E _ _ _ HF); skro).
  psrr_branch_pi RUNP BR HS.
  + (* cap < rest: the chunk is cap *)
    hc_bool Hc ltac:(fun H => rewrite Ur, Ucap in H). apply Z.ltb_lt in Hc.
    paj_run_shc RUNP RUNC HS HJ.
    * unfold ss_sk0, SKshps, SKps. cbn [ss_mem add_cond].
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      rewrite Hm2, Hm1 in HJ.
      pmkst HS. rewrite Hm2, Hm1.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (24%bv : bv 5) Q24.
      apply (HK (ms_regs ms0)).
      -- exact HJ.
      -- repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
      -- repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
      -- intros r0 Hr0'. exact (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_call HS HAE
           ltac:(vm_compute; reflexivity) r0 Hr0').
      -- rewrite Q1. reflexivity.
      -- rewrite Q10. skvat E18.
      -- rewrite Q11. skvlit.
      -- rewrite Q12. replace (Z.min cap r) with cap by lia. skvat E23.
      -- rewrite Q13. skvat E34.
      -- rewrite Q24. replace (Z.min cap r) with cap by lia. skvat E23.
  + (* cap >= rest: the chunk is the rest *)
    hc_bool Hc ltac:(fun H => rewrite Ur, Ucap in H). apply Z.ltb_ge in Hc.
    paj_run_shc RUNP RUNC HS HJ.
    * unfold ss_sk0, SKshps, SKps. cbn [ss_mem add_cond].
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      rewrite Hm2, Hm1 in HJ.
      pmkst HS. rewrite Hm2, Hm1.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (24%bv : bv 5) Q24.
      apply (HK (ms_regs ms0)).
      -- exact HJ.
      -- repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
      -- repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
      -- intros r0 Hr0'. exact (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_call HS HAE
           ltac:(vm_compute; reflexivity) r0 Hr0').
      -- rewrite Q1. reflexivity.
      -- rewrite Q10. skvat E18.
      -- rewrite Q11. skvlit.
      -- replace (Z.min cap r) with r by lia. rewrite Q12, !sk_add0_bv.
         apply sk_lo32_bv. rewrite E22. exact Hr.
      -- rewrite Q13. skvat E34.
      -- replace (Z.min cap r) with r by lia. rewrite Q24, sk_add0_bv.
         apply sk_lo32_bv. rewrite E22. exact Hr.
Qed.



(* ---- the run 0x8184c .. : a short chunk -> NP_exit, more to read -> NP_sk0, the record skipped -> NP_loop ---- *)
Lemma sk_run_skra : forall (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
  STK sp0 FP ly S W0 mem0 md0 own0 ly3 S3 k2 (fp sp1 buf F h kk chunk r : Z)
  (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own0) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + NP_sk_ra) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 112 <= 2 ^ 64 ->
  0 <= buf < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_F0) = Some F ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_BUF) = Some buf ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_FK) = Some F ->
  getr (ms_regs ms3) 10 = w64 kk -> 0 <= kk < 2 ^ 32 ->
  getr (ms_regs ms3) 24 = w64 chunk -> 0 <= chunk < 2 ^ 32 ->
  bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = r -> chunk <= r < 2 ^ 32 ->
  getr (ms_regs ms3) 25 = w64 (shadow_addr (frame_addr ly3 NX_CID fp)) ->
  shadow_addr (frame_addr ly3 NX_CID fp) + 8 <= sp1 + NS_F0 ->
  0 <= shadow_addr (frame_addr ly3 NX_CID fp) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_addr (frame_addr ly3 NX_CID fp) + 4) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_addr (frame_addr ly3 NX_CID fp) + 5) ->
  (* a short chunk: the exit join *)
  (kk <> chunk -> forall (regs' : bvmap 5 word) (md' : Model),
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own0) ly3 S3 W3 (ms_mem ms3) md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r0, In r0 SK_K_exit2 -> getr regs' r0 = getr (ms_regs ms3) r0) ->
     getr regs' 11 = w64 (-1) -> getr regs' 16 = w64 F -> getr regs' 19 = w64 F ->
     SRr SEGS W3 (mkCfg (mkst regs' (w64 (BASE + NP_exit)) (ms_mem ms3) (seg_rom SEGS)) md') Q) ->
  (* the whole chunk, more of the record to read: back to the skip loop's head *)
  (kk = chunk -> r <> chunk -> forall (regs' : bvmap 5 word) (md' : Model),
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own0) ly3 S3 W3 (ms_mem ms3) md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r0, In r0 SK_K_back -> getr regs' r0 = getr (ms_regs ms3) r0) ->
     bv_unsigned (getr regs' 22) mod 2 ^ 32 = r - chunk ->
     SRr SEGS W3 (mkCfg (mkst regs' (w64 (BASE + NP_sk0)) (ms_mem ms3) (seg_rom SEGS)) md') Q) ->
  (* the whole record read: `ph` out of scope, back to the record loop's head *)
  (kk = chunk -> r = chunk -> forall (ms' : machine_state) (md' : Model),
     ms' = mkst (ms_regs ms') (w64 (BASE + NP_loop)) (ms_mem ms') (seg_rom SEGS) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own0) ly3 S3 W3 (ms_mem ms') md' k2 ->
     m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
     (forall r0, In r0 SK_K_loop -> getr (ms_regs ms') r0 = getr (ms_regs ms3) r0) ->
     (forall a, 0 <= a < 2 ^ 64 ->
        a <> shadow_addr (frame_addr ly3 NX_CID fp) + 4 -> a <> shadow_addr (frame_addr ly3 NX_CID fp) + 5 ->
        aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     aview SEGS (w_H W3) (ms_mem ms') (shadow_addr (frame_addr ly3 NX_CID fp) + 4) = Some 248 ->
     aview SEGS (w_H W3) (ms_mem ms') (shadow_addr (frame_addr ly3 NX_CID fp) + 5) = Some 248 ->
     mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros W3 ms3 md3 STK sp0 FP ly S W0 mem0 md0 own0 ly3 S3 k2 fp sp1 buf F h kk chunk r Q
  HJ Hpc Hresv Hpend Hrom Hfr Hfc R9 Hsp0 Hsp1 Hbuf HFv Hf0 Hbf Hfk R10 Hk0 R24 Hch0 Hr Hrch R25
  Hshsp Hsh0 Hp4 Hp5 HKX HKB HKL.
pose proof (sk_seed_spill W3 ms3 NP_sk_ra sp1 buf F h Hpc Hresv Hpend Hrom Hfr Hfc R9 Hsp0 Hsp1 Hbuf HFv
  Hf0 Hbf Hfk) as HS.
change (sk_ss_spill NP_sk_ra) with ss_skra in HS.
set (E := Eimg (Ereg (ms_regs ms3) (sk_extra buf F h))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (sk_extra buf F h)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = w64 kk)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact R10).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E24 : ew E 24 = w64 chunk)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (shadow_addr (frame_addr ly3 NX_CID fp)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 25 25%bv eq_refl); exact R25).
assert (E33 : ew E 33 = w64 F)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U10 : U E (SOff 10 0) = kk) by (apply (U_atom E 10 kk E10); lia).
assert (U24 : U E (SOff 24 0) = chunk) by (apply (U_atom E 24 chunk E24); lia).
assert (U25 : bv_unsigned (ew E 25) = shadow_addr (frame_addr ly3 NX_CID fp))
  by (rewrite E25; apply unsigned_lit_small; unfold NS_F0 in *; lia).
assert (E9 : ew E 9 = w64 sp1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl); exact R9).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U22' : bv_unsigned (ew E 22) mod 2 ^ 32 = r) by (rewrite E22; exact Hr).
assert (U22 : U E (SOff 22 0) mod 2 ^ 32 = r) by (rewrite U_SOff, Z.add_0_r, zcanon_id, E22;
  [exact Hr | pose proof (u64_range (ew E 22)); unfold M64 in *; lia]).
clearbody E.
paj_run_sh RUNP HS HJ.
- unfold ss_skra, sk_ss_spill, SKspill. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Hm1 : ms_mem ms = ms_mem ms3) by (apply (sk_mem_eq E _ _ _ HF); skro).
  psrr_branch_pi RUNP BR HS.
  + (* a0 <> chunk: the short chunk *)
    hc_bool Hc ltac:(fun H => rewrite U10, U24 in H). apply Z.eqb_neq in Hc.
    paj_run_to_sh RUNTOP HS HJ NP_exit.
    * unfold ss_skra, sk_ss_spill, SKspill. cbn [ss_mem add_cond].
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      rewrite Hm2, Hm1 in HJ. pmkst HS. rewrite Hm2, Hm1.
      prreg HS (11%bv : bv 5) Q11. prreg HS (16%bv : bv 5) Q16. prreg HS (19%bv : bv 5) Q19.
      apply (HKX Hc (ms_regs ms0)).
      -- exact HJ.
      -- repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
      -- repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
      -- intros r0 Hr0. exact (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_exit2 HS HAE
           ltac:(vm_compute; reflexivity) r0 Hr0).
      -- rewrite Q11. skvlit.
      -- rewrite Q16. skvat E33.
      -- rewrite Q19. skvat E33.
  + (* a0 = chunk: the chunk was read whole *)
    hc_bool Hc ltac:(fun H => rewrite U10, U24 in H). apply Z.eqb_eq in Hc.
    paj_run_sh RUNP HS HJ.
    * unfold ss_skra, sk_ss_spill, SKspill. cbn [ss_mem add_cond].
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
    * assert (Hm2 : ms_mem ms0 = ms_mem ms) by (apply (sk_mem_eq E _ _ _ HF0); skro).
      psrr_branch_pi RUNP BR HS.
      -- (* the rest is not 0: back to the loop's head *)
         hc_bool Hc0 ltac:(fun H => rewrite ?U24 in H). hc_prop Hc0.
         assert (Hne : r <> chunk).
         { intros Heq. apply Hc0. apply sk_subw_zero. rewrite U22, U24, Heq.
           symmetry. apply Z.mod_small. lia. }
         paj_run_to_sh RUNTOP HS HJ NP_sk0.
         ++ unfold ss_skra, sk_ss_spill, SKspill. cbn [ss_mem add_cond].
            apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
         ++ assert (Hm3 : ms_mem ms1 = ms_mem ms0) by (apply (sk_mem_eq E _ _ _ HF1); skro).
            rewrite Hm3, Hm2, Hm1 in HJ. pmkst HS. rewrite Hm3, Hm2, Hm1.
            prreg HS (22%bv : bv 5) Q22.
            apply (HKB Hc Hne (ms_regs ms1)).
            ** exact HJ.
            ** repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
            ** repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
            ** intros r0 Hr0. exact (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) (sk_extra buf F h) SK_K_back HS HAE
                 ltac:(vm_compute; reflexivity) r0 Hr0).
            ** rewrite Q22, sk_subw_bv, E24. unfold w64.
               rewrite (unsigned_lit_small chunk) by lia.
               rewrite Zminus_mod, U22', (Z.mod_small chunk) by lia.
               rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r. apply Z.mod_small. lia.
      -- (* the record is read whole: `ph` out of scope, back to the record loop *)
         hc_bool Hc0 ltac:(fun H => rewrite ?U24 in H). hc_prop Hc0.
         assert (Heq : r = chunk).
         { pose proof (sk_subw_lo E (SOff 22 0) (SOff 24 0)) as HL. rewrite Hc0 in HL.
           rewrite Zminus_mod, U22, U24, (Z.mod_small chunk (2 ^ 32)) in HL by lia.
           rewrite (Z.mod_small (r - chunk)) in HL by lia.
           change (0 mod 2 ^ 32) with 0 in HL. lia. }
         (* the frame's shadow bytes 4 and 5 become writable regions of the run *)
         assert (HRfsh : YP09.region_ok SEGS E (ms_mem (restrict (w_H W3) ms0)) SKfsh).
         { unfold SKfsh, YP09.region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val
                ms_mem restrict mkst].
           rewrite U25. split; [lia|]. split; [unfold NS_F0 in *; lia|].
           split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS).
           rewrite Hm2, Hm1. assert (o = 4 \/ o = 5) as [-> | ->] by lia; assumption. }
         pose proof (st_ok_pi_add_region E _ _ SKfsh HS ltac:(vm_compute; reflexivity) HRfsh) as HS2.
         match type of HS2 with ?T -> _ => assert (HDfsh : T) end.
         { cbn [ss_mem add_cond]. unfold SKfsh.
           cbn [YP09.all_disjoint]. split; [|exact I]. unfold YP09.extent_disjoint.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U25, U9.
           left. unfold NS_F0 in *. lia. }
         specialize (HS2 HDfsh). clear HS HDfsh. rename HS2 into HS.
         paj_run_to_sh RUNTOP HS HJ NP_loop.
         ++ cbn [ss_mem add_cond]. unfold SKfsh.
            eapply awr_ok_cons_gen; [reflexivity | exact U25 | |].
            ** cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply awr_byte_own_head_shadow.
               assert (Hfb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
               rewrite Hfb. change (64 / 8) with 8. lia.
            ** unfold ss_skra, sk_ss_spill, SKspill. cbn [ss_mem add_cond].
               apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
         ++ (* the memory: the two shadow bytes, everything else kept *)
            pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms1 HS eq_refl) as Hms1.
            cbn [ss_pc add_cond] in Hms1.
            lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
              let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
              pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W3) msx) 0 r0 HS
                ltac:(vm_compute; reflexivity)) as HR0;
              cbn [ms_mem restrict mkst] in HR0 end.
            pose proof (field_of_region_any E (rdW W3 (ms_mem ms1)) 25
               (shadow_addr (frame_addr ly3 NX_CID fp)) _ _ _ _ _ 4 1
               (SLit 18446744073709551608) HR0 U25 ltac:(cbn; tauto) ltac:(cbn; lia)) as HV4.
            pose proof (field_of_region_any E (rdW W3 (ms_mem ms1)) 25
               (shadow_addr (frame_addr ly3 NX_CID fp)) _ _ _ _ _ 5 1
               (SLit 18446744073709551608) HR0 U25 ltac:(cbn; tauto) ltac:(cbn; lia)) as HV5.
            apply (HKL Hc Heq ms1).
            ** exact Hms1.
            ** exact HJ.
            ** repeat rewrite (proj1 (sk_wvb _ _ _)); reflexivity.
            ** repeat rewrite (proj2 (sk_wvb _ _ _)); reflexivity.
            ** intros r0 Hr0. exact (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) (sk_extra buf F h)
                 SK_K_loop HS HAE ltac:(vm_compute; reflexivity) r0 Hr0).
            ** intros a Ha H4 H5. rewrite <- Hm1, <- Hm2.
               apply (aview_kept_out E _ (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha).
               intros (rg & Hin & Hrg). cbn [ss_mem add_cond In] in Hin.
               destruct Hin as [<- | Hin];
                 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val] in Hrg;
                  unfold SKfsh in Hrg;
                  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hrg; rewrite U25 in Hrg; lia |].
               revert Hin. vm_compute (fst (sym_runN_pi pcap_tpi FUEL
                 (add_cond ss_skra (mkAC BC_EQ (SOff 10 0) (SOff 24 0))))).
               cbn [ss_mem add_cond In]. intros [<- | []].
               cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hrg. lia.
            ** apply (sk_aview_of_val1 W3 (ms_mem ms1)); [lia|].
               replace 248 with (bv_unsigned (sv_denot E (SLit 18446744073709551608)) mod 2 ^ (8 * Z.of_N 1))
                 by (cbn [sv_denot]; rewrite unsigned_lit; vm_compute; reflexivity).
               exact HV4.
            ** apply (sk_aview_of_val1 W3 (ms_mem ms1)); [lia|].
               replace 248 with (bv_unsigned (sv_denot E (SLit 18446744073709551608)) mod 2 ^ (8 * Z.of_N 1))
                 by (cbn [sv_denot]; rewrite unsigned_lit; vm_compute; reflexivity).
               exact HV5.
            ** rewrite <- Hm1, <- Hm2. exact HG1.
Qed.

(* ================================================================================================ *)
(* 4. Transport across the chunk fread                                                              *)
(* ================================================================================================ *)

(* The bytes of the walk's own state that the chunk fread keeps: the machine frame above the callee's
   window, this call's frame on the side stack, the caller's struct and timestamp cell, and the shadow
   band (the wrapper restores it). *)
Definition sk_keepset (cx : ncx) (fp : Z) (a : Z) : Prop :=
  (n_sp1 cx <= a < spZ (n_regs cx)) \/
  (nF cx fp <= a < nF cx fp + NX_FRAME) \/
  (n_ps cx <= a < n_ps cx + PS_LEN) \/
  (n_ts cx <> 0 /\ n_ts cx <= a < n_ts cx + 8) \/
  (kLowMemEnd <= a < kHighShadowEnd).

Lemma sk_rdword_keep2 : forall (W W' : world SEGS) (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W') m' (a + i) = aview SEGS (w_H W) m (a + i)) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W') m') a = Some v.
Proof.
intros W W' m m' a v K Hr.
pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
pose proof (K 7 ltac:(lia)) as K7.
unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma sk_vm_keep2 : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W m) a n v -> val_mem SEGS (rdW W' m') a n v.
Proof.
intros W W' m m' a n v K HV k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)) by (apply K; lia).
exact (HV k Hk).
Qed.

Lemma sk_garr8_keep2 : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rdW W m) a l -> garr8 SEGS (rdW W' m') a l.
Proof.
intros W W' m m' a l Hk HG j Hj. destruct (HG j Hj) as [HV Hb]. split; [|exact Hb].
apply (sk_vm_keep2 W W' m m'); [|exact HV]. intros x Hx. apply Hk.
assert (Hj' : (j < length l)%nat) by exact Hj. lia.
Qed.

Lemma sk_ps_keep2 : forall (W W' : world SEGS) (m m' : word -> option byte) ps h sw ol vt vid pad,
  (forall x, ps <= x < ps + PS_LEN -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  nx_ps_at SEGS (rdW W m) ps h sw ol vt vid pad -> nx_ps_at SEGS (rdW W' m') ps h sw ol vt vid pad.
Proof.
intros W W' m m' ps h sw ol vt vid pad K (H1 & H2 & H3 & H4 & H5 & Hg & Hlen).
unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF, PS_LEN in *.
split; [apply (sk_vm_keep2 W W' m m'); [intros x Hx; apply K; psoff | exact H1]|].
split; [apply (sk_vm_keep2 W W' m m'); [intros x Hx; apply K; psoff | exact H2]|].
split; [apply (sk_vm_keep2 W W' m m'); [intros x Hx; apply K; psoff | exact H3]|].
split; [apply (sk_vm_keep2 W W' m m'); [intros x Hx; apply K; psoff | exact H4]|].
split; [apply (sk_vm_keep2 W W' m m'); [intros x Hx; apply K; psoff | exact H5]|].
split; [|exact Hlen].
apply (sk_garr8_keep2 W W' m m'); [|exact Hg].
intros x Hx. rewrite Hlen in Hx. apply K. psoff.
Qed.

Lemma sk_ra_keep2 : forall (W W' : world SEGS) (m m' : word -> option byte) a n,
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W') m' s = aview SEGS (w_H W) m s) ->
  0 <= a -> a + n <= 2 ^ 47 -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a n.
Proof.
intros W W' m m' a n Hk Ha0 Han Hn HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. rewrite <- Hs. apply Hk.
unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* A range whose bytes are all there holds some list of that length. *)
Lemma sk_garr8_build : forall (k : nat) (W : world SEGS) (mem : word -> option byte) (p : Z),
  (forall i, 0 <= i < Z.of_nat k -> exists b : byte, mbyte SEGS (rdW W mem) (p + i) = Some b) ->
  exists l, garr8 SEGS (rdW W mem) p l /\ length l = k.
Proof.
induction k as [|k IH]; intros W mem p H.
- exists []. split; [intros j Hj; cbn [length] in Hj; lia | reflexivity].
- destruct (IH W mem (p + 1) ltac:(intros i Hi; replace (p + 1 + i) with (p + (1 + i)) by lia;
    apply H; lia)) as (l & Hl & Hlen).
  destruct (H 0 ltac:(lia)) as (b & Hb). rewrite Z.add_0_r in Hb.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  exists (bv_unsigned b :: l). split; [|cbn [length]; lia].
  intros j Hj. destruct j as [|j'].
  + cbn [nth]. split; [|lia].
    intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite !Z.add_0_r, Hb.
    f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
  + cbn [length] in Hj. destruct (Hl j' ltac:(lia)) as [HV Hb'].
    cbn [nth]. split; [|exact Hb'].
    intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
    pose proof (HV 0%nat ltac:(lia)) as HV0. cbn [Z.of_nat] in HV0 |- *.
    rewrite Z.add_0_r in HV0 |- *.
    replace (p + Z.of_nat (S j')) with (p + 1 + Z.of_nat j') by lia. exact HV0.
Qed.

(* Every byte of a live block is there, so the buffer always holds some list of its length. *)
Lemma sk_garr8_of_block : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  exists l, garr8 SEGS (rdW W mem) p l /\ length l = Z.to_nat n.
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpres & _).
pose proof (req_size_pos n Hn) as (_ & Hrq).
apply (sk_garr8_build (Z.to_nat n) W mem p).
intros i Hi. destruct (Hpres (p + i) ltac:(lia)) as ((HH & b & Hb) & _).
exists b. unfold mbyte, mrestrict. rewrite HH, Hb. reflexivity.
Qed.


(* ================================================================================================ *)
(* 5. The middle state moved by a run, and the exits                                                *)
(* ================================================================================================ *)

(* A run that moves only the pc and the registers (and materializes the model) keeps nx_mid, given the registers
   it names. *)
Lemma sk_mid_regs : forall cx fp pc pc' sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 (regs' : bvmap 5 word) md',
  nx_mid B MT KS cx fp pc sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  (forall r, In r SK_K_mid -> getr regs' r = getr (ms_regs ms3) r) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_mid B MT KS cx fp pc' sh E q ol vt vid tv k2 ly3 S3 W3
    (mkst regs' (w64 (BASE + pc')) (ms_mem ms3) (seg_rom SEGS)) md'.
Proof.
intros cx fp pc pc' sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 regs' md' HM HK Hfd Hfs.
destruct HM as ((HB0 & HSL) & R21 & R23 & R26 & R27 & (Hk & Hab & Hmo & Hfd0 & Hfs0) & REST).
destruct HB0 as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & HSV & HHD & HFL & HSH & Hlen
  & R25 & HFK).
split.
{ split; [|exact HSL].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { cbn [ms_regs mkst]. split; [rewrite HK by inkeep; exact G2|]. split; [rewrite HK by inkeep; exact G8|].
    split; [rewrite HK by inkeep; exact G9|]. split; [rewrite HK by inkeep; exact G3 | rewrite HK by inkeep; exact G4]. }
  split; [exact HSV|]. split; [exact HHD|]. split; [exact HFL|]. split; [exact HSH|]. split; [exact Hlen|].
  split; [cbn [ms_regs mkst]; rewrite HK by inkeep; exact R25 | exact HFK]. }
cbn [ms_regs mkst].
split; [rewrite HK by inkeep; exact R21|]. split; [rewrite HK by inkeep; exact R23|].
split; [rewrite HK by inkeep; exact R26|]. split; [rewrite HK by inkeep; exact R27|].
split; [split; [exact Hk|]; split; [exact Hab|]; split; [exact Hmo|];
        split; [rewrite Hfd; exact Hfd0 | rewrite Hfs; exact Hfs0]|].
exact REST.
Qed.

(* nx_exit_inv from the middle state at NP_exit, for a record that ends the call with -1 (lib/A's
   nxs_exit_of_mid, lib/A/Prog/PcapSourceNextSkip.v:192-216, at lib/B's registers: the result in a1, s3 = a6 = F). *)
Lemma sk_exit_of_mid : forall cx fp q Q k2 ly3 S3 W3 ms3 md3,
  nx_mid B MT KS cx fp NP_exit NSH_ph (nx_E cx) Q (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 11 = w64 (-1) -> getr (ms_regs ms3) 19 = w64 (nF cx fp) ->
  getr (ms_regs ms3) 16 = w64 (nF cx fp) ->
  nx_res (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = -1 ->
  nx_pos (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = Q ->
  nx_orig (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lol cx) = nx_ol cx (Some q) ->
  nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = false ->
  nx_vtag (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx) = n_lvt cx ->
  nx_vid (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx) = n_lvid cx ->
  nx_tsv (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_tsv cx) = n_tsv cx ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W3 ms3 md3.
Proof.
intros cx fp q Q k2 ly3 S3 W3 ms3 md3 HM R11 R19 R16 Eres Epos Eorig Efit Evt Evid Ets.
destruct HM as (HBD & _ & _ & _ & _ & HJB & HK & _ & Hh & Hps & _ & Hsrc & _ & Hbuf & Hts).
split; [exact HBD|]. split; [exact R19|]. split; [exact R16|]. split; [exact HJB|].
unfold nx_fin_at, PcapSourceNextSpec.nx_fin. right.
split; [exact Hh|].
split; [rewrite R11, Eres; reflexivity|].
split; [exact HK|].
split; [rewrite Epos; exact Hsrc|].
split; [rewrite Eorig, Evt, Evid; exact Hps|].
split; [destruct Hbuf as (bj' & Hg & Hl); exists bj'; split; [exact Hg|]; split; [exact Hl|]; rewrite Efit;
        discriminate|].
intros Hts0. rewrite Ets. exact (proj1 (Hts Hts0)).
Qed.

(* The state at NP_sk_ra (0x8184c), right after fread(buf, 1, chunk, h) returned: r bytes of the record were to
   read before the call, chunk = min (cap, r) were asked, j = rread_k chunk |C| p came back (p the stream's position
   at the call), and the stream is at p + j. *)
Definition sk_ra_at (R : ncx -> Z -> Prop) (r : Z) (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists q lh,
    nx_next_ok R cx q /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh /\
    q + 16 <= Z.of_nat (length (n_C cx)) /\
    nx_incl cx q <> 0 /\ n_cap cx < nx_incl cx q /\ n_cap cx <> 0 /\
    0 < r <= nx_incl cx q /\ q + 16 + nx_incl cx q - r <= Z.of_nat (length (n_C cx)) /\
    nx_mid B MT KS cx fp NP_sk_ra NSH_ph (nx_E cx)
      (q + 16 + nx_incl cx q - r +
         rread_k (Z.min (n_cap cx) r) (Z.of_nat (length (n_C cx))) (q + 16 + nx_incl cx q - r))
      (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 18 = w64 (n_buf cx) /\
    getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) /\
    getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\
    bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = r /\
    getr (ms_regs ms3) 24 = w64 (Z.min (n_cap cx) r) /\
    getr (ms_regs ms3) 10 =
      w64 (rread_k (Z.min (n_cap cx) r) (Z.of_nat (length (n_C cx))) (q + 16 + nx_incl cx q - r)).

(* ================================================================================================ *)
(* 6. One turn of the skip loop                                                                      *)
(* ================================================================================================ *)

Hypothesis H_fread : afread_spec SK SEGS B KS (SIGMA PS___interceptor_trampoline_fread).
(* the stream's image cells (PSourceMeta), for PcapSourceNextHdrBKeep.v's hb_mid_keep *)
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.




(* the bytes fread delivers, counted *)
Lemma sk_len_read : forall (C : list Z) p j, 0 <= p -> 0 <= j -> p + j <= Z.of_nat (length C) ->
  Z.of_nat (length (firstn (Z.to_nat j) (skipn (Z.to_nat p) C))) = j.
Proof.
intros C p j Hp Hj Hpj. rewrite length_firstn, length_skipn.
rewrite Nat.min_l by lia. lia.
Qed.

(* the registers a run keeps, from the list it states *)
Ltac kmid HK := intros r0 Hr0; apply HK; cbv delta [SK_K_mid] in Hr0; cbn [In] in Hr0;
  repeat (destruct Hr0 as [<- | Hr0]; [inkeep|]); destruct Hr0.

(* The NP_empty stores (s9 + 4, s9 + 5 := 0xf8, 0x8185c / 0x81860) and the jump to NP_loop: the middle state with
   `ph` out of scope again (NSH_entry). Composed from hb_body_keep, hb_kept_step and hb_mid_keep
   (lib/B/Prog/PcapSourceNextHdrBKeep.v), whose three windows contain this run's two shadow bytes. *)
Lemma sk_mid_empty : forall cx fp pc0 q ol k2 ly3 S3 (W3 : world SEGS) ms3 md3 (ms' : machine_state) md',
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp pc0 NSH_ph (nx_E cx) q ol (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  ms' = mkst (ms_regs ms') (w64 (BASE + NP_loop)) (ms_mem ms') (seg_rom SEGS) ->
  (forall r, In r SK_K_mid -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> nSH cx fp + 4 -> a <> nSH cx fp + 5 ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  aview SEGS (w_H W3) (ms_mem ms') (nSH cx fp + 4) = Some 248 ->
  aview SEGS (w_H W3) (ms_mem ms') (nSH cx fp + 5) = Some 248 ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_mid B MT KS cx fp NP_loop NSH_entry (nx_E cx) q ol (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms' md'.
Proof.
intros cx fp pc0 q ol k2 ly3 S3 W3 ms3 md3 ms' md' HB HJ HFR HM Hms' HK HOUT H4 H5 HG Hfd Hfs.
destruct HM as (HBD & R21 & R23 & R26 & R27 & (Hk & Hab & Hmo & Hfd0 & Hfs0) & HKEPT & HEsub & Hh & HPS & HRA & HSRC
  & Hq & HBUF & HTS).
pose proof HBD as ((_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & _ & _ & _ & _ & _ & R25 & _) & _).
(* the two stored bytes are none of the caller's *)
pose proof (hb_out B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (nSH cx fp + 4) HB HJ HFR
  ltac:(right; clear; lia)) as (_ & _ & O4 & _).
pose proof (hb_out B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (nSH cx fp + 5) HB HJ HFR
  ltac:(right; clear; lia)) as (_ & _ & O5 & _).
assert (UNCH : forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha _ _ Hw. apply HOUT; [exact Ha | | ]; intros ->; apply Hw; clear; lia. }
assert (UNCH2 : forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha _ _ Hw. apply HOUT; [exact Ha | | ]; intros ->; apply Hw; clear; lia. }
assert (HPRES : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a)
  by (intros a Hp; eapply apresent_grows; [exact HG | exact Hp]).
assert (HSTK : forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W3) (ms_mem ms') a).
{ intros a Ha. apply HPRES. destruct HKEPT as (_ & _ & _ & _ & _ & K6). exact (K6 a Ha). }
(* the struct's orig field is not one of the two bytes: the struct lies in a caller frame *)
pose proof (nxb_psfr B KS cx HB) as (Hpsin & Hpsle & Hpshi).
assert (Hpsin' : In (n_cid cx, n_pos cx) (frames (n_Sc cx))).
{ pose proof HB as (HJ0 & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
  rewrite Hfrs0. apply in_or_app. left. exact Hpsin. }
assert (VOL : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 ol).
{ pose proof HPS as (_ & _ & V3 & _).
  intros kk Hkk. rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms')).
  - exact (V3 kk Hkk).
  - destruct (O4 _ _ Hpsin') as (N4 & _). destruct (O5 _ _ Hpsin') as (N5 & _).
    unfold in_zr, frame_rng in N4, N5. cbn [fst snd] in N4, N5.
    assert (HPL : PS_LEN = 24) by reflexivity. assert (HOL : PS_OL_OFF = 12) by reflexivity.
    apply HOUT.
    + pose proof (nxb_ps B KS cx HB) as (_ & Hp4 & H47 & _). clear - Hkk H47 Hp4 HPL HOL. lia.
    + intros E4. apply N4. clear - E4 Hkk Hpsle Hpshi HPL HOL. lia.
    + intros E5. apply N5. clear - E5 Hkk Hpsle Hpshi HPL HOL. lia. }
destruct (hb_mid_keep B KS LAWS ASIL cx fp k2 ly3 S3 W3 ms3 ms' md3 ol ol q HB HJ HFR UNCH2 Hh HPS VOL HRA HSRC HBUF HTS)
  as (HPS' & HRA' & HSRC' & HBUF' & HTS').
split.
{ apply (hb_body_keep B KS LAWS cx fp k2 ly3 S3 W3 ms3 ms' md3 pc0 NP_loop NSH_entry HB HJ HFR HBD UNCH).
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - split; [rewrite HK by inkeep; exact G2|]. split; [rewrite HK by inkeep; exact G8|].
    split; [rewrite HK by inkeep; exact G9|]. split; [rewrite HK by inkeep; exact G3 | rewrite HK by inkeep; exact G4].
  - rewrite HK by inkeep. exact R25.
  - exact H4.
  - exact H5.
  - intros i Hi N4 N5. do 8 (destruct i as [|i]; [first [reflexivity | exfalso; lia] |]). exfalso; lia.
  - reflexivity. }
split; [rewrite HK by inkeep; exact R21|]. split; [rewrite HK by inkeep; exact R23|].
split; [rewrite HK by inkeep; exact R26|]. split; [rewrite HK by inkeep; exact R27|].
split; [split; [exact Hk|]; split; [exact Hab|]; split; [exact Hmo|];
        split; [rewrite Hfd; exact Hfd0 | rewrite Hfs; exact Hfs0]|].
split; [exact (hb_kept_step B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms') HB HJ HFR UNCH HPRES HSTK
          HKEPT)|].
split; [exact HEsub|]. split; [exact Hh|].
split; [exact HPS'|]. split; [exact HRA'|]. split; [exact HSRC'|]. split; [exact Hq|].
split; [exact HBUF' | exact HTS'].
Qed.

(* From NP_sk_ra: a short chunk ends the call (KCutBig), a whole chunk with more to read goes back to NP_sk0, the
   last chunk goes through NP_empty to the record loop's head (KBig). *)
Lemma sk_ret : forall (R : ncx -> Z -> Prop) (POST : ncx -> world SEGS -> config -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 r,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  sk_ra_at R r cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall k2' ly3' S3' (W3' : world SEGS) ms3' md3' r',
     ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
       ((NX_CID, fp) :: n_own cx) ly3' S3' W3' (ms_mem ms3') md3' k2' ->
     frames S3' = (NX_CID, fp) :: frames (n_Sc cx) ->
     0 < r' < r ->
     nx_sk0_inv B MT KS R r' cx fp k2' ly3' S3' W3' ms3' md3' ->
     SRr SEGS W3' (mkCfg ms3' md3') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros R POST HLOOP HEXIT cx fp k2 ly3 S3 W3 ms3 md3 r HB HJ HFR HI HNEXT.
destruct HI as (q & lh & Hnext & Hchain & Hq16 & Hincl0 & Hcaplt & Hcap0 & Hrr & Hp0C & HM & R18 & R19 & R20 & R22
  & R24 & R10).
set (p0 := q + 16 + nx_incl cx q - r) in *.
set (chunk := Z.min (n_cap cx) r) in *.
set (j := rread_k chunk (Z.of_nat (length (n_C cx))) p0) in *.
assert (Ep0 : p0 = q + 16 + nx_incl cx q - r) by reflexivity.
assert (Echunk : chunk = Z.min (n_cap cx) r) by reflexivity.
assert (Ej : j = Z.min chunk (Z.of_nat (length (n_C cx)) - p0)) by reflexivity.
clearbody p0 chunk j.
pose proof HM as HM0.
destruct HM as (HBODY & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqrange & HBUF & HTS).
destruct HBODY as (HBODY0 & HSLOTS).
destruct HBODY0 as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW & HSH & Hshlen
  & R25 & HFK).
destruct HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HSLOTS as (L1 & L2 & L3 & _).
pose proof (nx_sp_facts B KS cx HB) as (Hspal & Hspceil & Hsp47 & Hsp1rng & Hsp1al).
pose proof (nx_F_facts B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR)
  as (HF4096 & HFceil & HFapp & HFimg & HF64 & HSHeq).
apply sk_pack in HFimg. apply sk_pack in HFapp.
pose proof (nx_SH_range B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HSH0 & HSH1 & HSH8).
pose proof asan_consts as (Hac & Hahs & Hahb & Hahe & Hlme).
pose proof (nxb_buf B KS cx HB Hh) as (HBin & Hbuf4 & Hbuf63 & Hcaprng & Hbufps).
apply sk_pack in Hbufps.
pose proof (nxs_incl_range (n_sw cx =? 1) (nxF (n_C cx)) q) as Hincl32.
change (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) with (nx_incl cx q) in Hincl32.
assert (HCAPM : NX_CAP_MAX = 2040) by reflexivity.
assert (HNSF0 : NS_F0 = 64) by reflexivity.
assert (HBUFN : nx_bufn (n_cap cx) = Z.max (n_cap cx) 1) by reflexivity.
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (Hchunk : 0 < chunk <= r /\ chunk <= n_cap cx) by lia.
assert (Hj0 : 0 <= j <= chunk) by lia.
assert (Hfsb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
assert (ESH : shadow_addr (frame_addr ly3 NX_CID fp) = nSH cx fp).
{ rewrite (nx_frame_addr_eq B KS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ). reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ NX_CID fp (proj1 HJ) ltac:(rewrite HFR; left; reflexivity))
  as (_ & _ & _ & HFSpres).
rewrite Hfsb in HFSpres. change (64 / 8) with 8 in HFSpres.
refine (sk_run_skra W3 ms3 md3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) (n_own cx) ly3 S3 k2 fp (n_sp1 cx) (n_buf cx) (nF cx fp) (n_h cx) j chunk r (POST cx)
  HJ Hpc Hresv Hpend Hrom Hfregs Hfcsr Rs1 _ _ _ _ L2 L3 L1 R10 _ R24 _ R22 _ _ _ _ _ _ _ _ _).
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- rewrite ESH. exact R25.
- rewrite ESH. lia.
- rewrite ESH. lia.
- exact (proj1 (HFSpres 4 ltac:(lia))).
- exact (proj1 (HFSpres 5 ltac:(lia))).
- (* a short chunk: the stream is at its end, KCutBig *)
  intros Hne regs' md' HJ' Hfd Hfs HK R11' R16' R19'.
  assert (Hpj : p0 + j = Z.of_nat (length (n_C cx))) by lia.
  assert (Hflen : PSN.flen (nxF (n_C cx)) = Z.of_nat (length (n_C cx))) by (unfold PSN.flen; rewrite nxF_length; reflexivity).
  assert (HKC : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KCutBig).
  { destruct (nxs_kind_big (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q ltac:(rewrite Hflen; lia) Hincl0 Hcaplt)
      as [(Hc & _) | [(_ & Hle & _) | (_ & _ & K)]].
    - lia.
    - change (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) with (nx_incl cx q) in Hle. lia.
    - exact K. }
  destruct (nxs_exit_model (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) q lh (n_lol cx) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) Hchain ltac:(lia) (or_intror HKC)) as (Eres & Epos & Eorig & Efit & Evt & Evid & Ets).
  apply (HEXIT cx fp k2 ly3 S3 W3 (mkst regs' (w64 (BASE + NP_exit)) (ms_mem ms3) (seg_rom SEGS)) md' HB HJ' HFR).
  apply (sk_exit_of_mid cx fp q (p0 + j) k2 ly3 S3 W3 _ md').
  + apply (sk_mid_regs cx fp NP_sk_ra NP_exit _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 regs' md' HM0);
      [kmid HK | exact Hfd | exact Hfs].
  + exact R11'.
  + exact R19'.
  + exact R16'.
  + exact Eres.
  + rewrite Epos. unfold PSN.pos_of. rewrite HKC, Hflen. lia.
  + rewrite Eorig. reflexivity.
  + exact Efit.
  + exact Evt.
  + exact Evid.
  + exact Ets.
- (* a whole chunk, more of the record to read: back to NP_sk0 *)
  intros Heq Hne regs' md' HJ' Hfd Hfs HK R22'.
  apply (HNEXT k2 ly3 S3 W3 (mkst regs' (w64 (BASE + NP_sk0)) (ms_mem ms3) (seg_rom SEGS)) md' (r - chunk) HJ' HFR
    ltac:(lia)).
  split; [exact Hcap0|].
  split; [cbn [ms_regs mkst]; rewrite HK by inkeep; exact R18|].
  exists q, lh. split; [exact Hnext|]. split; [exact Hchain|]. split; [exact Hq16|].
  split; [exact Hincl0|]. split; [exact Hcaplt|]. split; [lia|].
  split.
  { replace (q + 16 + nx_incl cx q - (r - chunk)) with (p0 + j) by lia.
    apply (sk_mid_regs cx fp NP_sk_ra NP_sk0 _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 regs' md' HM0);
      [kmid HK | exact Hfd | exact Hfs]. }
  cbn [ms_regs mkst].
  split; [rewrite HK by inkeep; exact R19|].
  split; [rewrite HK by inkeep; exact R20|].
  exact R22'.
- (* the whole record read: NP_empty, then the record loop's head at q + 16 + incl (KBig) *)
  intros Heq Hrc ms' md' Hms' HJ' Hfd Hfs HK HOUT H4 H5 HG.
  assert (Hpj : p0 + j = q + 16 + nx_incl cx q) by lia.
  assert (Hflen : PSN.flen (nxF (n_C cx)) = Z.of_nat (length (n_C cx))) by (unfold PSN.flen; rewrite nxF_length; reflexivity).
  assert (HKB : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KBig).
  { destruct (nxs_kind_big (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q ltac:(rewrite Hflen; lia) Hincl0 Hcaplt)
      as [(Hc & _) | [(_ & _ & K) | (_ & Hgt & _)]].
    - lia.
    - exact K.
    - change (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) with (nx_incl cx q) in Hgt. rewrite Hflen in Hgt. lia. }
  apply (HLOOP cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR).
  exists (q + 16 + nx_incl cx q), (Some q). split; [apply Hnext; lia|].
  split; [|split; [rewrite HK by inkeep; exact R19|]; split; [rewrite HK by inkeep; exact R20|]].
  + rewrite <- Hpj. rewrite ESH in HOUT, H4, H5.
    apply (sk_mid_empty cx fp NP_sk_ra (p0 + j) (nx_ol cx (Some q)) k2 ly3 S3 W3 ms3 md3 ms' md' HB HJ HFR HM0 Hms');
      [kmid HK | exact HOUT | exact H4 | exact H5 | exact HG | exact Hfd | exact Hfs].
  + apply (nx_chain_big _ _ _ _ _ _ Hchain); [rewrite nxF_length; lia | lia | exact HKB].
Qed.

Lemma sk_turn : forall (R : ncx -> Z -> Prop) (POST : ncx -> world SEGS -> config -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 r,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_sk0_inv B MT KS R r cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall k2' ly3' S3' (W3' : world SEGS) ms3' md3' r',
     ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
       ((NX_CID, fp) :: n_own cx) ly3' S3' W3' (ms_mem ms3') md3' k2' ->
     frames S3' = (NX_CID, fp) :: frames (n_Sc cx) ->
     0 < r' < r ->
     nx_sk0_inv B MT KS R r' cx fp k2' ly3' S3' W3' ms3' md3' ->
     SRr SEGS W3' (mkCfg ms3' md3') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros R POST HLOOP HEXIT cx fp k2 ly3 S3 W3 ms3 md3 r HB HJ HFR HI HNEXT.
destruct HI as (Hcap0 & R18 & q & lh & Hnext & Hchain & Hq16 & Hincl0 & Hcaplt & Hrr & HM & R19 & R20 & R22).
destruct HM as (HBODY & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqrange
  & HBUF & HTS).
pose proof HBODY as HBODYc.
destruct HBODY as (HBODY0 & HSLOTS).
destruct HBODY0 as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW & HSH & Hshlen
  & R25 & HFK).
destruct HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HJBK as (Hk2 & HBL & HMO & HFDS & HFS).
pose proof HB as HB'.
pose proof (nxb_buf B KS cx HB Hh) as (HBin & Hbuf4 & Hbuf63 & Hcaprng & Hbufps).
apply sk_pack in Hbufps.
pose proof (nxb_ps B KS cx HB) as (Hps8 & Hps4 & Hps47 & Hpsamr).
pose proof (nxb_psfr B KS cx HB) as (Hpsin & Hpsle & Hpshi).
pose proof (nx_sp_facts B KS cx HB)
  as (Hspal & Hspceil & Hsp47 & Hsp1rng & Hsp1al).
pose proof (nx_F_facts B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR)
  as (HF4096 & HFceil & HFapp & HFimg & HF64 & HSHeq).
apply sk_pack in HFimg.
pose proof (nx_SH_range B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HSH0 & HSH1 & HSH8).
pose proof asan_consts as (Hac & Hahs & Hahb & Hahe & Hlme).
(* the chunk the code reads this turn *)
assert (HSTKB : NX_STK_B = 8464) by reflexivity.
assert (HAFS : AFREAD_STK = 8192) by reflexivity.
assert (HSRCB : SRC_FILE_BLOCK = 1304) by reflexivity.
assert (HCAPM : NX_CAP_MAX = 2040) by reflexivity.
assert (HPSL : PS_LEN = 24) by reflexivity.
assert (HBUFN : nx_bufn (n_cap cx) = Z.max (n_cap cx) 1) by reflexivity.
set (chunk := Z.min (n_cap cx) r) in *.
assert (Hchunk : 0 < chunk <= r /\ chunk <= n_cap cx) by (unfold chunk; lia).
assert (Hh64 : 0 <= n_h cx < 2 ^ 64)
  by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
destruct HPS as (HPSf & HPSsw & HPSol & HPSvt & HPSvid & HPSpad & HPSlen).
refine (sk_run_sk0 W3 ms3 md3 _ _ _ _ _ _ _ _ _ ly3 S3 k2 (n_ps cx) (n_buf cx) (nF cx fp) (n_h cx)
  (n_cap cx) r (POST cx) HJ Hpc Hresv Hpend Hrom Hfregs Hfcsr R18 _ R21 R23 _ R26 R22 Hps8 Hps4 _ _
  Hh64 _ _ _).
- lia.
- lia.
- lia.
- unfold amem_range in Hpsamr |- *. lia.
- apply (range_addressable_sub (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ps cx) PS_LEN);
    [exact HRAps | lia | unfold PS_LEN; lia].
- unfold PS_F_OFF in HPSf. rewrite Z.add_0_r in HPSf. exact HPSf.
- intros regs2 md2 HJ2 Hfds2 Hfs2 HKEEP2 Q1 Q10 Q11 Q12 Q13 Q24.
  pose proof HB as (_ & _ & _ & _ & HBgp & HBtp & _ & _ & _ & _ & _ & Hspwin & Hspsp0 & _).
  pose proof (proj1 HJ) as HAR3.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstream & _).
  destruct (Hstream Hh)
    as (HFin & HBin2 & HSRC0 & HClen & Hprng & Hbufh & Hbufb & Hpsh & Hpsb & Htshb & HFPh).
  apply sk_pack in Hbufh. apply sk_pack in Hbufb. apply sk_pack in Hpsh. apply sk_pack in Hpsb.
  apply sk_pack in Htshb.
  assert (Rsp2 : getr regs2 2 = w64 (n_sp1 cx)) by (rewrite HKEEP2 by inkeep; exact Rsp).
  assert (Rs02 : getr regs2 8 = w64 (spZ (n_regs cx))) by (rewrite HKEEP2 by inkeep; exact Rs0).
  assert (Hsp1Z : spZ regs2 = n_sp1 cx)
    by (unfold spZ; rewrite Rsp2; apply unsigned_lit_small; lia).
  assert (Hs0Z : s0Z regs2 = spZ (n_regs cx))
    by (unfold s0Z; rewrite Rs02; apply unsigned_lit_small; lia).
  assert (HBLb : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite HBL; exact HBin).
  assert (HBLf : In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite HBL; exact HFin).
  assert (HBLb2 : In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B ly3 S3)) by (rewrite HBL; exact HBin2).
  (* the right to write a byte, moved to this call's journal (the same blocks, one more frame) *)
  assert (HWR : forall lo n a, lo <= a < lo + n ->
      nx_wr_ok NX_STK_B B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx)
        (n_own cx) (spZ (n_regs cx)) lo n ->
      awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B ly3 S3) ly3
        ((NX_CID, fp) :: n_own cx) a /\ ~ (spZ regs2 - AFREAD_STK <= a < spZ regs2)).
  { intros lo n a Ha HW. destruct (HW a Ha) as (HA & HNW). split;
      [|rewrite Hsp1Z; intros (Hx1 & Hx2); apply HNW; unfold NX_STK_B, AFREAD_STK in *; split; lia].
    rewrite HBL. destruct HA as [HA | [HA | [HA | (cid & pos & Hin & Hr)]]].
    - left; exact HA.
    - right; left; exact HA.
    - right; right; left; exact HA.
    - right; right; right. exists cid, pos. split; [right; exact Hin|].
      rewrite (nx_frame_addr_eq B KS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ). exact Hr. }
  assert (HraZ : 4096 <= raZ regs2).
  { unfold raZ. rewrite Q1, unsigned_lit_small by
      (pose proof pa_B_ok as (HB1 & HB2 & _); pose proof pa_base_lo; unfold NP_sk_ra; lia).
    pose proof pa_base_lo. unfold NP_sk_ra. lia. }
  eapply SRr_bind.
  { eapply (H_fread (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md2 k2 regs2 (nx_ch cx)
      (n_buf cx) chunk (n_h cx) (n_b cx) (q + 16 + nx_incl cx q - r) (n_C cx)).
    split.
    { (* afread_call *)
      split; [exact HJ2|].
      split; [rewrite Q1; apply ret_ok_codeptr_v;
              [unfold NP_sk_ra; lia | unfold NP_sk_ra; vm_compute; reflexivity]|].
      split; [exact HraZ|].
      split; [rewrite (HKEEP2 3%bv ltac:(inkeep)), Rgp; exact HBgp|].
      split; [rewrite (HKEEP2 4%bv ltac:(inkeep)), Rtp; exact HBtp|].
      split; [rewrite Hsp1Z; pose proof (Z.div_mod (n_sp1 cx) 32 ltac:(lia)) as D;
              rewrite Hsp1al, Z.add_0_r in D; rewrite D;
              replace (32 * (n_sp1 cx / 32)) with ((2 * (n_sp1 cx / 32)) * 16) by lia;
              apply Z.mod_mul; lia|].
      split; [rewrite Hsp1Z; lia|].
      split; [rewrite Hsp1Z; lia|].
      rewrite Hsp1Z, Hs0Z.
      exact (hdA_chain SK B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR (aview SEGS (w_H W3) (ms_mem ms3)) Hh
        ltac:(intros a Ha; reflexivity) HSAVED HKEPT). }
    split; [rewrite Q10; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [exact HBLf|].
    split; [exact HBLb2|].
    split.
    { left. rewrite Hsp1Z.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 HBLb2) as (_ & _ & Hce & _).
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as (_ & Hrq).
      lia. }
    split; [exact HSRC|].
    split.
    { intros a Ha. split.
      + rewrite HBL. destruct (HFPh a ltac:(exists (n_h cx, n_h cx + SRC_FILE_BLOCK); cbn; split;
          [left; reflexivity | lia])) as [HA | HA].
        * right; left. split; [exact HA|]. exists (n_h cx), SRC_FILE_BLOCK. split; [exact HFin|].
          pose proof (req_size_pos SRC_FILE_BLOCK ltac:(lia)) as (_ & Hrq).
          lia.
        * right; right; left; exact HA.
      + rewrite Hsp1Z.
        destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 HBLf) as (_ & _ & Hce & _).
        pose proof (req_size_pos SRC_FILE_BLOCK ltac:(lia)) as (_ & Hrq).
        intros (Hx1 & Hx2). lia. }
    split; [lia|].
    (* afread_dest *)
    split; [apply sk_unpack in Hbufh; destruct Hbufh; [left | right]; lia|].
    split; [apply sk_unpack in Hbufb; destruct Hbufb; [left | right]; lia|].
    split; [lia|].
    split.
    { apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (n_buf cx) (nx_bufn (n_cap cx)));
        [exact HAR3 | exact HBLb | lia |
         pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(lia)) as (_ & Hrq);
         lia]. }
    split.
    { right; right. exists (n_buf cx), (nx_bufn (n_cap cx)). split; [exact HBLb|].
      lia. }
    split.
    { intros a Ha. apply (HWR (n_buf cx) (nx_bufn (n_cap cx)) a ltac:(lia)).
      pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbf & _).
      destruct (Hbf Hh) as (_ & _ & _ & _ & _ & _ & HWbuf & _). exact HWbuf. }
    split.
    { destruct (al_shadow _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 HBLb) as (Hbs & _).
      apply (block_shadow_range _ _ (n_buf cx) (req_size (nx_bufn (n_cap cx)))); [exact Hbs | lia |].
      pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(lia)) as (_ & Hrq).
      lia. }
    intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (n_buf cx)
      (nx_bufn (n_cap cx))); [exact HAR3 | exact HBLb | lia | | lia].
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(lia)) as (_ & Hrq).
    lia. }
  (* ---- the return of the chunk fread, NP_sk_ra ---- *)
  intros W4 c4 Hle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HPRES & HKEPT4 & HPOST).
  unfold afread_post in HPOST. cbv zeta in HPOST.
  destruct HPOST as (-> & -> & R10' & HGARR & HSRC4 & _ & _ & Hfds4 & Hfs4 & HSB).
  rewrite Hsp1Z in HKEPT4.
  rewrite Q1.
  assert (Hp0C : n_p cx <= q + 16 + nx_incl cx q - r <= Z.of_nat (length (n_C cx))) by exact Hqrange.
  set (p0 := q + 16 + nx_incl cx q - r) in *.
  assert (Hj0 : 0 <= rread_k chunk (Z.of_nat (length (n_C cx))) p0 <= chunk) by (unfold rread_k; lia).
  set (j := rread_k chunk (Z.of_nat (length (n_C cx))) p0) in *.
  assert (HjC : p0 + j <= Z.of_nat (length (n_C cx))) by (unfold j, rread_k; lia).
  assert (Hp00 : 0 <= p0).
  { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
    destruct (Hst Hh) as (_ & _ & _ & _ & HpC & _). lia. }
  destruct (sk_fread_buf_post B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 W4 mem4 md4 chunk j (nx_ol cx (Some q))
    (n_lvt cx) (n_lvid cx) (n_tsv cx) (firstn (Z.to_nat j) (skipn (Z.to_nat p0) (n_C cx))) HB Hh HJ HFR HBL
    ltac:(lia) HKEPT4 HSB (proj1 HJ4) HGARR (sk_len_read (n_C cx) p0 j Hp00 (proj1 Hj0) HjC) ltac:(lia)
    HKEPT (conj HPSf (conj HPSsw (conj HPSol (conj HPSvt (conj HPSvid (conj HPSpad HPSlen)))))) HRAps HTS)
    as (HKEPT5 & HPS5 & HRA5 & HBUF5 & HTS5).
  (* the callee-saved registers are the ones at NP_sk0 (and s8 = chunk, set by the run) *)
  assert (KS2 : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv ->
            getr regs4 rr = getr (ms_regs ms3) rr).
  { intros rr Hrr0. cbn [In] in Hrr0.
    repeat (destruct Hrr0 as [<- | Hrr0];
    [ first
    [ rewrite (hdA_keep _ _ 2%bv 2 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 3%bv 3 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 4%bv 4 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 8%bv 8 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 9%bv 9 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 18%bv 18 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 19%bv 19 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 20%bv 20 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 21%bv 21 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 22%bv 22 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 23%bv 23 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 25%bv 25 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 26%bv 26 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia))
    | rewrite (hdA_keep _ _ 27%bv 27 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)) ];
      apply HKEEP2; inkeep | ]).
    destruct Hrr0. }
  assert (R24' : getr regs4 24 = w64 chunk)
    by (rewrite (hdA_keep _ _ 24%bv 24 HPRES ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia));
        exact Q24).
  apply (sk_ret R POST HLOOP HEXIT cx fp k2 ly3 S3 W4 (mkst regs4 (w64 (BASE + NP_sk_ra)) mem4 (seg_rom SEGS)) md4 r
    HB HJ4 HFR); [|exact HNEXT].
  exists q, lh.
  split; [exact Hnext|]. split; [exact Hchain|]. split; [exact Hq16|]. split; [exact Hincl0|].
  split; [exact Hcaplt|]. split; [exact Hcap0|]. split; [exact Hrr|]. split; [lia|].
  split.
  { split.
    { apply (sk_body_call B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 W4 regs4 mem4 chunk NP_sk0 NP_sk_ra NSH_ph HB Hh HJ HFR HBL
        ltac:(lia) HBODYc HKEPT4 HSB).
      intros rr Hrr0. apply KS2. cbn [In] in Hrr0 |- *. clear - Hrr0. tauto. }
    cbn [ms_regs mkst ms_mem].
    split; [rewrite KS2 by inkeep; exact R21|]. split; [rewrite KS2 by inkeep; exact R23|].
    split; [rewrite KS2 by inkeep; exact R26|]. split; [rewrite KS2 by inkeep; exact R27|].
    split; [split; [exact Hk2|]; split; [exact HBL|]; split; [exact HMO|];
            split; [rewrite Hfds4, Hfds2; exact HFDS | rewrite Hfs4, Hfs2; exact HFS]|].
    split; [exact HKEPT5|]. split; [exact HEsub|]. split; [exact Hh|].
    split; [exact HPS5|]. split; [exact HRA5|]. split; [exact HSRC4|].
    split; [change (n_p cx <= p0 + j <= Z.of_nat (length (n_C cx))); lia|].
    split; [destruct HBUF as (bj0 & Hg0 & Hl0); destruct (HBUF5 bj0 Hg0 Hl0) as (bj' & Hg' & Hl' & _ & _);
            exists bj'; split; [exact Hg' | exact Hl']|].
    exact HTS5. }
  cbn [ms_regs mkst].
  split; [rewrite KS2 by inkeep; exact R18|].
  split; [rewrite KS2 by inkeep; exact R19|].
  split; [rewrite KS2 by inkeep; exact R20|].
  split; [rewrite KS2 by inkeep; exact R22|].
  split; [exact R24'|].
  exact R10'.
Qed.

(* ================================================================================================ *)
(* 7. The skip loop, by induction on the bytes still to read, and the phase                         *)
(* ================================================================================================ *)

Lemma sk_loop : forall (R : ncx -> Z -> Prop) (POST : ncx -> world SEGS -> config -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  forall r, nx_from SK B KS POST (nx_sk0_inv B MT KS R r).
Proof.
intros R POST HLOOP HEXIT r. pattern r. apply (well_founded_induction (Zwf_well_founded 0)). clear r.
intros r IH cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
apply (sk_turn R POST HLOOP HEXIT cx fp k2 ly3 S3 W3 ms3 md3 r HB HJ HFR HI).
intros k2' ly3' S3' W3' ms3' md3' r' HJ' HFR' Hr' HI'.
apply (IH r' ltac:(unfold Zwf; lia) cx fp k2' ly3' S3' W3' ms3' md3' HB HJ' HFR' HI').
Qed.

(* The phase: from NP_sk1 (nx_sk1_inv) to the record loop's head (KBig) or the exit join (KBig0, KCutBig). *)
Theorem nxb_skip_ph : forall (POST : ncx -> world SEGS -> config -> Prop) (R : ncx -> Z -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  nx_from SK B KS POST (nx_sk1_inv B MT KS R).
Proof.
intros POST R HLOOP HEXIT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
destruct HI as (q & lh & Hnext & Hchain & Hq16 & Hincl0 & Hcaplt & HM & R19 & R20 & R22).
pose proof HM as HM0.
destruct HM as (HBODY & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqrange & HBUF & HTS).
destruct HBODY as (HBODY0 & HSLOTS).
destruct HBODY0 as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW & HSH & Hshlen
  & R25 & HFK).
destruct HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HSLOTS as (L1 & L2 & L3 & _).
pose proof (nx_sp_facts B KS cx HB) as (Hspal & Hspceil & Hsp47 & Hsp1rng & Hsp1al).
pose proof (nx_F_facts B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR)
  as (HF4096 & HFceil & HFapp & HFimg & HF64 & HSHeq).
apply sk_pack in HFimg. apply sk_pack in HFapp.
pose proof asan_consts as (Hac & Hahs & Hahb & Hahe & Hlme).
pose proof (nxb_buf B KS cx HB Hh) as (HBin & Hbuf4 & Hbuf63 & Hcaprng & Hbufps).
apply sk_pack in Hbufps.
pose proof (nxs_incl_range (n_sw cx =? 1) (nxF (n_C cx)) q) as Hincl32.
change (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) with (nx_incl cx q) in Hincl32.
assert (HCAPM : NX_CAP_MAX = 2040) by reflexivity.
assert (HBUFN : nx_bufn (n_cap cx) = Z.max (n_cap cx) 1) by reflexivity.
assert (Hflen : PSN.flen (nxF (n_C cx)) = Z.of_nat (length (n_C cx)))
  by (unfold PSN.flen; rewrite nxF_length; reflexivity).
refine (sk_run_sk1 W3 ms3 md3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 k2 (n_sp1 cx) (n_buf cx) (nF cx fp) (n_h cx) (n_cap cx) (POST cx)
  HJ Hpc Hresv Hpend Hrom Hfregs Hfcsr Rs1 _ _ R23 _ _ _ L2 L3 L1 _ _).
- lia.
- lia.
- lia.
- lia.
- lia.
- (* cap = 0: KBig0, the exit join with the stream at q + 16 *)
  intros Hc0 regs' md' HJ' Hfd Hfs HK R11' R16' R19'.
  assert (HK0 : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KBig0).
  { destruct (nxs_kind_big (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q ltac:(rewrite Hflen; lia) Hincl0 Hcaplt)
      as [(_ & K) | [(Hc & _) | (Hc & _)]]; [exact K | lia | lia]. }
  destruct (nxs_exit_model (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) q lh (n_lol cx) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) Hchain ltac:(lia) (or_introl HK0)) as (Eres & Epos & Eorig & Efit & Evt & Evid & Ets).
  apply (HEXIT cx fp k2 ly3 S3 W3 (mkst regs' (w64 (BASE + NP_exit)) (ms_mem ms3) (seg_rom SEGS)) md' HB HJ' HFR).
  apply (sk_exit_of_mid cx fp q (q + 16) k2 ly3 S3 W3 _ md').
  + apply (sk_mid_regs cx fp NP_sk1 NP_exit _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 regs' md' HM0);
      [kmid HK | exact Hfd | exact Hfs].
  + exact R11'.
  + exact R19'.
  + exact R16'.
  + exact Eres.
  + rewrite Epos. unfold PSN.pos_of. rewrite HK0. reflexivity.
  + rewrite Eorig. reflexivity.
  + exact Efit.
  + exact Evt.
  + exact Evid.
  + exact Ets.
- (* cap <> 0: the skip loop, the whole record to read *)
  intros Hc regs' md' HJ' Hfd Hfs HK R18'.
  apply (sk_loop R POST HLOOP HEXIT (nx_incl cx q) cx fp k2 ly3 S3 W3
    (mkst regs' (w64 (BASE + NP_sk0)) (ms_mem ms3) (seg_rom SEGS)) md' HB HJ' HFR).
  split; [exact Hc|]. split; [exact R18'|].
  exists q, lh. split; [exact Hnext|]. split; [exact Hchain|]. split; [exact Hq16|].
  split; [exact Hincl0|]. split; [exact Hcaplt|]. split; [lia|].
  split.
  { replace (q + 16 + nx_incl cx q - nx_incl cx q) with (q + 16) by lia.
    apply (sk_mid_regs cx fp NP_sk1 NP_sk0 _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 regs' md' HM0);
      [kmid HK | exact Hfd | exact Hfs]. }
  cbn [ms_regs mkst].
  split; [rewrite HK by inkeep; exact R19|].
  split; [rewrite HK by inkeep; exact R20|].
  rewrite HK by inkeep. exact R22.
Qed.

End c.
End b.
End a.

(* SK is explicit at every use (a Theorem Labs lane ruling 21:57Z; as lib/B/Prog/PcapSourceNextDefs.v): the closure's only global
   sink_head instance is the PLAIN build's, so an inferred SK would make the stream facts vacuous. *)
Arguments nxb_skip_ph {fx rc} SK {PI}.
(* GUARD: SK is passed by position; were it implicit again, it would land on B and this line would not compile. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) (B : asyms) =>
  nxb_skip_ph (fx := fx) (rc := rc) SK (PI := PI) B).
