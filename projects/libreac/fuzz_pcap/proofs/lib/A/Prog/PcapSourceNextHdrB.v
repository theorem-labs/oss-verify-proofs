(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the phase from the return of the
   header fread (NP_hd_ra, 0x819bc) to the record loop's head (KEmpty), the skip test (NP_sk1), the
   fit path (NP_fit) or the exit (NP_exit), over 0x819bc..0x81ac0, 0x81b00..0x81b0c and
   0x81b34..0x81b3c. Its entry predicate is nx_hdra_inv (PcapSourceNextHdrBDefs.v).

   THE CODE. 0x819bc s6 := -1; 0x819c4 `bne a0,16` -> 0x81b34 (NP_eof): `bnez a0` -> NP_exit with
   s6 = -1 (KCutH), else s6 := a0 = 0 (KEnd) and `j` NP_exit. Else the shadow check of ps + 8
   (0x819c8..0x819d0, through the slot NS_SH8; the slow compare 0x81b10 is not reached: the shadow
   byte is 0), the header bytes 8..11 into s9 (0x819d4..0x81a00, sign-extended 32-bit), ps->sw
   (`lw` through the slot NS_PS8, 0x819e8), byte-swapped when sw <> 0 (0x81a08..0x81a28);
   `beqz s9` 0x81a2c -> 0x81b00 (NP_empty): shadow 4, 5 of the frame := 0xf8 and `j` NP_loop
   (KEmpty). Else orig_len from bytes 12..15 into a3 (swapped the same way), bytes 4..7 into
   a1 a6 a4 a5 and 0..3 into a2 t1 a7 t0, the shadow check of ps + 12 (0x81a90..0x81aa8, slot
   NS_SH12), s11 := zero-extended s9, `sw a3,0(t2)` 0x81ab8 stores orig into ps->orig through the
   slot NS_PS12, and `bgeu s7,s11` 0x81abc -> NP_fit (cap >= incl), else NP_sk1 0x81ac0.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; capstone 5 disassembly of its unstripped twin,
   next.dis (sha256 06286410ee55; internal record)). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaStep PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC1g YC1h YC4b YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextSeatG PcapSourceNextSeat PcapSourceNextHdrBDefs
  PcapSourceNextSkipDefs PcapSourceNextFitADefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextWords.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the arithmetic of the header assembly (0x819d4..0x81ab0) ---- *)

Lemma nx_mod64_small : forall z, 0 <= z < 2 ^ 64 -> z mod 2 ^ 64 = z.
Proof. intros z Hz. apply Z.mod_small. exact Hz. Qed.

Lemma nx_srl_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SRL a (Z_to_bv 64 k)) = bv_unsigned a / 2 ^ k.
Proof.
  intros a k Hk. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !nx_wrap64.
  rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
  rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma nx_sllw_u : forall (a : word) k, 0 <= k < 32 ->
  bv_unsigned (sext 64 (alu32 ALU_SLL (low32 a) (low32 (Z_to_bv 64 k)))) =
  bv_wrap 64 (bv_swrap 32 ((bv_unsigned a * 2 ^ k) mod 2 ^ 32)).
Proof.
  intros a k Hk. unfold sext, alu32, alu, low32.
  rewrite bv_sign_extend_unsigned. unfold bv_signed. f_equal. f_equal.
  rewrite bv_shiftl_unsigned, bv_and_unsigned, !bv_extract_unsigned, !Z_to_bv_unsigned, !nx_wrap32, !nx_wrap64.
  rewrite !Z.shiftr_0_r. rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia.
  change (31 mod 2 ^ 32) with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

(* The record's incl_len (0x819d4..0x81a00, s9) as the code builds it without the swap. *)
Lemma nx_asm_lo : forall x0 x1 x2 x3,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  alu64 ALU_OR (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x1) (Z_to_bv 64 8)) (Z_to_bv 64 x0))
    (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x2) (Z_to_bv 64 16))
       (sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 x3)) (low32 (Z_to_bv 64 24))))) =
  Z_to_bv 64 (bv_swrap 32 (PSN.w32le x0 x1 x2 x3)).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3. apply bv_eq.
  rewrite !nx_or_u, !nx_sll_u, nx_sllw_u by lia. rewrite !Z_to_bv_unsigned, !nx_wrap64.
  rewrite !(Z.mod_small x0 (2 ^ 64)), (Z.mod_small x1 (2 ^ 64)), (Z.mod_small x2 (2 ^ 64)),
    (Z.mod_small x3 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (x1 * 2 ^ 8)), (Z.mod_small (x2 * 2 ^ 16)), (Z.mod_small (x3 * 2 ^ 24) (2 ^ 32)) by lia.
  rewrite !nx_s32 by (unfold PSN.w32le; lia).
  rewrite (Z.lor_comm (x1 * 2 ^ 8) x0), (nx_lor_add x0 (x1 * 2 ^ 8) 8) by (first [apply Z.mod_mul; lia | lia]).
  unfold PSN.w32le.
  destruct (Z.ltb_spec (x3 * 2 ^ 24) (2 ^ 31)); destruct (Z.ltb_spec (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3) (2 ^ 31)); try lia.
  - rewrite (nx_lor_add (x2 * 2 ^ 16) (x3 * 2 ^ 24) 24) by (first [apply Z.mod_mul; lia | lia]).
    rewrite (nx_lor_add (x0 + x1 * 2 ^ 8) (x2 * 2 ^ 16 + x3 * 2 ^ 24) 16); [lia | lia | lia | lia |].
    replace (x2 * 2 ^ 16 + x3 * 2 ^ 24) with ((x2 + x3 * 2 ^ 8) * 2 ^ 16) by ring. apply Z.mod_mul. lia.
  - rewrite (nx_lor_add (x2 * 2 ^ 16) (x3 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) 24); [| lia | lia | lia |].
    2: { replace (x3 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) with ((x3 + 2 ^ 40 - 2 ^ 8) * 2 ^ 24) by ring. apply Z.mod_mul. lia. }
    rewrite (nx_lor_add (x0 + x1 * 2 ^ 8) (x2 * 2 ^ 16 + (x3 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)) 16); [lia | lia | lia | lia |].
    replace (x2 * 2 ^ 16 + (x3 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)) with ((x2 + x3 * 2 ^ 8 + 2 ^ 48 - 2 ^ 16) * 2 ^ 16) by ring.
    apply Z.mod_mul. lia.
Qed.


Lemma nx_u_s32 : forall v, 0 <= v < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 v)) = if v <? 2 ^ 31 then v else v + 2 ^ 64 - 2 ^ 32.
Proof. intros v Hv. rewrite Z_to_bv_unsigned, nx_wrap64. apply nx_s32. exact Hv. Qed.

(* The byte-swapped incl_len (0x81a08..0x81a28), from the unswapped word V in s9. *)
Lemma nx_asm_sw : forall x0 x1 x2 x3,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  forall V : word, V = Z_to_bv 64 (bv_swrap 32 (PSN.w32le x0 x1 x2 x3)) ->
  alu64 ALU_OR
    (alu64 ALU_OR (sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 x0)) (low32 (Z_to_bv 64 24))))
       (alu64 ALU_SLL (alu64 ALU_AND V (Z_to_bv 64 65280)) (Z_to_bv 64 8)))
    (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x2) (Z_to_bv 64 8))
       (sext 64 (alu32 ALU_SRL (low32 V) (low32 (Z_to_bv 64 24))))) =
  Z_to_bv 64 (bv_swrap 32 (PSN.w32le x3 x2 x1 x0)).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3 V EV. apply bv_eq.
  assert (UV : bv_unsigned V = if PSN.w32le x0 x1 x2 x3 <? 2 ^ 31 then PSN.w32le x0 x1 x2 x3
                               else PSN.w32le x0 x1 x2 x3 + 2 ^ 64 - 2 ^ 32)
    by (rewrite EV; apply nx_u_s32; unfold PSN.w32le; lia).
  assert (A1 : Z.land (bv_unsigned V) 65280 = x1 * 256).
  { rewrite nx_land_ff00 by (rewrite UV; destruct (_ <? _); unfold PSN.w32le; lia).
    rewrite UV. unfold PSN.w32le. destruct (_ <? _); Z.div_mod_to_equations; lia. }
  assert (A3 : bv_unsigned V mod 2 ^ 32 / 2 ^ 24 = x3).
  { rewrite UV. unfold PSN.w32le. destruct (_ <? _); Z.div_mod_to_equations; lia. }
  rewrite !nx_or_u, !nx_sll_u, nx_and_u, nx_sllw_u, nx_srlw_u by lia.
  rewrite A3. rewrite !Z_to_bv_unsigned, !nx_wrap64.
  replace (65280 mod 2 ^ 64) with 65280 by reflexivity. rewrite A1.
  rewrite !(Z.mod_small x0 (2 ^ 64)), (Z.mod_small x2 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (x0 * 2 ^ 24) (2 ^ 32)), (Z.mod_small (x1 * 256 * 2 ^ 8)), (Z.mod_small (x2 * 2 ^ 8)) by lia.
  rewrite (nx_s32_lo x3) by lia. rewrite !nx_s32 by (unfold PSN.w32le; lia).
  unfold PSN.w32le.
  rewrite (Z.lor_comm (x2 * 2 ^ 8) x3), (nx_lor_add x3 (x2 * 2 ^ 8) 8) by (first [apply Z.mod_mul; lia | lia]).
  destruct (Z.ltb_spec (x0 * 2 ^ 24) (2 ^ 31)); destruct (Z.ltb_spec (x3 + 256 * x2 + 65536 * x1 + 16777216 * x0) (2 ^ 31)); try lia.
  - rewrite (Z.lor_comm (x0 * 2 ^ 24) (x1 * 256 * 2 ^ 8)), (nx_lor_add (x1 * 256 * 2 ^ 8) (x0 * 2 ^ 24) 24)
      by (first [apply Z.mod_mul; lia | lia]).
    rewrite (Z.lor_comm (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) (x3 + x2 * 2 ^ 8)),
      (nx_lor_add (x3 + x2 * 2 ^ 8) (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) 16); [lia | lia | lia | lia |].
    replace (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) with ((x1 + x0 * 2 ^ 8) * 2 ^ 16) by ring. apply Z.mod_mul. lia.
  - rewrite (Z.lor_comm (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) (x1 * 256 * 2 ^ 8)),
      (nx_lor_add (x1 * 256 * 2 ^ 8) (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) 24); [| lia | lia | lia |].
    2: { replace (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) with ((x0 + 2 ^ 40 - 2 ^ 8) * 2 ^ 24) by ring. apply Z.mod_mul. lia. }
    rewrite (Z.lor_comm (x1 * 256 * 2 ^ 8 + (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)) (x3 + x2 * 2 ^ 8)),
      (nx_lor_add (x3 + x2 * 2 ^ 8) (x1 * 256 * 2 ^ 8 + (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)) 16); [lia | lia | lia | lia |].
    replace (x1 * 256 * 2 ^ 8 + (x0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)) with ((x1 + x0 * 2 ^ 8 + 2 ^ 48 - 2 ^ 16) * 2 ^ 16) by ring.
    apply Z.mod_mul. lia.
Qed.

(* s11 := zero-extension of s9 (0x81aac, 0x81ab0). *)
Lemma nx_zext32 : forall v, 0 <= v < 2 ^ 32 ->
  alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 (bv_swrap 32 v)) (Z_to_bv 64 32)) (Z_to_bv 64 32) = Z_to_bv 64 v.
Proof.
  intros v Hv. apply bv_eq. rewrite nx_srl_u, nx_sll_u by lia. rewrite nx_u_s32 by lia.
  rewrite Z_to_bv_unsigned, nx_wrap64, (Z.mod_small v) by lia.
  destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite (Z.mod_small (v * 2 ^ 32)) by lia. rewrite Z.div_mul by lia. reflexivity.
  - rewrite <- (Z.mod_unique ((v + 2 ^ 64 - 2 ^ 32) * 2 ^ 32) (2 ^ 64) (2 ^ 32 - 1) (v * 2 ^ 32)) by lia.
    rewrite Z.div_mul by lia. reflexivity.
Qed.

(* ---- the header bytes and the model ---- *)

(* The header byte j as the fread left it in `ph`. *)
Definition nx_hb (C : list Z) (q : Z) (j : nat) : Z := nth j (nx_hdr C q) 0.

Lemma nx_hk_16 : forall C q, 16 <= Z.of_nat (length C) - q -> nx_hk C q = 16.
Proof. intros C q H. unfold nx_hk, NX_PH_LEN. lia. Qed.

Lemma nx_hdr_len16 : forall C q, 0 <= q -> 16 <= Z.of_nat (length C) - q -> length (nx_hdr C q) = 16%nat.
Proof.
  intros C q Hq H. unfold nx_hdr. rewrite nx_hk_16 by exact H.
  rewrite length_firstn, length_skipn. lia.
Qed.

(* The model's byte q + j of the file is the header byte j (j < 16), given that the bytes are bytes. *)
Lemma nx_fb_hb : forall C q j, 0 <= q -> 16 <= Z.of_nat (length C) - q -> (j < 16)%nat ->
  0 <= nx_hb C q j < 256 ->
  PSN.fb (nxF C) (q + Z.of_nat j) = nx_hb C q j.
Proof.
  intros C q j Hq H Hj Hb. unfold PSN.fb, nxF, bytesZ, nx_hb in *.
  unfold nx_hdr in *. rewrite nx_hk_16 in * by exact H.
  rewrite nth_firstn in Hb |- *.
  replace (j <? Z.to_nat 16)%nat with true in * by (symmetry; apply Nat.ltb_lt; change (Z.to_nat 16) with 16%nat; lia).
  rewrite nth_skipn in Hb |- *.
  change (Z_to_bv 8 0) with ((fun z : Z => Z_to_bv 8 z) 0). rewrite map_nth.
  replace (Z.to_nat (q + Z.of_nat j)) with (Z.to_nat q + j)%nat by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hb.
Qed.

Lemma nx_hw_hb : forall sw C q j, 0 <= q -> 16 <= Z.of_nat (length C) - q -> (j + 3 < 16)%nat ->
  (forall i, (i < 16)%nat -> 0 <= nx_hb C q i < 256) ->
  PSN.hw sw (nxF C) q (Z.of_nat j) =
  if sw then PSN.w32le (nx_hb C q (j + 3)) (nx_hb C q (j + 2)) (nx_hb C q (j + 1)) (nx_hb C q j)
  else PSN.w32le (nx_hb C q j) (nx_hb C q (j + 1)) (nx_hb C q (j + 2)) (nx_hb C q (j + 3)).
Proof.
  intros sw C q j Hq H Hj HB. unfold PSN.hw.
  replace (q + Z.of_nat j + 3) with (q + Z.of_nat (j + 3)) by lia.
  replace (q + Z.of_nat j + 2) with (q + Z.of_nat (j + 2)) by lia.
  replace (q + Z.of_nat j + 1) with (q + Z.of_nat (j + 1)) by lia.
  rewrite !nx_fb_hb by (try apply HB; lia). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bytes the phase may change, and what that leaves of the middle state                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* Two class-0-aligned frames whose ranges are apart have shadow ranges apart. *)
Lemma hb_shadow_apart : forall F G n a, F mod 64 = 0 -> G mod 8 = 0 -> n mod 8 = 0 ->
  0 <= F -> 0 <= G -> 0 <= n -> (F + 64 <= G \/ G + n <= F) ->
  SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8 ->
  SHADOW_OFF + G / 8 <= a < SHADOW_OFF + G / 8 + n / 8 -> False.
Proof. intros F G n a HF HG Hn H0 H1 H2 Hd Ha Hb. Z.div_mod_to_equations. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.


(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic state of the phase                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* The phase's own atoms (PcapSourceNextSeat.v leaves 33..59 to the phases): 33 the shadow byte of
   ps + 8 and ps + 12 (one granule: ps is 8-aligned), 34 + j the header byte j, 50 ps->f,
   51 ps->sw, 52 ps->orig. *)
Definition HB_SHP : nat := 33%nat.
Definition HB_H : nat := 50%nat.
Definition HB_SW : nat := 51%nat.
Definition HB_OL : nat := 52%nat.

Definition hb_v (cx : ncx) (q : Z) (lh : option Z) (i : nat) : Z :=
  if (i =? 33)%nat then shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)
  else if (i <? 50)%nat then nx_hb (n_C cx) q (i - 34)
  else if (i =? 50)%nat then n_h cx
  else if (i =? 51)%nat then n_sw cx
  else nx_ol cx lh.

Definition hb_E (cx : ncx) (fp : Z) (regs : bvmap 5 word) (q : Z) (lh : option Z) : env :=
  {| ew := fun i => if ((33 <=? i) && (i <? 53))%nat then Z_to_bv 64 (hb_v cx q lh i)
                    else ew (nx_mkE cx fp regs) i;
     ed := ed (nx_mkE cx fp regs) |}.

Lemma hb_E_other : forall cx fp regs q lh i, (i < 33 \/ 53 <= i)%nat ->
  ew (hb_E cx fp regs q lh) i = ew (nx_mkE cx fp regs) i.
Proof.
  intros cx fp regs q lh i Hi. cbn [hb_E ew].
  replace ((33 <=? i) && (i <? 53))%nat with false; [reflexivity|].
  symmetry. destruct Hi; [apply andb_false_intro1; apply Nat.leb_gt | apply andb_false_intro2; apply Nat.ltb_ge]; lia.
Qed.

Lemma hb_E_mine : forall cx fp regs q lh i, (33 <= i < 53)%nat ->
  ew (hb_E cx fp regs q lh) i = Z_to_bv 64 (hb_v cx q lh i).
Proof.
  intros cx fp regs q lh i Hi. cbn [hb_E ew].
  replace ((33 <=? i) && (i <? 53))%nat with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma hb_E_env : forall cx fp regs q lh, nx_env cx fp (hb_E cx fp regs q lh).
Proof.
  intros cx fp regs q lh. pose proof (nx_mkE_env cx fp regs) as (AG & H32 & H60 & HF & HFL & HFSH).
  unfold nx_env. unfold NA_SB, NA_SP1, NA_F, NA_FL, NA_FSH in *.
  rewrite !hb_E_other by lia.
  repeat split; try assumption. intros n Hn. rewrite hb_E_other by lia. exact (AG n Hn).
Qed.

Lemma hb_E_img : forall cx fp regs q lh, img_env VAL A_LIM (hb_E cx fp regs q lh).
Proof.
  intros cx fp regs q lh a Ha. rewrite hb_E_other by (unfold A_TEXT in Ha; lia).
  exact (nx_mkE_img cx fp regs a Ha).
Qed.

(* The symbolic registers: a Theorem Labs lane's standard file, but s10 = F + 32, the base of the header loads
   (0x819d4..0x81aa4 `lbu ..(s10)`). *)
Definition hb_sr : list sv := Eval vm_compute in sr_set nx_sr (26%bv : bv 5) (SOff NA_F NO_PH).

(* The header bytes as chunks of the frame region, at F + 32 + j. *)
Definition hb_fcs : list YP09.chunk :=
  Eval vm_compute in map (fun j => YP09.mkChunk (NO_PH + Z.of_nat j) (CVal 1 (SOff (34 + j) 0))) (seq 0 16).
(* The struct's first 16 bytes (f, sw, orig) and the granule of shadow of ps + 8 .. ps + 15. *)
Definition hb_pcs : list YP09.chunk :=
  [ YP09.mkChunk PS_F_OFF (CVal 8 (SOff HB_H 0)); YP09.mkChunk PS_SW_OFF (CVal 4 (SOff HB_SW 0));
    YP09.mkChunk PS_OL_OFF (CVal 4 (SOff HB_OL 0)) ].
Definition hb_shp_region : YP09.region := YP09.mkRegion (Some HB_SHP) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition hb_extra : YP09.smem := [nx_ps_region 16 hb_pcs; hb_shp_region].
(* The facts: the fixed part's, the header bytes are bytes, sw is 0 or 1, and the two shadow
   addresses the slots NS_SH8 / NS_SH12 hold are the atom 33 (the plain engine resolves the `lb`
   at 0x819cc and 0x81a94 through them). *)
Definition hb_G : facts :=
  mkFacts (f_atoms nx_facts0 ++ (HB_SW, mkAF 0 1 0) :: map (fun j => ((34 + j)%nat, mkAF 0 255 0)) (seq 0 16)) []
    [ (SAlu ALU_ADD (nx_shx (SOff NA_PS PS_SW_OFF)) (SLit 0), SOff HB_SHP 0);
      (SAlu ALU_ADD (nx_shx (SOff NA_PS PS_OL_OFF)) (SLit 0), SOff HB_SHP 0) ].
Definition hb_ss : sstate := nx_ss NP_hd_ra hb_sr true NSH_ph 4 6 0 hb_fcs hb_extra hb_G.
(* The short read (k <> 16) reads neither the header nor the struct. *)
Definition hb_ss0 : sstate := nx_ss NP_hd_ra nx_sr true NSH_ph 0 0 0 [] [] nx_facts0.

(* The bytes this phase may write: its stack window (the spill slots), the first 16 bytes of the
   caller's struct (ps->orig at 0x81ab8; the window also holds ps->f and ps->sw, which the phase
   reads) and the shadow of its own frame (`ph` out of scope at 0x81b04, 0x81b08). *)
Definition hb_wr (cx : ncx) (fp : Z) (a : Z) : Prop :=
  (spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) \/ (n_ps cx <= a < n_ps cx + 16) \/
  (nSH cx fp <= a < nSH cx fp + 8).

Section d.
Variable cx : ncx.
Variable fp k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
#[local] Notation m3 := (ms_mem ms3).
Hypothesis HB : nx_base SK B KS cx.
Hypothesis HJ : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
  (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HFR : frames S3 = (NX_CID, fp) :: frames (n_Sc cx).

Lemma hb_J : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.

Lemma hb_frame_addr_eq : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p.
Proof.
  intros c p. pose proof HJ as (_ & Hly3 & _). pose proof hb_J as (_ & Hlyc & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  unfold frame_addr. rewrite EF3, EFc. reflexivity.
Qed.

Lemma hb_in_frames : forall c p, In (c, p) (n_own cx) -> In (c, p) (frames (n_Sc cx)).
Proof.
  intros c p H. pose proof hb_J as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact H.
Qed.


Ltac hb_base := let H := fresh in pose proof HB as H; unfold nx_base in H; decompose [and] H.

Lemma hb_psfr : In (n_cid cx, n_pos cx) (n_own cx) /\ frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) /\
  n_ps cx mod 8 = 0 /\ 4096 <= n_ps cx /\ n_ps cx + PS_LEN <= 2 ^ 47.
Proof. hb_base. repeat split; assumption. Qed.

Lemma hb_buf : n_h cx <> 0 ->
  In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  (n_buf cx + nx_bufn (n_cap cx) <= n_ps cx \/ n_ps cx + PS_LEN <= n_buf cx) /\ 0 <= n_cap cx <= NX_CAP_MAX.
Proof.
  intros Hh. hb_base.
  match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ => destruct (H Hh) as (B1 & _ & _ & _ & _ & B6 & _ & B8) end.
  repeat split; try assumption; lia.
Qed.

Lemma hb_stream : n_h cx <> 0 ->
  In (n_h cx, SRC_FILE_BLOCK) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  (n_ps cx + PS_LEN <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_ps cx) /\
  (n_ps cx + PS_LEN <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_ps cx) /\
  Z.of_nat (length (n_C cx)) < 2 ^ 26 /\ 0 <= n_p cx.
Proof.
  intros Hh. hb_base.
  match goal with H : n_h cx <> 0 -> In (n_h cx, SRC_FILE_BLOCK) _ /\ _ |- _ =>
    destruct (H Hh) as (S1 & S2 & _ & S4 & S5 & _ & _ & S8 & S9 & _) end.
  repeat split; try assumption; lia.
Qed.

Lemma hb_tsfr : n_h cx <> 0 -> n_ts cx <> 0 ->
  (exists tcid tpos, In (tcid, tpos) (n_own cx) /\ frame_addr (n_lyc cx) tcid tpos <= n_ts cx /\
     n_ts cx + 8 <= frame_addr (n_lyc cx) tcid tpos + fs_frame_bytes tcid) /\
  (n_ts cx + 8 <= n_ps cx \/ n_ps cx + PS_LEN <= n_ts cx) /\ 4096 <= n_ts cx.
Proof.
  intros Hh Ht. hb_base.
  match goal with H : n_h cx <> 0 -> n_ts cx <> 0 -> _ |- _ =>
    destruct (H Hh Ht) as (_ & _ & T3 & _ & _ & T6 & _ & _ & T9 & _) end.
  split; [exact T6|]. split; [exact T9 | exact T3].
Qed.

(* The own frame and a caller frame are apart. *)
Lemma hb_frames_apart : forall c p, In (c, p) (frames (n_Sc cx)) ->
  nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp.
Proof.
  intros c p Hin. pose proof HJ as (HAR3 & _).
  apply in_split in Hin as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 m3 md3 (NX_CID, fp) (c, p) [] l2 l3 HAR3
    ltac:(rewrite HFR, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !hb_frame_addr_eq in Hd.
  assert (Hfb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity). rewrite Hfb in Hd.
  unfold nF. lia.
Qed.

Lemma hb_geo :
  alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\
  spZ (n_regs cx) - 240 <= n_sp1 cx <= spZ (n_regs cx) - 224 /\
  4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ in_app (nF cx fp) 64 /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  SHADOW_OFF + 512 <= nSH cx fp /\ nSH cx fp + 8 <= kHighMemBeg.
Proof.
  pose proof HB as HB'. unfold nx_base in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
  pose proof hb_J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (Hac & _ & HHB & _ & _).
  pose proof HJ as (HAR3 & _).
  assert (Hin : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 Hin) as (HF0 & HFc & HFia).
  pose proof (frame_al64 SEGS B ly3 S3 W3 m3 md3 NX_CID fp HAR3 Hin) as (H64 & _).
  assert (Hfb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
  unfold nSH, nF, shadow_of_addr. rewrite <- hb_frame_addr_eq. rewrite Hfb in HFc, HFia.
  unfold n_sp1, nx_sp1, NX_MFRAME.
  assert (Hx : 0 <= spZ (n_regs cx) - 224) by (unfold NX_STK, AFREAD_STK in *; lia).
  pose proof (Z.div_mod (spZ (n_regs cx) - 224) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)) as Hmp.
  pose proof (Z.div_mod (spZ (n_regs cx)) 16 ltac:(lia)) as Hd16.
  assert (Hm : (spZ (n_regs cx) - 224) mod 32 = 0 \/ (spZ (n_regs cx) - 224) mod 32 = 16) by (rewrite Hal in Hd16; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  assert (D0 : 512 <= frame_addr ly3 NX_CID fp / 8) by (apply Z.div_le_lower_bound; lia).
  assert (D1 : frame_addr ly3 NX_CID fp / 8 + 8 <= (frame_addr ly3 NX_CID fp + 64) / 8)
    by (replace (frame_addr ly3 NX_CID fp + 64) with (frame_addr ly3 NX_CID fp + 8 * 8) by lia;
        rewrite Z.div_add by lia; lia).
  assert (D2 : (frame_addr ly3 NX_CID fp + 64) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  change (2 ^ 47 / 8) with 17592186044416 in D2.
  unfold NX_STK, AFREAD_STK in *. unfold SHADOW_OFF. repeat split; lia.
Qed.

(* The caller's frame a byte of its struct (or of its timestamp cell) lies in, and the geometry
   of that frame. *)
Lemma hb_geo_frame : forall c p x n, In (c, p) (n_own cx) ->
  frame_addr (n_lyc cx) c p <= x -> x + n <= frame_addr (n_lyc cx) c p + fs_frame_bytes c -> 0 <= n ->
  4096 <= frame_addr (n_lyc cx) c p /\ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= alloc_ceiling /\
  in_app (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) /\
  off_img (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) /\
  frame_addr (n_lyc cx) c p mod 64 = 0 /\ fs_frame_bytes c mod 64 = 0 /\
  (nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp).
Proof.
  intros c p x n Hown Hlo Hhi Hn.
  pose proof (hb_in_frames c p Hown) as Hin. pose proof HJ as (HAR3 & _).
  assert (Hin3 : In (c, p) (frames S3)) by (rewrite HFR; right; exact Hin).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR3 Hin3) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 m3 md3 c p HAR3 Hin3) as HFo.
  pose proof (frame_al64 SEGS B ly3 S3 W3 m3 md3 c p HAR3 Hin3) as (H64 & H64b & _).
  rewrite hb_frame_addr_eq in HF0, HFc, HFia, HFo, H64.
  pose proof (hb_frames_apart c p Hin) as Hap.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  split; [exact H64|]. split; [exact H64b | exact Hap].
Qed.


(* ---- what the caller's memory keeps across the phase's writes ---- *)
Section e.
Variable m' : word -> option byte.
Hypothesis HV : forall a, 0 <= a < 2 ^ 64 -> ~ hb_wr cx fp a ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m3 a.
Hypothesis HP : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) m' a.

Lemma hb_shadow_not_app : forall a, nSH cx fp <= a < nSH cx fp + 8 ->
  kLowShadowBeg + 4096 <= a /\ a < kHighMemBeg.
Proof.
  intros a Ha. pose proof hb_geo as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma hb_kept_step : forall E,
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m3 (spZ (n_regs cx)) E ->
  (forall a, n_ps cx <= a < n_ps cx + 16 -> E a) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m' (spZ (n_regs cx)) E.
Proof.
  intros E (K1 & K2 & K3 & K4 & K5 & K6) HE.
  pose proof hb_geo as (Hsp & Hsp47 & _ & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  pose proof asan_consts as (Hac & _ & HHB & _ & HLME).
  pose proof hb_J as (HARc & _).
  assert (Hsha : forall a, nSH cx fp <= a < nSH cx fp + 8 -> kLowShadowBeg + 4096 <= a < kHighMemBeg)
    by exact hb_shadow_not_app.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hs He. rewrite <- (K1 a Ha Hs He). apply HV; [lia|].
    intros [Hw | [Hw | Hw]]; [exact (Hs Hw) | exact (He (HE a Hw)) | pose proof (Hsha a Hw); unfold kHighMemBeg in *; lia].
  - intros b mm i Hb Hi He. rewrite <- (K2 b mm i Hb Hi He).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HARc Hb) as (_ & Hb4 & Hbc & Hbia & _).
    apply HV; [lia|].
    intros [Hw | [Hw | Hw]]; [lia | exact (He (HE _ Hw)) |].
    pose proof (Hsha _ Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - intros a Hi Ho Her. rewrite <- (K3 a Hi Ho Her).
    pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
    apply HV; [unfold kLowMemEnd in Hr2; lia|].
    pose proof (hb_geo_frame (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN) as G.
    pose proof hb_psfr as (Hown & Hpsl & Hpsh & Hps8 & Hps4 & Hps47).
    destruct (G Hown Hpsl Hpsh ltac:(unfold PS_LEN; lia)) as (_ & _ & _ & Hoff & _).
    intros [Hw | [Hw | Hw]]; [lia | unfold off_img, PS_LEN, pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *; lia |].
    pose proof (Hsha _ Hw). unfold kLowShadowBeg, kLowMemEnd in *. lia.
  - intros cid pos a Hin Hr He. rewrite <- (K4 cid pos a Hin Hr He).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hin) as (Hg4 & Hgc & Hgia).
    pose proof (frame_al64 SEGS B _ _ _ _ _ cid pos HARc Hin) as (Hg64 & Hgb64 & Hgb).
    pose proof (hb_frames_apart cid pos Hin) as Hap.
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) cid pos) ltac:(unfold kHighMemEnd; lia)) as Hsb1.
    pose proof (shadow_range_end (frame_addr (n_lyc cx) cid pos) (fs_frame_bytes cid) Hnn) as Hse.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; lia)) as Hsb2.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    apply HV; [unfold shadow_addr, kHighShadowEnd, kLowMemEnd in *; destruct Hr; lia|].
    intros [Hw | [Hw | Hw]]; [unfold shadow_addr, kHighShadowEnd in *; destruct Hr; lia | exact (He (HE _ Hw)) |].
    destruct Hr as [Hr | Hr].
    + pose proof (Hsha _ Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    + assert (HG8 : frame_addr (n_lyc cx) cid pos mod 8 = 0) by (clear - Hg64; Z.div_mod_to_equations; lia).
      assert (Hn8 : fs_frame_bytes cid mod 8 = 0) by (clear - Hgb64; Z.div_mod_to_equations; lia).
      rewrite HSHe in Hw. unfold shadow_addr in Hr.
      exact (hb_shadow_apart (nF cx fp) (frame_addr (n_lyc cx) cid pos) (fs_frame_bytes cid) a
        HF64 HG8 Hn8 ltac:(lia) ltac:(lia) Hnn Hap Hw Hr).
  - intros a Ha Hs Hp. apply HP. exact (K5 a Ha Hs Hp).
  - intros a Ha. apply HP. exact (K6 a Ha).
Qed.

Lemma hb_mbyte : forall x, 0 <= x < 2 ^ 64 -> ~ hb_wr cx fp x ->
  mbyte SEGS (rdW W3 m') x = mbyte SEGS (rdW W3 m3) x.
Proof. intros x Hx Hn. apply (mbyte_of_aview SEGS). apply HV; assumption. Qed.

(* A heap block of the caller apart from the struct's first 16 bytes is kept. *)
Lemma hb_block_out : forall p n x, In (p, n) (ablocks B (n_lyc cx) (n_Sc cx)) ->
  p <= x < p + req_size n -> ~ (n_ps cx <= x < n_ps cx + 16) -> 0 <= x < 2 ^ 64 /\ ~ hb_wr cx fp x.
Proof.
  intros p n x Hin Hx Hps. pose proof hb_J as (HARc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4 & Hpc & Hpia & _).
  pose proof hb_geo as (Hsp & _). pose proof asan_consts as (Hac & _).
  split; [lia|]. intros [Hw | [Hw | Hw]]; [lia | exact (Hps Hw) |].
  pose proof (hb_shadow_not_app x Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* A byte of a caller frame apart from the struct's first 16 bytes is kept, and so is its shadow. *)
Lemma hb_frame_out : forall c p x, In (c, p) (n_own cx) ->
  frame_addr (n_lyc cx) c p <= x < frame_addr (n_lyc cx) c p + fs_frame_bytes c ->
  (~ (n_ps cx <= x < n_ps cx + 16) -> 0 <= x < 2 ^ 64 /\ ~ hb_wr cx fp x) /\
  (0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ hb_wr cx fp (shadow_of_addr SHADOW_OFF x)).
Proof.
  intros c p x Hown Hx.
  destruct (hb_geo_frame c p x 0 Hown ltac:(lia) ltac:(lia) ltac:(lia)) as (Hg4 & Hgc & Hgia & _ & Hg64 & Hgb64 & Hap).
  pose proof hb_geo as (Hsp & _ & _ & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  pose proof asan_consts as (Hac & _).
  assert (HG8 : frame_addr (n_lyc cx) c p mod 8 = 0) by (clear - Hg64; Z.div_mod_to_equations; lia).
  assert (Hn8 : fs_frame_bytes c mod 8 = 0) by (clear - Hgb64; Z.div_mod_to_equations; lia).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  assert (Hsx : SHADOW_OFF + frame_addr (n_lyc cx) c p / 8 <= shadow_of_addr SHADOW_OFF x <
                SHADOW_OFF + frame_addr (n_lyc cx) c p / 8 + fs_frame_bytes c / 8).
  { unfold shadow_of_addr. clear - Hx HG8 Hn8 Hnn Hg4. Z.div_mod_to_equations. lia. }
  assert (Hsx2 : shadow_of_addr SHADOW_OFF x < kHighMemBeg).
  { unfold shadow_of_addr, kHighMemBeg, SHADOW_OFF in *.
    assert (x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). change (0x7fffff800000 / 8) with 17592184995840 in *. lia. }
  split.
  - intros Hps. split; [lia|]. intros [Hw | [Hw | Hw]]; [lia | exact (Hps Hw) |].
    pose proof (hb_shadow_not_app x Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - split; [unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]|].
    intros [Hw | [Hw | Hw]].
    + unfold kHighMemBeg in *. lia.
    + unfold shadow_of_addr, SHADOW_OFF in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      pose proof hb_psfr as (Hown' & Hpl & Hph & _).
      destruct (hb_geo_frame (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown' Hpl Hph ltac:(unfold PS_LEN; lia))
        as (_ & _ & Hpia & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, PS_LEN in *.
      assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
    + rewrite HSHe in Hw. exact (hb_shadow_apart (nF cx fp) (frame_addr (n_lyc cx) c p) (fs_frame_bytes c)
        (shadow_of_addr SHADOW_OFF x) HF64 HG8 Hn8 ltac:(lia) ltac:(lia) Hnn Hap Hw Hsx).
Qed.

Lemma hb_ra_step : forall x n, 0 <= n ->
  (forall y, x <= y < x + n -> exists c p, In (c, p) (n_own cx) /\
     frame_addr (n_lyc cx) c p <= y < frame_addr (n_lyc cx) c p + fs_frame_bytes c) ->
  range_addressable (aview SEGS (w_H W3) m3) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W3) m') SHADOW_OFF x n.
Proof.
  intros x n Hn Hfr HR. apply (PcapSourceCloseSpec.ra_frame _ _ x n HR).
  intros y Hy. destruct (Hfr y Hy) as (c & p & Hown & Hyr).
  destruct (hb_frame_out c p y Hown Hyr) as (_ & Hs1 & Hs2). apply HV; assumption.
Qed.

Lemma hb_mid_step : forall pc sh q ol vt vid tv ms' md' pc' sh' ol',
  ms_mem ms' = m' ->
  nx_mid B MT KS cx fp pc sh (nx_E cx) q ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  nx_body cx fp pc' W3 ms' sh' ->
  getr (ms_regs ms') 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  val_mem SEGS (rdW W3 m') (n_ps cx + PS_F_OFF) 8 (n_h cx) ->
  val_mem SEGS (rdW W3 m') (n_ps cx + PS_SW_OFF) 4 (n_sw cx) ->
  val_mem SEGS (rdW W3 m') (n_ps cx + PS_OL_OFF) 4 ol' ->
  nx_mid B MT KS cx fp pc' sh' (nx_E cx) q ol' vt vid tv k2 ly3 S3 W3 ms' md'.
Proof.
  intros pc sh q ol vt vid tv ms' md' pc' sh' ol' Hm' HM Hbd Hs8 Hfds Hfs Vf Vsw Vol.
  destruct HM as (_ & _ & (Hk & Hbl & Hmo & Hfds3 & Hfs3) & HK & HEs & Hh & Hps & Hra & Hsrc & Hq & Hbuf & Hts).
  unfold nx_mid. rewrite Hm'.
  pose proof hb_psfr as (Hown & Hpl & Hph & Hps8 & Hps4 & Hps47).
  assert (Hpsw : forall a, n_ps cx <= a < n_ps cx + 16 -> nx_E cx a)
    by (intros a Ha; unfold nx_E, nx_wrset, PS_LEN; left; lia).
  split; [exact Hbd|]. split; [exact Hs8|].
  split; [split; [exact Hk|]; split; [exact Hbl|]; split; [exact Hmo|]; split; [rewrite Hfds; exact Hfds3 | rewrite Hfs; exact Hfs3]|].
  split; [exact (hb_kept_step (nx_E cx) HK Hpsw)|].
  split; [exact HEs|]. split; [exact Hh|].
  split.
  { destruct Hps as (_ & _ & _ & Hvt & Hvid & Hpad & Hpadl).
    unfold nx_ps_at. split; [exact Vf|]. split; [exact Vsw|]. split; [exact Vol|].
    assert (Htail : forall y, n_ps cx + 16 <= y < n_ps cx + 24 ->
      mbyte SEGS (rdW W3 m') y = mbyte SEGS (rdW W3 m3) y).
    { intros y Hy. apply hb_mbyte; apply (proj1 (hb_frame_out (n_cid cx) (n_pos cx) y Hown ltac:(unfold PS_LEN in *; lia)));
      unfold PS_LEN in *; lia. }
    split; [eapply PcapSourceClose.vm_frame; [| exact Hvt]; intros y Hy; apply Htail; unfold PS_VT_OFF in *; cbn in Hy; lia|].
    split; [eapply PcapSourceClose.vm_frame; [| exact Hvid]; intros y Hy; apply Htail; unfold PS_VID_OFF in *; cbn in Hy; lia|].
    split; [|exact Hpadl].
    apply (garr8_frame SEGS _ _ _ _ Hpad). intros y Hy. rewrite Hpadl in Hy. apply Htail. cbn in Hy. lia. }
  split.
  { apply hb_ra_step; [unfold PS_LEN; lia | | exact Hra].
    intros y Hy. exists (n_cid cx), (n_pos cx). split; [exact Hown | unfold PS_LEN in *; lia]. }
  destruct (hb_stream Hh) as (Hinh & Hinb & Hsh & Hsb & Hlen & Hp0).
  split.
  { apply (PcapSourceClose.asource_at_frame KS (rdW W3 m3) (rdW W3 m')); [|exact Hsrc].
    intros a [Ha | [Ha | Ha]].
    - pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as (_ & Hrq).
      destruct (hb_block_out (n_h cx) SRC_FILE_BLOCK a Hinh ltac:(lia) ltac:(unfold PS_LEN in *; lia)) as (H1 & H2).
      apply hb_mbyte; assumption.
    - pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as (_ & Hrq).
      destruct (hb_block_out (n_b cx) (Z.of_nat (length (n_C cx))) a Hinb ltac:(lia) ltac:(unfold PS_LEN in *; lia)) as (H1 & H2).
      apply hb_mbyte; assumption.
    - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
      pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
      pose proof hb_geo as (Hsp & _).
      destruct (hb_geo_frame (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown Hpl Hph ltac:(unfold PS_LEN; lia))
        as (_ & _ & _ & Hoff & _).
      apply hb_mbyte; [unfold kLowMemEnd in Hr2; lia|].
      intros [Hw | [Hw | Hw]]; [pose proof asan_consts as (Hac & _); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia
        | unfold off_img, PS_LEN, pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *; lia |].
      pose proof (hb_shadow_not_app a Hw). unfold kLowShadowBeg, kLowMemEnd in *. lia. }
  split; [exact Hq|].
  split.
  { destruct Hbuf as (bj' & Hg & Hl). exists bj'. split; [|exact Hl].
    destruct (hb_buf Hh) as (Hinbuf & Hsep & Hcap).
    pose proof HB as HB'. unfold nx_base in HB'.
    assert (Hlb : Z.of_nat (length (n_bj cx)) = nx_bufn (n_cap cx))
      by (decompose [and] HB'; match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ =>
            destruct (H Hh) as (_ & _ & _ & _ & L & _); exact L end).
    apply (garr8_frame SEGS _ _ _ _ Hg). intros y Hy. rewrite Hl, Hlb in Hy.
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & Hrq).
    destruct (hb_block_out (n_buf cx) (nx_bufn (n_cap cx)) y Hinbuf ltac:(lia) ltac:(unfold PS_LEN in *; lia)) as (H1 & H2).
    apply hb_mbyte; assumption. }
  intros Hts0. destruct (Hts Hts0) as (Hv & Hrat).
  destruct (hb_tsfr Hh Hts0) as ((tc & tp & Htown & Htl & Hth) & Htsep & Hts4).
  split.
  - eapply PcapSourceClose.vm_frame; [| exact Hv]. intros y Hy. cbn in Hy.
    apply hb_mbyte; apply (proj1 (hb_frame_out tc tp y Htown ltac:(lia))); unfold PS_LEN in *; lia.
  - apply hb_ra_step; [lia | | exact Hrat].
    intros y Hy. exists tc, tp. split; [exact Htown | lia].
Qed.

End e.


(* ---- frames of consecutive runs ---- *)
Definition hb_wkeyg (r : YP09.region) : option nat * Z * Z := (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r).

Lemma hb_wrange_same_g : forall (Ex : env) rs rs', map hb_wkeyg rs = map hb_wkeyg rs' ->
  forall a, in_wrange Ex rs a -> in_wrange Ex rs' a.
Proof.
  intros Ex rs. induction rs as [|r rs IH]; intros rs' Hm a (r0 & Hin & Ha); [destruct Hin|].
  destruct rs' as [|r' rs']; [discriminate Hm|].
  assert (Hk : hb_wkeyg r = hb_wkeyg r') by (simpl in Hm; congruence).
  assert (Hm' : map hb_wkeyg rs = map hb_wkeyg rs') by (simpl in Hm; congruence). clear Hm. rename Hm' into Hm.
  destruct Hin as [<- | Hin].
  - exists r'. split; [left; reflexivity|]. unfold hb_wkeyg in Hk.
    assert (E1 : YP09.r_base r = YP09.r_base r') by congruence.
    assert (E2 : YP09.r_wlo r = YP09.r_wlo r') by congruence.
    assert (E3 : YP09.r_whi r = YP09.r_whi r') by congruence.
    rewrite <- E1, <- E2, <- E3. exact Ha.
  - destruct (IH rs' Hm a (ex_intro _ r0 (conj Hin Ha))) as (r1 & Hin1 & Ha1).
    exists r1. split; [right; exact Hin1 | exact Ha1].
Qed.

Lemma hb_frame_compose_g : forall (Ex : env) rs0 rs (m1 m2 m4 : word -> option byte),
  frame_of Ex rs0 m1 m2 -> frame_of Ex rs m2 m4 -> map hb_wkeyg rs = map hb_wkeyg rs0 ->
  frame_of Ex rs0 m1 m4.
Proof.
  intros Ex rs0 rs m1 m2 m4 H1 H2 Hm x Hx. rewrite (H2 x); [exact (H1 x Hx)|].
  intros Hw. apply Hx. exact (hb_wrange_same_g Ex rs rs0 Hm _ Hw).
Qed.

Lemma hb_mbyte_frame : forall (Ex : env) rs (m m' : word -> option byte) a,
  frame_of Ex rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange Ex rs a -> mbyte SEGS m' a = mbyte SEGS m a.
Proof.
  intros Ex rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* ---- tactics of the walk ---- *)
Local Ltac hb_reg HS r H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H end.

Local Ltac hb_branch BR HS Hc :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi pcap_tpi FUEL ss) in
    lazymatch r with (_, PRS_stopped (SR_branch ?c ?a ?b)) =>
      apply (BR W Ex ss ms _ _ c a b HS); clear HS; intros Hc HS end end.


(* ---- the seat at NP_hd_ra (the full header) ---- *)
Section f.
Variable q : Z.
Variable lh : option Z.
#[local] Notation E := (hb_E cx fp (ms_regs ms3) q lh).
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).
Hypothesis HM : nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
  (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3.
Hypothesis Hhdr : garr8 SEGS (rdW W3 (ms_mem ms3)) (nF cx fp + NO_PH) (nx_hdr (n_C cx) q).
Hypothesis Hs10 : getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH).
Hypothesis Hq0 : 0 <= q.
Hypothesis Hfull : 16 <= Z.of_nat (length (n_C cx)) - q.

Lemma hb_hb : forall j, (j < 16)%nat -> 0 <= nx_hb (n_C cx) q j < 256 /\
  val_mem SEGS (rdW W3 (ms_mem ms3)) (nF cx fp + NO_PH + Z.of_nat j) 1 (nx_hb (n_C cx) q j).
Proof.
  intros j Hj. rewrite <- (nx_hdr_len16 (n_C cx) q Hq0 Hfull) in Hj.
  destruct (Hhdr j Hj) as [Hv Hr]. split; [exact Hr | exact Hv].
Qed.

Lemma hb_mid_h : n_h cx <> 0.
Proof. destruct HM as (_ & _ & _ & _ & _ & Hh & _). exact Hh. Qed.

Lemma hb_sw01 : n_sw cx = 0 \/ n_sw cx = 1.
Proof. pose proof hb_mid_h as Hh. hb_base. auto. Qed.

Lemma hb_E_sv_other : forall n z, (n < 33 \/ 53 <= n)%nat ->
  sv_denot E (SOff n z) = sv_denot (nx_mkE cx fp (ms_regs ms3)) (SOff n z).
Proof. intros n z Hn. cbn [sv_denot]. rewrite hb_E_other by exact Hn. reflexivity. Qed.

Lemma hb_regs_ok : regs_ok E hb_sr (ms_regs ms3).
Proof.
  pose proof HM as ((Hb0 & _) & _).
  destruct Hb0 as (_ & _ & _ & _ & _ & _ & Hnr & _ & _ & _ & _ & _ & H18 & H19 & _).
  pose proof (nx_regs_ok B KS cx fp ms3 HB Hnr H18 H19) as HR0.
  assert (HR1 : regs_ok E nx_sr (ms_regs ms3)).
  { apply (regs_ok_agree_p (fun n => negb ((33 <=? n) && (n <? 53))%nat) (nx_mkE cx fp (ms_regs ms3)) E);
      [| vm_compute; reflexivity | exact HR0].
    split; [|reflexivity]. intros n Hn. apply hb_E_other.
    destruct ((33 <=? n) && (n <? 53))%nat eqn:Hb; [discriminate|].
    apply andb_false_iff in Hb as [Hb|Hb]; [left; apply Nat.leb_gt in Hb | right; apply Nat.ltb_ge in Hb]; lia. }
  replace hb_sr with (sr_set nx_sr (26%bv : bv 5) (SOff NA_F NO_PH)) by (vm_compute; reflexivity).
  intros r. destruct (decide (r = (26%bv : bv 5))) as [->|Hne].
  - rewrite sr_get_set_same by reflexivity. rewrite Hs10. cbn [sv_denot].
    unfold NA_F, NO_PH in *. rewrite hb_E_other by lia.
    pose proof (nx_mkE_env cx fp (ms_regs ms3)) as (_ & _ & _ & HF' & _). unfold NA_F in HF'. rewrite HF'.
    pose proof hb_geo as (_ & _ & _ & HF0 & HFc & _).
    pose proof asan_consts as (Hac & _).
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite sr_get_set_other by exact Hne. apply HR1.
Qed.


Lemma hb_ps_geo : 4096 <= n_ps cx /\ n_ps cx mod 8 = 0 /\ in_app (n_ps cx) PS_LEN /\
  frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) /\
  n_ps cx + PS_LEN <= alloc_ceiling.
Proof.
  pose proof hb_psfr as (Hown & Hpl & Hph & Hps8 & Hps4 & Hps47).
  destruct (hb_geo_frame (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown Hpl Hph ltac:(unfold PS_LEN; lia))
    as (Hg4 & Hgc & Hgia & _).
  unfold in_app in *. repeat split; try lia.
Qed.

Definition hb_shp_v : Z := shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF).

Lemma hb_shp_facts : SHADOW_OFF + 512 <= hb_shp_v /\ hb_shp_v + 1 <= kHighMemBeg /\
  ~ (nSH cx fp <= hb_shp_v < nSH cx fp + 8) /\
  shadow_of_addr SHADOW_OFF (n_ps cx + PS_OL_OFF) = hb_shp_v /\
  shadow_of_addr SHADOW_OFF (n_ps cx + 15) = hb_shp_v.
Proof.
  pose proof hb_ps_geo as (Hps4 & Hps8 & Hpsia & Hpl & Hph & Hpc).
  pose proof hb_psfr as (Hown & _).
  pose proof hb_geo as (_ & _ & _ & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  pose proof asan_consts as (Hac & _).
  destruct (hb_frame_out
    (n_cid cx) (n_pos cx) (n_ps cx + PS_SW_OFF) Hown ltac:(unfold PS_SW_OFF, PS_LEN in *; lia)) as (_ & _ & Hw).
  unfold hb_shp_v, shadow_of_addr, PS_SW_OFF, PS_OL_OFF, PS_LEN, SHADOW_OFF, kHighMemBeg, hb_wr in *.
  assert (D1 : (n_ps cx + 12) / 8 = (n_ps cx + 8) / 8) by (clear - Hps8; Z.div_mod_to_equations; lia).
  assert (D2 : (n_ps cx + 15) / 8 = (n_ps cx + 8) / 8) by (clear - Hps8; Z.div_mod_to_equations; lia).
  assert (D3 : 512 <= (n_ps cx + 8) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (D4 : (n_ps cx + 8) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in D4.
  split; [lia|]. split; [lia|]. split; [intros Hx; apply Hw; right; right; exact Hx|].
  rewrite D1, D2. split; reflexivity.
Qed.

Lemma hb_fcs_ok : Forall (YP09.chunk_ok SEGS E M3 (nF cx fp)) hb_fcs.
Proof.
  assert (HC : forall j, (j < 16)%nat ->
    YP09.chunk_ok SEGS E M3 (nF cx fp) (YP09.mkChunk (NO_PH + Z.of_nat j) (CVal 1 (SOff (34 + j) 0)))).
  { intros j Hj. destruct (hb_hb j Hj) as (Hr & Hv).
    apply (chunk_ok_val SEGS E M3 (nF cx fp) (NO_PH + Z.of_nat j) 1%N (SOff (34 + j) 0) (nx_hb (n_C cx) q j)).
    - rewrite nx_sv_SOff0, hb_E_mine by lia. f_equal. unfold hb_v.
      replace ((34 + j) =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace ((34 + j) <? 50)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      f_equal. lia.
    - cbn. lia.
    - cbn. lia.
    - rewrite Z.add_assoc. exact Hv. }
  unfold hb_fcs.
  repeat (apply Forall_cons; [match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 34)%nat in
    replace o with (NO_PH + Z.of_nat j) by reflexivity; replace n with (34 + j)%nat by reflexivity;
    apply HC; lia end|]).
  apply Forall_nil.
Qed.
Lemma hb_E33 : ew E HB_SHP = Z_to_bv 64 hb_shp_v.
Proof. unfold HB_SHP. rewrite hb_E_mine by lia. reflexivity. Qed.
Lemma hb_E50 : ew E HB_H = Z_to_bv 64 (n_h cx).
Proof. unfold HB_H. rewrite hb_E_mine by lia. reflexivity. Qed.
Lemma hb_E51 : ew E HB_SW = Z_to_bv 64 (n_sw cx).
Proof. unfold HB_SW. rewrite hb_E_mine by lia. reflexivity. Qed.
Lemma hb_E52 : ew E HB_OL = Z_to_bv 64 (nx_ol cx lh).
Proof. unfold HB_OL. rewrite hb_E_mine by lia. reflexivity. Qed.
Lemma hb_Ex : forall j, (j < 16)%nat -> ew E (34 + j) = Z_to_bv 64 (nx_hb (n_C cx) q j).
Proof.
  intros j Hj. rewrite hb_E_mine by lia. f_equal. unfold hb_v.
  replace ((34 + j) =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((34 + j) <? 50)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  f_equal. lia.
Qed.

Lemma hb_ol_rng : 0 <= nx_ol cx lh < 2 ^ 32.
Proof.
  pose proof hb_mid_h as Hh. unfold nx_ol. destruct lh as [q0|].
  - unfold PSN.orig. apply nx_hw_range.
  - hb_base. match goal with H : n_h cx <> 0 -> 0 <= n_lol cx < 2 ^ 32 /\ _ |- _ => apply H; exact Hh end.
Qed.

Lemma hb_extra_ok : Forall (YP09.region_ok SEGS E M3) hb_extra.
Proof.
  pose proof hb_mid_h as Hh.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE.
  pose proof hb_sw01 as Hsw. pose proof hb_ol_rng as Hol.
  pose proof HM as (_ & _ & _ & _ & _ & _ & (Vf & Vs & Vo & _) & Hra & _).
  assert (Hh64 : 0 <= n_h cx < 2 ^ 64) by (hb_base; lia).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (nx_ps_region_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E 16 hb_pcs HE ltac:(unfold PS_LEN; lia)).
    unfold hb_pcs. repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E M3 (n_ps cx) PS_F_OFF 8%N (SOff HB_H 0) (n_h cx));
        [rewrite nx_sv_SOff0, hb_E50; reflexivity | cbn; lia | cbn; lia | exact Vf].
    + apply (chunk_ok_val SEGS E M3 (n_ps cx) PS_SW_OFF 4%N (SOff HB_SW 0) (n_sw cx));
        [rewrite nx_sv_SOff0, hb_E51; reflexivity | cbn; lia | cbn; lia | exact Vs].
    + apply (chunk_ok_val SEGS E M3 (n_ps cx) PS_OL_OFF 4%N (SOff HB_OL 0) (nx_ol cx lh));
        [rewrite nx_sv_SOff0, hb_E52; reflexivity | cbn; lia | cbn; lia | exact Vo].
  - pose proof hb_shp_facts as (S0 & S1 & _ & _ & S15).
    unfold YP09.region_ok, hb_shp_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite hb_E33, unsigned_lit_small by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
    split; [unfold SHADOW_OFF in *; lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 hb_shp_v 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    destruct (Hra (n_ps cx + 15) ltac:(unfold PS_LEN; lia)) as (sb & Hsb & Hok).
    rewrite S15 in Hsb.
    assert (Hs0 : sb = 0).
    { pose proof hb_ps_geo as (_ & Hps8 & _). unfold saddr_ok in Hok.
      assert ((n_ps cx + 15) mod 8 = 7) by (rewrite Z.add_mod, Hps8 by lia; reflexivity). lia. }
    subst sb. intros k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite !Z.add_0_r.
    unfold aview in Hsb. destruct (mbyte SEGS M3 hb_shp_v) as [b|] eqn:Hb; [|discriminate].
    cbn [option_map] in Hsb. injection Hsb as Hb0. f_equal.
    apply bv_eq. rewrite Hb0. vm_compute. reflexivity.
Qed.

Lemma hb_extra_pwd : YP09.pairwise_disjoint E hb_extra.
Proof.
  pose proof hb_ps_geo as (Hps4 & Hps8 & Hpsia & _).
  pose proof hb_shp_facts as (S0 & S1 & _).
  pose proof (nx_ps_base B KS cx fp HB E (hb_E_env cx fp (ms_regs ms3) q lh)) as U10.
  unfold hb_extra. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, nx_ps_region, hb_shp_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U10. cbn [YP09.base_val].
  rewrite hb_E33, unsigned_lit_small by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, PS_LEN in *.
  split; [split; [lia | exact I]|]. split; exact I.
Qed.

Lemma hb_fix_disj : Forall (fun r => YP09.all_disjoint E r hb_extra) (nx_regions0 true NSH_ph 4 6 0 hb_fcs).
Proof.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE. pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  apply nx_fix_disj_cons.
  - exact (nx_ps_disj B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E true NSH_ph 4 6 0 hb_fcs 16 hb_pcs HE HEI
      ltac:(unfold NX_FRAME; lia) ltac:(lia) ltac:(lia)).
  - pose proof (nx_bases B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
    pose proof hb_shp_facts as (S0 & S1 & S2 & _).
    pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
    pose proof asan_consts as (Hac & _).
    pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
    assert (U33 : YP09.base_val E (Some HB_SHP) = hb_shp_v)
      by (cbn [YP09.base_val]; rewrite hb_E33; apply unsigned_lit_small; unfold kHighMemBeg, SHADOW_OFF in *; lia).
    unfold nx_regions0, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.all_disjoint]; (split; [|exact I]);
      unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; unfold hb_shp_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi];
      rewrite ?U2, ?U60, ?U516, ?U529, ?U242, ?U256, ?U33;
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, NX_SPILL, NX_FRAME, NX_STK, AFREAD_STK,
        pcap_img_end, YImgTop.IMG_TOP in *; lia.
Qed.

Lemma hb_G_ok : facts_ok E hb_G.
Proof.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE.
  pose proof (nx_facts0_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E HE) as (A0 & _).
  pose proof hb_sw01 as Hsw.
  pose proof hb_ps_geo as (Hps4 & Hps8 & Hpsia & _).
  pose proof hb_shp_facts as (S0 & S1 & _ & S12 & _).
  assert (Hb : forall j, (j < 16)%nat -> afact_ok E (34 + j) (mkAF 0 255 0)).
  { intros j Hj. destruct (hb_hb j Hj) as (Hr & _). unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite hb_Ex by exact Hj. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (Hm : forall l, (forall j, In j l -> (j < 16)%nat) ->
    atoms_ok E (map (fun j => ((34 + j)%nat, mkAF 0 255 0)) l)).
  { intros l. induction l as [|j l IH]; intros Hl; cbn [map atoms_ok]; [exact I|].
    split; [apply Hb; apply Hl; left; reflexivity | apply IH; intros j' Hj'; apply Hl; right; exact Hj']. }
  assert (Happ : forall l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2)).
  { intros l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
    destruct H1 as [H1a H1b]. split; [exact H1a | exact (IH l2 H1b H2)]. }
  unfold facts_ok, hb_G. cbn [f_atoms f_conds f_alias].
  split; [|split; [exact I|]].
  - apply Happ; [exact A0|]. cbn [atoms_ok]. split.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite hb_E51, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + apply Hm. intros j Hj. apply in_seq in Hj. lia.
  - pose proof HE as (_ & Hsb & _). 
    pose proof (nx_ps_atom B KS cx fp HB E HE) as HPS.
    assert (Hps64 : 0 <= n_ps cx < 2 ^ 64)
      by (pose proof hb_ps_geo as (_ & _ & _ & _ & _ & Hpc); pose proof asan_consts as (Hac & _); unfold PS_LEN in *; lia).
    assert (ADD0 : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w).
    { intros w. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r.
      apply Z.mod_small. apply u64_range. }
    cbn [alias_ok sv_denot]. rewrite !ADD0.
    rewrite (nx_U_shx E NA_PS (n_ps cx) PS_SW_OFF Hsb HPS Hps64) by (pose proof hb_ps_geo as (_ & _ & _ & _ & _ & Hpc); pose proof asan_consts as (Hac & _); unfold PS_SW_OFF, PS_LEN in *; lia).
    rewrite (nx_U_shx E NA_PS (n_ps cx) PS_OL_OFF Hsb HPS Hps64) by (pose proof hb_ps_geo as (_ & _ & _ & _ & _ & Hpc); pose proof asan_consts as (Hac & _); unfold PS_OL_OFF, PS_LEN in *; lia).
    rewrite S12. fold hb_shp_v. rewrite hb_E33, unsigned_lit_small, Z.add_0_r by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
    split; [reflexivity | split; [reflexivity | exact I]].
Qed.

Lemma hb_seat : st_ok_pi SEGS VAL E hb_ss (restrict (w_H W3) ms3).
Proof.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE. pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  pose proof HM as (Hbd & _).
  apply (nx_seat B KS LAWS TL cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E NP_hd_ra hb_sr NSH_ph 4 6 0 hb_fcs hb_extra hb_G
    HE HEI Hbd hb_regs_ok ltac:(unfold NX_FRAME; lia) hb_fcs_ok ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
    hb_extra_ok hb_extra_pwd hb_fix_disj hb_G_ok).
Qed.

(* ---- the writes of the runs ---- *)
Definition hb_wkey (r : YP09.region) : option nat * Z * Z := (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r).

Lemma hb_wrange_same : forall rs rs', map hb_wkey rs = map hb_wkey rs' ->
  forall a, in_wrange E rs a -> in_wrange E rs' a.
Proof.
  intros rs. induction rs as [|r rs IH]; intros rs' Hm a (r0 & Hin & Ha); [destruct Hin|].
  destruct rs' as [|r' rs']; [discriminate Hm|].
  assert (Hk : hb_wkey r = hb_wkey r') by (simpl in Hm; congruence).
  assert (Hm' : map hb_wkey rs = map hb_wkey rs') by (simpl in Hm; congruence). clear Hm. rename Hm' into Hm.
  destruct Hin as [<- | Hin].
  - exists r'. split; [left; reflexivity|]. unfold hb_wkey in Hk.
    assert (E1 : YP09.r_base r = YP09.r_base r') by congruence.
    assert (E2 : YP09.r_wlo r = YP09.r_wlo r') by congruence.
    assert (E3 : YP09.r_whi r = YP09.r_whi r') by congruence.
    rewrite <- E1, <- E2, <- E3. exact Ha.
  - destruct (IH rs' Hm a (ex_intro _ r0 (conj Hin Ha))) as (r1 & Hin1 & Ha1).
    exists r1. split; [right; exact Hin1 | exact Ha1].
Qed.

Lemma hb_awr : awr_ok E (ss_mem hb_ss) (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
  (ablocks B ly3 S3) ly3 ((NX_CID, fp) :: n_own cx).
Proof.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE. pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  pose proof (nx_bases B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  pose proof (nx_ps_base B KS cx fp HB E HE) as U10.
  pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  pose proof hb_mid_h as Hh.
  pose proof HM as (_ & _ & (_ & Hbl & _) & _).
  assert (Hst : n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK /\ spZ (n_regs cx) <= n_sp0 cx) by (hb_base; lia).
  assert (Hwr : nx_wr_ok NX_STK B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
    (spZ (n_regs cx)) (n_ps cx) PS_LEN) by (hb_base; auto).
  unfold hb_ss, nx_ss, nx_regions, nx_regions0, hb_extra. cbn [ss_mem app].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_at _ _ _ _ _ _ _ _ _ _ NA_SP1 (n_sp1 cx)); [reflexivity | exact U60 | cbn; unfold NX_STK, AFREAD_STK in *; lia | cbn; unfold NX_SPILL; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ NA_FSH (nSH cx fp)); [reflexivity | exact U529 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi nx_shadow_region] in Ha. apply awr_byte_own_head_shadow.
    rewrite hb_frame_addr_eq. fold (nF cx fp). unfold shadow_addr. rewrite HSHe in Ha.
    assert (Hfb : fs_frame_bytes NX_CID / 8 = 8) by (vm_compute; reflexivity). rewrite Hfb. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ NA_PS (n_ps cx)); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi nx_ps_region] in Ha.
    destruct (Hwr a ltac:(unfold PS_LEN; lia)) as (Hab & _).
    eapply awr_byte_weaken; [| | | exact Hab].
    - intros x Hx. rewrite Hbl. exact Hx.
    - intros x Hx. right. exact Hx.
    - exact hb_frame_addr_eq. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
Qed.

Lemma hb_awr_any : forall rs, map hb_wkey rs = map hb_wkey (ss_mem hb_ss) ->
  awr_ok E rs (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
    (ablocks B ly3 S3) ly3 ((NX_CID, fp) :: n_own cx).
Proof. intros rs Hm a Ha. apply hb_awr. exact (hb_wrange_same rs (ss_mem hb_ss) Hm a Ha). Qed.

Lemma hb_frame_compose : forall rs (m1 m2 m4 : word -> option byte),
  frame_of E (ss_mem hb_ss) m1 m2 -> frame_of E rs m2 m4 -> map hb_wkey rs = map hb_wkey (ss_mem hb_ss) ->
  frame_of E (ss_mem hb_ss) m1 m4.
Proof.
  intros rs m1 m2 m4 H1 H2 Hm x Hx. rewrite (H2 x); [exact (H1 x Hx)|].
  intros Hw. apply Hx. exact (hb_wrange_same rs (ss_mem hb_ss) Hm _ Hw).
Qed.

Lemma hb_HV : forall m', frame_of E (ss_mem hb_ss) (rdW W3 (ms_mem ms3)) (rdW W3 m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ hb_wr cx fp a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
  intros m' HF a Ha Hn.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE. pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & _).
  apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E true NSH_ph 4 6 0 hb_fcs hb_extra
    (ms_mem ms3) m' HE HEI HF a Ha).
  - intros Hw. apply Hn. left. unfold NX_SPILL, NX_STK, AFREAD_STK in *. lia.
  - lia.
  - intros Hw. apply Hn. right. right. lia.
  - intros (r & Hin & Hr). apply Hn. right. left. unfold hb_extra in Hin. destruct Hin as [<- | [<- | []]].
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi nx_ps_region] in Hr. rewrite (nx_ps_base B KS cx fp HB E HE) in Hr. lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi hb_shp_region] in Hr. lia.
Qed.

(* ---- the denotations the walk meets ---- *)
Lemma hb_sv_cur : forall i, (i < 32)%nat -> sv_denot E (SOff (530 + i) 0) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros i Hi. rewrite nx_sv_SOff0, hb_E_other by lia.
  exact (nx_mkE_cur cx fp (ms_regs ms3) i Hi).
Qed.

Lemma hb_sv_x : forall n, (34 <= n < 50)%nat -> sv_denot E (SOff n 0) = Z_to_bv 64 (nx_hb (n_C cx) q (n - 34)).
Proof.
  intros n Hn. rewrite nx_sv_SOff0. replace n with (34 + (n - 34))%nat at 1 by lia.
  rewrite hb_Ex by lia. reflexivity.
Qed.

Lemma hb_sv_sw : sv_denot E (SOff HB_SW 0) = Z_to_bv 64 (n_sw cx).
Proof. rewrite nx_sv_SOff0. exact hb_E51. Qed.

(* ---- a leaf of the walk: the middle state where a run stops ---- *)
Lemma hb_wb_md : forall l mat (md : Model), m_fds (with_vm_backing l mat md) = m_fds md /\
  m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md as [f [mp lz mt] io fs pr li ti sg sc]. split; reflexivity. Qed.

Lemma hb_leaf_mid : forall (ms' : machine_state) md' ss' ol' cs e_ol vs sh',
  st_ok_pi SEGS VAL E ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E (ss_mem hb_ss) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E (ss_regs ss') ->
  nx_land_chk true vs (ss_mem ss') = true -> map (fun v => v mod 256) vs = sh' -> length sh' = NX_NSH ->
  nth_error (ss_mem ss') 6 = Some (YP09.mkRegion (Some NA_PS) 0 PS_LEN 0 16 cs) ->
  In (YP09.mkChunk PS_F_OFF (CVal 8 (SOff HB_H 0))) cs ->
  In (YP09.mkChunk PS_SW_OFF (CVal 4 (SOff HB_SW 0))) cs ->
  In (YP09.mkChunk PS_OL_OFF (CVal 4 e_ol)) cs -> sv_denot E e_ol = Z_to_bv 64 ol' -> 0 <= ol' < 2 ^ 32 ->
  sr_get (ss_regs ss') 24 = SOff 554 0 ->
  nx_mid B MT KS cx fp (ss_pc ss') sh' (nx_E cx) (q + 16) ol' (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' ss' ol' cs e_ol vs sh' HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hsh Hlen Hnth Hcf Hcs Hco Heo Hro Hr24.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE. pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  pose proof hb_mid_h as Hh.
  pose proof (nx_land_by B KS LAWS cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR E ss' vs sh' HE HEI HS' Hrv Hsr Hchk Hsh Hlen Hh)
    as Hbd.
  assert (Hs8 : getr (ms_regs ms') 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx))).
  { rewrite (st_ok_pi_restrict_reg _ E ss' ms' 24%bv HS'), Hr24.
    change (SOff 554 0) with (SOff (530 + 24) 0). rewrite hb_sv_cur by lia.
    pose proof HM as (_ & H24 & _). exact H24. }
  pose proof (st_ok_pi_region_nth E ss' (restrict (w_H W3) ms') 6 _ HS' Hnth) as HR.
  cbn [ms_mem restrict] in HR.
  pose proof (nx_ps_base B KS cx fp HB E HE) as U10. cbn [YP09.base_val] in U10.
  assert (Hh64 : 0 <= n_h cx < 2 ^ 64) by (hb_base; lia).
  pose proof hb_sw01 as Hsw.
  assert (Vf : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_F_OFF) 8 (n_h cx)).
  { change 8%nat with (N.to_nat 8).
    apply (field_of_region E _ NA_PS (n_ps cx) cs 0 PS_LEN 0 16 PS_F_OFF 8%N (SOff HB_H 0) (n_h cx) HR U10 Hcf);
      [rewrite nx_sv_SOff0, hb_E50; reflexivity | cbn; lia | cbn; lia]. }
  assert (Vs : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_SW_OFF) 4 (n_sw cx)).
  { change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ NA_PS (n_ps cx) cs 0 PS_LEN 0 16 PS_SW_OFF 4%N (SOff HB_SW 0) (n_sw cx) HR U10 Hcs);
      [rewrite nx_sv_SOff0, hb_E51; reflexivity | cbn; lia | cbn; lia]. }
  assert (Vo : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 ol').
  { change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ NA_PS (n_ps cx) cs 0 PS_LEN 0 16 PS_OL_OFF 4%N e_ol ol' HR U10 Hco);
      [exact Heo | cbn; lia | cbn; lia]. }
  pose proof (hb_mid_step (ms_mem ms') (hb_HV (ms_mem ms') HF)
    (fun a Hp => apresent_grows _ _ _ a HG Hp)
    NP_hd_ra NSH_ph (q + nx_hk (n_C cx) q) (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx) ms' md' (ss_pc ss') sh' ol'
    eq_refl HM Hbd Hs8 Hfds Hfs Vf Vs Vo) as HM'.
  rewrite nx_hk_16 in HM' by exact Hfull. exact HM'.
Qed.

Lemma hb_kind_hdr : forall cap,
  PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) cap q =
  if PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q =? 0 then PSN.KEmpty
  else if PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <=? cap then
    (if q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <=? Z.of_nat (length (n_C cx)) then PSN.KFit else PSN.KCutFit)
  else if cap =? 0 then PSN.KBig0
  else if q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <=? Z.of_nat (length (n_C cx)) then PSN.KBig else PSN.KCutBig.
Proof.
  intros cap. unfold PSN.kind, PSN.flen. rewrite nxF_length.
  replace (Z.of_nat (length (n_C cx)) - q =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.of_nat (length (n_C cx)) - q <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* KEmpty: back to the loop head at q + 16, lh kept. *)
Lemma hb_leaf_loop : forall R (ms' : machine_state) md' ss' cs vs,
  st_ok_pi SEGS VAL E ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E (ss_mem hb_ss) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E (ss_regs ss') ->
  nx_land_chk true vs (ss_mem ss') = true -> map (fun v => v mod 256) vs = NSH_entry ->
  nth_error (ss_mem ss') 6 = Some (YP09.mkRegion (Some NA_PS) 0 PS_LEN 0 16 cs) ->
  In (YP09.mkChunk PS_F_OFF (CVal 8 (SOff HB_H 0))) cs ->
  In (YP09.mkChunk PS_SW_OFF (CVal 4 (SOff HB_SW 0))) cs ->
  In (YP09.mkChunk PS_OL_OFF (CVal 4 (SOff HB_OL 0))) cs ->
  sr_get (ss_regs ss') 24 = SOff 554 0 ->
  ss_pc ss' = NP_loop ->
  getr (ms_regs ms') 20 = w64 (n_buf cx) -> getr (ms_regs ms') 21 = w64 (n_ps cx) ->
  getr (ms_regs ms') 23 = w64 (n_cap cx) -> getr (ms_regs ms') 26 = w64 (nF cx fp + NO_PH) ->
  nx_next_ok R cx q -> n_p cx <= q ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q = 0 ->
  nx_loop_at B MT KS R cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros R ms' md' ss' cs vs HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hsh Hnth Hcf Hcs Hco Hr24 Hpc R20 R21 R23 R26
    HNX Hpq Hch Hi0.
  exists (q + 16), lh. split; [apply HNX; lia|].
  unfold nx_loop_inv. split.
  { rewrite <- Hpc.
    exact (hb_leaf_mid ms' md' ss' (nx_ol cx lh) cs (SOff HB_OL 0) vs NSH_entry HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hsh
      eq_refl Hnth Hcf Hcs Hco ltac:(rewrite nx_sv_SOff0; exact hb_E52) hb_ol_rng Hr24). }
  split; [exact R20|]. split; [exact R21|]. split; [exact R23|]. split; [exact R26|].
  apply nx_chain_empty; [exact Hch | rewrite nxF_length; lia |].
  rewrite hb_kind_hdr, Hi0. reflexivity.
Qed.

(* cap < incl: the skip test at NP_sk1. *)
Lemma hb_leaf_sk1 : forall R (ms' : machine_state) md' ss' cs e_ol vs,
  st_ok_pi SEGS VAL E ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E (ss_mem hb_ss) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E (ss_regs ss') ->
  nx_land_chk true vs (ss_mem ss') = true -> map (fun v => v mod 256) vs = NSH_ph ->
  nth_error (ss_mem ss') 6 = Some (YP09.mkRegion (Some NA_PS) 0 PS_LEN 0 16 cs) ->
  In (YP09.mkChunk PS_F_OFF (CVal 8 (SOff HB_H 0))) cs ->
  In (YP09.mkChunk PS_SW_OFF (CVal 4 (SOff HB_SW 0))) cs ->
  In (YP09.mkChunk PS_OL_OFF (CVal 4 e_ol)) cs ->
  sv_denot E e_ol = Z_to_bv 64 (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  sr_get (ss_regs ss') 24 = SOff 554 0 ->
  ss_pc ss' = NP_sk1 ->
  getr (ms_regs ms') 20 = w64 (n_buf cx) -> getr (ms_regs ms') 21 = w64 (n_ps cx) ->
  getr (ms_regs ms') 22 = w64 (-1) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  bv_unsigned (getr (ms_regs ms') 25) mod 2 ^ 32 = nx_incl cx q ->
  getr (ms_regs ms') 26 = w64 (nF cx fp + NO_PH) ->
  nx_next_ok R cx q ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  nx_incl cx q <> 0 -> n_cap cx < nx_incl cx q ->
  nx_sk1_inv B MT KS R cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros R ms' md' ss' cs e_ol vs HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hsh Hnth Hcf Hcs Hco Heo Hr24 Hpc R20 R21 R22 R23
    R25 R26 HNX Hch Hi0 Hcap.
  exists q, lh. split; [exact HNX|]. split; [exact Hch|]. split; [lia|]. split; [exact Hi0|]. split; [exact Hcap|].
  split.
  { rewrite <- Hpc. unfold nx_ol.
    exact (hb_leaf_mid ms' md' ss' (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) cs e_ol vs NSH_ph HS' HJ' HF HG Hfds Hfs
      Hrv Hsr Hchk Hsh eq_refl Hnth Hcf Hcs Hco Heo ltac:(unfold PSN.orig; apply nx_hw_range) Hr24). }
  repeat split; assumption.
Qed.

(* cap >= incl: the record is handed back at NP_fit. *)
Lemma hb_leaf_fit : forall (ms' : machine_state) md' ss' cs e_ol vs,
  st_ok_pi SEGS VAL E ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E (ss_mem hb_ss) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E (ss_regs ss') ->
  nx_land_chk true vs (ss_mem ss') = true -> map (fun v => v mod 256) vs = NSH_ph ->
  nth_error (ss_mem ss') 6 = Some (YP09.mkRegion (Some NA_PS) 0 PS_LEN 0 16 cs) ->
  In (YP09.mkChunk PS_F_OFF (CVal 8 (SOff HB_H 0))) cs ->
  In (YP09.mkChunk PS_SW_OFF (CVal 4 (SOff HB_SW 0))) cs ->
  In (YP09.mkChunk PS_OL_OFF (CVal 4 e_ol)) cs ->
  sv_denot E e_ol = Z_to_bv 64 (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  sr_get (ss_regs ss') 24 = SOff 554 0 ->
  ss_pc ss' = NP_fit ->
  getr (ms_regs ms') 10 = w64 (n_sw cx) ->
  getr (ms_regs ms') 12 = w64 (PSN.fb (nxF (n_C cx)) q) ->
  getr (ms_regs ms') 6 = w64 (PSN.fb (nxF (n_C cx)) (q + 1)) ->
  getr (ms_regs ms') 17 = w64 (PSN.fb (nxF (n_C cx)) (q + 2)) ->
  getr (ms_regs ms') 5 = w64 (PSN.fb (nxF (n_C cx)) (q + 3)) ->
  getr (ms_regs ms') 11 = w64 (PSN.fb (nxF (n_C cx)) (q + 4)) ->
  getr (ms_regs ms') 16 = w64 (PSN.fb (nxF (n_C cx)) (q + 5)) ->
  getr (ms_regs ms') 14 = w64 (PSN.fb (nxF (n_C cx)) (q + 6)) ->
  getr (ms_regs ms') 15 = w64 (PSN.fb (nxF (n_C cx)) (q + 7)) ->
  getr (ms_regs ms') 20 = w64 (n_buf cx) -> getr (ms_regs ms') 21 = w64 (n_ps cx) ->
  getr (ms_regs ms') 22 = w64 (-1) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  getr (ms_regs ms') 25 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  getr (ms_regs ms') 27 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  n_p cx <= q ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  0 < PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= n_cap cx ->
  nx_fit_inv B MT KS cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' ss' cs e_ol vs HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hsh Hnth Hcf Hcs Hco Heo Hr24 Hpc
    R10 R12 R6 R17 R5 R11 R16 R14 R15 R20 R21 R22 R23 R25 R27 Hpq Hch Hic.
  assert (Hk : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KFit \/
               PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KCutFit).
  { rewrite hb_kind_hdr. replace (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <=? n_cap cx) with true by (symmetry; apply Z.leb_le; lia).
    destruct (_ <=? _); [left | right]; reflexivity. }
  destruct (nx_chain_stop _ _ _ _ _ _ Hch ltac:(rewrite nxF_length; lia)
    ltac:(destruct Hk as [-> | ->]; discriminate) ltac:(destruct Hk as [-> | ->]; discriminate)) as (Hq' & Hlh').
  exists q. split.
  { rewrite <- Hpc.
    exact (hb_leaf_mid ms' md' ss' (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) cs e_ol vs NSH_ph HS' HJ' HF HG Hfds Hfs
      Hrv Hsr Hchk Hsh eq_refl Hnth Hcf Hcs Hco Heo ltac:(unfold PSN.orig; apply nx_hw_range) Hr24). }
  split; [exact Hq'|]. split; [unfold nx_lh; rewrite Hlh'; destruct Hk as [-> | ->]; reflexivity|].
  split; [exact Hpq|]. split; [exact Hic|].
  repeat split; assumption.
Qed.

(* ---- the words the engine computes, and what they are ---- *)
Definition hb_V0 : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 43 0) (SLit 8)) (SOff 42 0))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 44 0) (SLit 16)) (SAluw ALU_SLL (SOff 45 0) (SLit 24))).
Definition hb_Vsw : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAluw ALU_SLL (SOff 42 0) (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND hb_V0 (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 44 0) (SLit 8)) (SAluw ALU_SRL hb_V0 (SLit 24))).
Definition hb_O0 : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 47 0) (SLit 8)) (SOff 46 0))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 48 0) (SLit 16)) (SAlu ALU_SLL (SOff 49 0) (SLit 24))).
Definition hb_Osw : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 46 0) (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND hb_O0 (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 48 0) (SLit 8)) (SAluw ALU_SRL hb_O0 (SLit 24))).
Definition hb_Z32 (v : sv) : sv := SAlu ALU_SRL (SAlu ALU_SLL v (SLit 32)) (SLit 32).

Lemma hb_xw : forall n, (34 <= n < 50)%nat ->
  Z_to_bv 64 (bv_unsigned (ew E n) + 0) = Z_to_bv 64 (nx_hb (n_C cx) q (n - 34)).
Proof.
  intros n Hn. replace n with (34 + (n - 34))%nat at 1 by lia. rewrite hb_Ex by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma hb_xr : forall j, (j < 16)%nat -> 0 <= nx_hb (n_C cx) q j < 256.
Proof. intros j Hj. exact (proj1 (hb_hb j Hj)). Qed.

Lemma hb_incl_hb : forall b : bool,
  PSN.incl b (nxF (n_C cx)) q =
  if b then PSN.w32le (nx_hb (n_C cx) q 11) (nx_hb (n_C cx) q 10) (nx_hb (n_C cx) q 9) (nx_hb (n_C cx) q 8)
  else PSN.w32le (nx_hb (n_C cx) q 8) (nx_hb (n_C cx) q 9) (nx_hb (n_C cx) q 10) (nx_hb (n_C cx) q 11).
Proof.
  intros b. unfold PSN.incl. change 8 with (Z.of_nat 8).
  rewrite (nx_hw_hb b (n_C cx) q 8 Hq0 Hfull ltac:(lia) hb_xr). reflexivity.
Qed.
Lemma hb_orig_hb : forall b : bool,
  PSN.orig b (nxF (n_C cx)) q =
  if b then PSN.w32le (nx_hb (n_C cx) q 15) (nx_hb (n_C cx) q 14) (nx_hb (n_C cx) q 13) (nx_hb (n_C cx) q 12)
  else PSN.w32le (nx_hb (n_C cx) q 12) (nx_hb (n_C cx) q 13) (nx_hb (n_C cx) q 14) (nx_hb (n_C cx) q 15).
Proof.
  intros b. unfold PSN.orig. change 12 with (Z.of_nat 12).
  rewrite (nx_hw_hb b (n_C cx) q 12 Hq0 Hfull ltac:(lia) hb_xr). reflexivity.
Qed.
Lemma hb_fb_hb : forall j, (j < 16)%nat -> PSN.fb (nxF (n_C cx)) (q + Z.of_nat j) = nx_hb (n_C cx) q j.
Proof. intros j Hj. apply nx_fb_hb; [exact Hq0 | exact Hfull | exact Hj | exact (hb_xr j Hj)]. Qed.

Ltac hb_xs := rewrite ?(hb_xw 42%nat), ?(hb_xw 43%nat), ?(hb_xw 44%nat), ?(hb_xw 45%nat),
  ?(hb_xw 46%nat), ?(hb_xw 47%nat), ?(hb_xw 48%nat), ?(hb_xw 49%nat) by lia; cbn [Nat.sub].

Lemma hb_V0_den : sv_denot E hb_V0 = Z_to_bv 64 (bv_swrap 32 (PSN.incl false (nxF (n_C cx)) q)).
Proof.
  unfold hb_V0. cbn [sv_denot]. hb_xs. rewrite hb_incl_hb.
  apply nx_asm_lo; apply hb_xr; lia.
Qed.
Lemma hb_Vsw_den : sv_denot E hb_Vsw = Z_to_bv 64 (bv_swrap 32 (PSN.incl true (nxF (n_C cx)) q)).
Proof.
  unfold hb_Vsw. cbn [sv_denot]. rewrite hb_V0_den, (hb_incl_hb false). hb_xs. rewrite hb_incl_hb.
  apply (nx_asm_sw (nx_hb (n_C cx) q 8) (nx_hb (n_C cx) q 9) (nx_hb (n_C cx) q 10) (nx_hb (n_C cx) q 11));
    [apply hb_xr; lia .. | reflexivity].
Qed.
Lemma hb_O0_den : sv_denot E hb_O0 = Z_to_bv 64 (PSN.orig false (nxF (n_C cx)) q).
Proof.
  unfold hb_O0. cbn [sv_denot]. hb_xs. rewrite hb_orig_hb.
  apply nx_asm_lo64; apply hb_xr; lia.
Qed.
Lemma hb_Osw_den : sv_denot E hb_Osw = Z_to_bv 64 (PSN.orig true (nxF (n_C cx)) q).
Proof.
  unfold hb_Osw. cbn [sv_denot]. rewrite hb_O0_den, (hb_orig_hb false). hb_xs. rewrite hb_orig_hb.
  apply (nx_asm_sw64 (nx_hb (n_C cx) q 12) (nx_hb (n_C cx) q 13) (nx_hb (n_C cx) q 14) (nx_hb (n_C cx) q 15));
    [apply hb_xr; lia .. | reflexivity].
Qed.
Lemma hb_Z32_den : forall v I, sv_denot E v = Z_to_bv 64 (bv_swrap 32 I) -> 0 <= I < 2 ^ 32 ->
  sv_denot E (hb_Z32 v) = Z_to_bv 64 I.
Proof. intros v I Hv HI. unfold hb_Z32. cbn [sv_denot]. rewrite Hv. apply nx_zext32. exact HI. Qed.

Lemma hb_incl_rng : forall b, 0 <= PSN.incl b (nxF (n_C cx)) q < 2 ^ 32.
Proof. intros b. unfold PSN.incl. apply nx_hw_range. Qed.

(* the branch conditions *)
Lemma hb_br_eq0 : forall I, 0 <= I < 2 ^ 32 ->
  branch_taken BC_EQ (Z_to_bv 64 (bv_swrap 32 I)) (sv_denot E (SLit 0)) = (I =? 0).
Proof.
  intros I HI. cbn [branch_taken sv_denot]. unfold bv_eqb. rewrite nx_u_s32 by exact HI.
  rewrite unsigned_lit_small by lia.
  destruct (Z.ltb_spec I (2 ^ 31)); apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; lia.
Qed.
Lemma hb_br_geu : forall c I, 0 <= c < 2 ^ 64 -> 0 <= I < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 c) (Z_to_bv 64 I) = (I <=? c).
Proof.
  intros c I Hc HI. cbn [branch_taken]. unfold bv_ltu. rewrite !unsigned_lit_small by lia.
  destruct (Z.ltb_spec c I), (Z.leb_spec I c); try reflexivity; lia.
Qed.
Lemma hb_br_sw : branch_taken BC_EQ (sv_denot E (SOff 51 0)) (sv_denot E (SLit 0)) = (n_sw cx =? 0).
Proof.
  change (SOff 51 0) with (SOff HB_SW 0). rewrite hb_sv_sw. cbn [branch_taken sv_denot]. unfold bv_eqb. pose proof hb_sw01 as Hsw.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- the walk from NP_hd_ra, full header ---- *)
(* After a run: fold its frame, growth and model facts into the ones from the seat's state. *)
Local Ltac hb_book HFt HGt Hmd :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?mk)), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) _ |- _ =>
    let HFt2 := fresh "HFt" in let HGt2 := fresh "HGt" in let Hmd2 := fresh "Hmd" in
    pose proof (hb_frame_compose _ _ _ _ HFt HFr ltac:(vm_compute; reflexivity)) as HFt2;
    assert (HGt2 : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem mk))) by (intros x Hx; apply HG; apply HGt; exact Hx);
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing ?l ?mt ?mdk)) _ =>
      assert (Hmd2 : m_fds (with_vm_backing l mt mdk) = m_fds md3 /\ m_fs (with_vm_backing l mt mdk) = m_fs md3)
        by (rewrite (proj1 (hb_wb_md l mt mdk)), (proj2 (hb_wb_md l mt mdk)); exact Hmd) end;
    clear HFt HGt Hmd HF HFr HG; rename HFt2 into HFt; rename HGt2 into HGt; rename Hmd2 into Hmd
  end.

Local Ltac hb_run RUNP HS HJ0 HFt HGt Hmd :=
  paj_run_sh RUNP HS HJ0; [apply hb_awr_any; vm_compute; reflexivity | hb_book HFt HGt Hmd].
Local Ltac hb_run_to RUNTOP HS HJ0 stop HFt HGt Hmd :=
  paj_run_to_sh RUNTOP HS HJ0 stop; [apply hb_awr_any; vm_compute; reflexivity | hb_book HFt HGt Hmd].

Lemma hb_cur_reg : forall i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  sv_denot E (SOff (530 + i) 0) = getr (ms_regs ms3) r.
Proof.
  intros i r Hi Hr. rewrite hb_sv_cur by exact Hi. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hr. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma hb_a0_den : getr (ms_regs ms3) 10 = w64 (nx_hk (n_C cx) q) ->
  sv_denot E (SOff 540 0) = Z_to_bv 64 16.
Proof.
  intros Ha0. change (SOff 540 0) with (SOff (530 + 10) 0).
  rewrite (hb_cur_reg 10 (10%bv : bv 5)) by (try lia; vm_compute; reflexivity).
  rewrite Ha0, nx_hk_16 by exact Hfull. reflexivity.
Qed.


Local Ltac hb_rr HS :=
  lazymatch goal with |- context [getr (ms_regs ?m) ?r] => let H := fresh "H" in hb_reg HS r H; rewrite H; clear H end.
Local Ltac hb_cur n r :=
  lazymatch goal with |- sv_denot _ (SOff ?k 0) = _ =>
    change (SOff k 0) with (SOff (530 + n) 0); rewrite (hb_cur_reg n r) by (try lia; vm_compute; reflexivity) end.
Local Ltac hb_srok :=
  lazymatch goal with HE : nx_env cx fp ?Ex |- nx_sr_ok cx fp ?Ex ?sr =>
    apply (nx_sr_ok_std B KS cx fp HB Ex sr HE); vm_compute; reflexivity end.
Local Ltac hb_in := repeat (first [left; reflexivity | right]).

Lemma hb_den_F32 : sv_denot E (SOff NA_F NO_PH) = w64 (nF cx fp + NO_PH).
Proof.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as (_ & _ & _ & HF' & _).
  pose proof hb_geo as (_ & _ & _ & HF0 & HFc & _). pose proof asan_consts as (Hac & _).
  cbn [sv_denot]. rewrite HF'. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma hb_den_m1 : sv_denot E (SLit 18446744073709551615) = w64 (-1).
Proof. apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma hb_den_byte : forall n, (34 <= n < 50)%nat ->
  sv_denot E (SOff n 0) = w64 (PSN.fb (nxF (n_C cx)) (q + Z.of_nat (n - 34))).
Proof. intros n Hn. rewrite hb_sv_x by exact Hn. rewrite hb_fb_hb by lia. reflexivity. Qed.


Lemma hb_swrap_small : forall I, 0 <= I < 2 ^ 31 -> bv_swrap 32 I = I.
Proof.
  intros I HI. unfold bv_swrap. rewrite nx_wrap32. change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma hb_s9_low : forall I, 0 <= I < 2 ^ 32 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 I)) mod 2 ^ 32 = I.
Proof.
  intros I HI. rewrite nx_u_s32 by exact HI. destruct (Z.ltb_spec I (2 ^ 31)).
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (I + 2 ^ 64 - 2 ^ 32) (2 ^ 32) (2 ^ 32 - 1) I) by lia. reflexivity.
Qed.
Local Ltac hb_byte := rewrite hb_den_byte by lia; first [reflexivity | cbn [Nat.sub Z.of_nat]; rewrite Z.add_0_r; reflexivity].

Lemma hb_walk_full : forall POST R,
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_sk1_inv B MT KS R) ->
  nx_from SK B KS POST (nx_fit_inv B MT KS) ->
  nx_next_ok R cx q -> n_p cx <= q ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  getr (ms_regs ms3) 10 = w64 (nx_hk (n_C cx) q) ->
  getr (ms_regs ms3) 20 = w64 (n_buf cx) -> getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  getr (ms_regs ms3) 23 = w64 (n_cap cx) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST R HLOOP HSK1 HFIT HNX Hpq Hch Ha0 Hs4 Hs5 Hs7.
  pose proof hb_seat as HS.
  pose proof (hb_E_img cx fp (ms_regs ms3) q lh) as HEI.
  pose proof (hb_E_env cx fp (ms_regs ms3) q lh) as HE.
  pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
  pose proof (paj_branch (PI := PI)) as BR.
  pose proof HJ as HJ0.
  pose proof (frame_of_refl E (ss_mem hb_ss) (rdW W3 (ms_mem ms3))) as HFt.
  assert (HGt : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms3))) by (intros x Hx; exact Hx).
  assert (Hmd : m_fds md3 = m_fds md3 /\ m_fs md3 = m_fs md3) by (split; reflexivity).
  pose proof hb_sw01 as Hsw. pose proof hb_mid_h as Hh.
  assert (Hcap : 0 <= n_cap cx <= NX_CAP_MAX) by (destruct (hb_buf Hh) as (_ & _ & H); exact H).
  assert (Hsr : forall ss', ss_regs ss' = ss_regs ss' -> True) by (intros; exact I).
  (* 0x819bc .. the `bne a0,16` at 0x819c4 *)
  hb_run RUNP HS HJ0 HFt HGt Hmd.
  hb_branch BR HS Hc.
  { exfalso. rewrite (hb_a0_den Ha0) in Hc. cbn [branch_taken sv_denot] in Hc. rewrite bv_eqb_refl in Hc. discriminate Hc. }
  (* the header is whole: .. the `beqz a0` (ps->sw) at 0x81a04 *)
  clear Hc. hb_run RUNP HS HJ0 HFt HGt Hmd.
  hb_branch BR HS Hc2; rewrite hb_br_sw in Hc2.
  - assert (Esw : (n_sw cx =? 1) = false) by (apply Z.eqb_eq in Hc2; rewrite Hc2; reflexivity).
    clear Hc2.
    hb_run RUNP HS HJ0 HFt HGt Hmd.
    hb_branch BR HS Hc3.
    + fold hb_V0 in Hc3. rewrite hb_V0_den, hb_br_eq0 in Hc3 by apply hb_incl_rng.
      replace (PSN.incl false (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc3 by (rewrite Esw; reflexivity).
      apply Z.eqb_eq in Hc3.
      (* KEmpty: 0x81b00 .. `j` NP_loop *)
      hb_run_to RUNTOP HS HJ0 NP_loop HFt HGt Hmd.
      lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HLOOP cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
      lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
        eapply (hb_leaf_loop R m _ ss _ [241;241;241;241;18446744073709551608;18446744073709551608;243;243] HS HJ0 HFt HGt
          (proj1 Hmd) (proj2 Hmd)) end;
        [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | hb_in | hb_in | hb_in | vm_compute; reflexivity | vm_compute; reflexivity
        | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
        | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
        | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
        | hb_rr HS; exact hb_den_F32
        | exact HNX | exact Hpq | exact Hch | exact Hc3 ].
    + fold hb_V0 in Hc3. rewrite hb_V0_den, hb_br_eq0 in Hc3 by apply hb_incl_rng.
      replace (PSN.incl false (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc3 by (rewrite Esw; reflexivity).
      apply Z.eqb_neq in Hc3.
      (* .. the `bgeu s7,s11` at 0x81abc *)
      hb_run RUNP HS HJ0 HFt HGt Hmd.
      hb_branch BR HS Hc4;
        fold hb_V0 in Hc4; fold (hb_Z32 hb_V0) in Hc4;
        rewrite (hb_Z32_den hb_V0 _ hb_V0_den (hb_incl_rng false)) in Hc4;
        change (SOff 553 0) with (SOff (530 + 23) 0) in Hc4;
        rewrite (hb_cur_reg 23 (23%bv : bv 5)) in Hc4 by (try lia; vm_compute; reflexivity);
        rewrite Hs7 in Hc4; unfold w64 in Hc4;
        rewrite hb_br_geu in Hc4 by (pose proof (hb_incl_rng false); unfold NX_CAP_MAX in Hcap; lia);
        replace (PSN.incl false (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc4
          by (rewrite Esw; reflexivity).
      * (* cap >= incl: 0x81abc `bgeu` -> NP_fit *)
        apply Z.leb_le in Hc4.
        hb_run_to RUNTOP HS HJ0 NP_fit HFt HGt Hmd.
        lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HFIT cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
        pose proof (hb_incl_rng (n_sw cx =? 1)) as Hir.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
          eapply (hb_leaf_fit m _ ss _ hb_O0 [241;241;241;241;0;0;243;243] HS HJ0 HFt HGt (proj1 Hmd) (proj2 Hmd)) end;
          [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_in | hb_in | hb_in | rewrite Esw; exact hb_O0_den | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_rr HS; change (SOff 51 0) with (SOff HB_SW 0); exact hb_sv_sw
          | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte
          | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte
          | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
          | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
          | hb_rr HS; exact hb_den_m1
          | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
          | hb_rr HS; fold hb_V0; rewrite hb_V0_den, <- Esw, hb_swrap_small by (unfold NX_CAP_MAX in Hcap; lia); reflexivity
          | hb_rr HS; fold hb_V0; fold (hb_Z32 hb_V0); rewrite (hb_Z32_den hb_V0 _ hb_V0_den (hb_incl_rng false)), <- Esw; reflexivity
          | exact Hpq | exact Hch | lia ].
      * (* cap < incl: the fall-through to NP_sk1 0x81ac0 *)
        apply Z.leb_gt in Hc4.
        hb_run_to RUNTOP HS HJ0 NP_sk1 HFt HGt Hmd.
        lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HSK1 cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
          eapply (hb_leaf_sk1 R m _ ss _ hb_O0 [241;241;241;241;0;0;243;243] HS HJ0 HFt HGt (proj1 Hmd) (proj2 Hmd)) end;
          [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_in | hb_in | hb_in | rewrite Esw; exact hb_O0_den | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
          | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
          | hb_rr HS; exact hb_den_m1
          | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
          | hb_rr HS; fold hb_V0; rewrite hb_V0_den, hb_s9_low by apply hb_incl_rng; unfold nx_incl; rewrite Esw; reflexivity
          | hb_rr HS; exact hb_den_F32
          | exact HNX | exact Hch | unfold nx_incl; exact Hc3 | unfold nx_incl; exact Hc4 ].
  - assert (Esw : (n_sw cx =? 1) = true) by (apply Z.eqb_neq in Hc2; apply Z.eqb_eq; lia).
    clear Hc2.
    hb_run RUNP HS HJ0 HFt HGt Hmd.
    hb_branch BR HS Hc3.
    + fold hb_V0 in Hc3. fold hb_Vsw in Hc3. rewrite hb_Vsw_den, hb_br_eq0 in Hc3 by apply hb_incl_rng.
      replace (PSN.incl true (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc3 by (rewrite Esw; reflexivity).
      apply Z.eqb_eq in Hc3.
      (* KEmpty: 0x81b00 .. `j` NP_loop *)
      hb_run_to RUNTOP HS HJ0 NP_loop HFt HGt Hmd.
      lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HLOOP cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
      lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
        eapply (hb_leaf_loop R m _ ss _ [241;241;241;241;18446744073709551608;18446744073709551608;243;243] HS HJ0 HFt HGt
          (proj1 Hmd) (proj2 Hmd)) end;
        [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | hb_in | hb_in | hb_in | vm_compute; reflexivity | vm_compute; reflexivity
        | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
        | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
        | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
        | hb_rr HS; exact hb_den_F32
        | exact HNX | exact Hpq | exact Hch | exact Hc3 ].
    + fold hb_V0 in Hc3. fold hb_Vsw in Hc3. rewrite hb_Vsw_den, hb_br_eq0 in Hc3 by apply hb_incl_rng.
      replace (PSN.incl true (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc3 by (rewrite Esw; reflexivity).
      apply Z.eqb_neq in Hc3.
      (* .. the `bgeu s7,s11` at 0x81abc *)
      hb_run RUNP HS HJ0 HFt HGt Hmd.
      hb_branch BR HS Hc4;
        fold hb_V0 in Hc4; fold hb_Vsw in Hc4; fold (hb_Z32 hb_Vsw) in Hc4;
        rewrite (hb_Z32_den hb_Vsw _ hb_Vsw_den (hb_incl_rng true)) in Hc4;
        change (SOff 553 0) with (SOff (530 + 23) 0) in Hc4;
        rewrite (hb_cur_reg 23 (23%bv : bv 5)) in Hc4 by (try lia; vm_compute; reflexivity);
        rewrite Hs7 in Hc4; unfold w64 in Hc4;
        rewrite hb_br_geu in Hc4 by (pose proof (hb_incl_rng true); unfold NX_CAP_MAX in Hcap; lia);
        replace (PSN.incl true (nxF (n_C cx)) q) with (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in Hc4
          by (rewrite Esw; reflexivity).
      * (* cap >= incl: 0x81abc `bgeu` -> NP_fit *)
        apply Z.leb_le in Hc4.
        hb_run_to RUNTOP HS HJ0 NP_fit HFt HGt Hmd.
        lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HFIT cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
        pose proof (hb_incl_rng (n_sw cx =? 1)) as Hir.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
          eapply (hb_leaf_fit m _ ss _ hb_Osw [241;241;241;241;0;0;243;243] HS HJ0 HFt HGt (proj1 Hmd) (proj2 Hmd)) end;
          [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_in | hb_in | hb_in | rewrite Esw; exact hb_Osw_den | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_rr HS; change (SOff 51 0) with (SOff HB_SW 0); exact hb_sv_sw
          | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte
          | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte | hb_rr HS; hb_byte
          | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
          | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
          | hb_rr HS; exact hb_den_m1
          | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
          | hb_rr HS; fold hb_V0; fold hb_Vsw; rewrite hb_Vsw_den, <- Esw, hb_swrap_small by (unfold NX_CAP_MAX in Hcap; lia); reflexivity
          | hb_rr HS; fold hb_V0; fold hb_Vsw; fold (hb_Z32 hb_Vsw); rewrite (hb_Z32_den hb_Vsw _ hb_Vsw_den (hb_incl_rng true)), <- Esw; reflexivity
          | exact Hpq | exact Hch | lia ].
      * (* cap < incl: the fall-through to NP_sk1 0x81ac0 *)
        apply Z.leb_gt in Hc4.
        hb_run_to RUNTOP HS HJ0 NP_sk1 HFt HGt Hmd.
        lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HSK1 cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
          eapply (hb_leaf_sk1 R m _ ss _ hb_Osw [241;241;241;241;0;0;243;243] HS HJ0 HFt HGt (proj1 Hmd) (proj2 Hmd)) end;
          [ reflexivity | hb_srok | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_in | hb_in | hb_in | rewrite Esw; exact hb_Osw_den | vm_compute; reflexivity | vm_compute; reflexivity
          | hb_rr HS; hb_cur 20%nat (20%bv : bv 5); exact Hs4
          | hb_rr HS; hb_cur 21%nat (21%bv : bv 5); exact Hs5
          | hb_rr HS; exact hb_den_m1
          | hb_rr HS; hb_cur 23%nat (23%bv : bv 5); exact Hs7
          | hb_rr HS; fold hb_V0; fold hb_Vsw; rewrite hb_Vsw_den, hb_s9_low by apply hb_incl_rng; unfold nx_incl; rewrite Esw; reflexivity
          | hb_rr HS; exact hb_den_F32
          | exact HNX | exact Hch | unfold nx_incl; exact Hc3 | unfold nx_incl; exact Hc4 ].
Qed.

End f.

(* ---- the walk from NP_hd_ra, short read (k <> 16): NP_eof, then NP_exit ---- *)
Section g.
Variable q : Z.
Variable lh : option Z.
#[local] Notation E0 := (nx_mkE cx fp (ms_regs ms3)).
Hypothesis HM : nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
  (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3.
Hypothesis Hq : n_p cx <= q <= Z.of_nat (length (n_C cx)).
Hypothesis Hshort : Z.of_nat (length (n_C cx)) - q < 16.
Hypothesis Hch : nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh.

Lemma hb0_hk : nx_hk (n_C cx) q = Z.of_nat (length (n_C cx)) - q.
Proof. unfold nx_hk, NX_PH_LEN. lia. Qed.

Lemma hb0_seat : st_ok_pi SEGS VAL E0 hb_ss0 (restrict (w_H W3) ms3).
Proof.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HM as (Hbd & _).
  pose proof Hbd as ((_ & _ & _ & _ & _ & _ & Hnr & _ & _ & _ & _ & _ & H18 & H19 & _) & _).
  apply (nx_seat B KS LAWS TL cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 NP_hd_ra nx_sr NSH_ph 0 0 0 [] [] nx_facts0
    HE HEI Hbd (nx_regs_ok B KS cx fp ms3 HB Hnr H18 H19) ltac:(unfold NX_FRAME; lia) (Forall_nil _) ltac:(lia) ltac:(lia)
    ltac:(vm_compute; reflexivity) (Forall_nil _) I).
  - unfold nx_regions0. repeat constructor.
  - exact (nx_facts0_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 HE).
Qed.

Lemma hb0_HV : forall m', frame_of E0 (ss_mem hb_ss0) (rdW W3 (ms_mem ms3)) (rdW W3 m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ hb_wr cx fp a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
  intros m' HF a Ha Hn.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & _).
  apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 true NSH_ph 0 0 0 [] []
    (ms_mem ms3) m' HE HEI HF a Ha).
  - intros Hw. apply Hn. left. unfold NX_SPILL, NX_STK, AFREAD_STK in *. lia.
  - lia.
  - lia.
  - intros (r & Hin & _). destruct Hin.
Qed.

Lemma hb0_kind : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q =
  if Z.of_nat (length (n_C cx)) - q =? 0 then PSN.KEnd else PSN.KCutH.
Proof.
  unfold PSN.kind, PSN.flen. rewrite nxF_length.
  destruct (Z.eqb_spec (Z.of_nat (length (n_C cx)) - q) 0); [reflexivity|].
  replace (Z.of_nat (length (n_C cx)) - q <? 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* NP_exit with the model's result: the stream at the end of the file, nothing of the caller's
   written. *)
Lemma hb0_exit : forall (ms' : machine_state) md',
  nx_mid B MT KS cx fp NP_exit NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms' md' ->
  getr (ms_regs ms') 22 = w64 (if Z.of_nat (length (n_C cx)) - q =? 0 then 0 else -1) ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' HM' R22.
  destruct HM' as (Hbd & _ & Hjbk & HK & _ & Hh & Hps & _ & Hsrc & _ & Hbuf & Hts).
  pose proof hb0_kind as Hk.
  destruct (nx_chain_stop _ _ _ _ _ _ Hch ltac:(rewrite nxF_length; lia)
    ltac:(rewrite Hk; destruct (_ =? 0); discriminate) ltac:(rewrite Hk; destruct (_ =? 0); discriminate)) as (Hq' & Hlh').
  rewrite Hk in Hlh'.
  assert (Hkind : nx_kind (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q)
    by (unfold nx_kind, nx_q; rewrite Hq'; reflexivity).
  assert (Hfit : nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = false)
    by (unfold nx_fit; rewrite Hkind, Hk; destruct (_ =? 0); reflexivity).
  split; [exact Hbd|]. split; [exact Hjbk|].
  unfold nx_fin_at. hnf. right.
  split; [exact Hh|].
  split.
  { rewrite R22. unfold nx_res, nx_q. rewrite Hq'. unfold PSN.res_of. rewrite Hk.
    destruct (_ =? 0); reflexivity. }
  split; [exact HK|].
  split.
  { unfold nx_pos, nx_q. rewrite Hq'. unfold PSN.pos_of. rewrite Hk.
    replace (PSN.flen (nxF (n_C cx))) with (q + nx_hk (n_C cx) q)
      by (unfold PSN.flen; rewrite nxF_length, hb0_hk; lia).
    destruct (_ =? 0); exact Hsrc. }
  split.
  { unfold nx_orig, nx_vtag, nx_vid. rewrite Hfit. unfold nx_lh. rewrite Hlh'.
    replace (match (if Z.of_nat (length (n_C cx)) - q =? 0 then PSN.KEnd else PSN.KCutH) with
             | PSN.KEnd | PSN.KCutH => lh | _ => Some q end) with lh by (destruct (_ =? 0); reflexivity).
    exact Hps. }
  split.
  { destruct Hbuf as (bj' & Hg & Hl). exists bj'. split; [exact Hg|]. split; [exact Hl|].
    rewrite Hfit. intros H; discriminate H. }
  intros Hts0. unfold nx_tsv. rewrite Hfit. exact (proj1 (Hts Hts0)).
Qed.


Lemma hb0_leaf : forall (ms' : machine_state) md' ss',
  st_ok_pi SEGS VAL E0 ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E0 (ss_mem hb_ss0) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E0 (ss_regs ss') ->
  nx_land_chk true [241;241;241;241;0;0;243;243] (ss_mem ss') = true ->
  sr_get (ss_regs ss') 24 = SOff 554 0 -> ss_pc ss' = NP_exit ->
  getr (ms_regs ms') 22 = w64 (if Z.of_nat (length (n_C cx)) - q =? 0 then 0 else -1) ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' ss' HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hr24 Hpc R22.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HM as (_ & _ & _ & _ & _ & Hh & _).
  apply hb0_exit; [|exact R22].
  pose proof (nx_land_by B KS LAWS cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR E0 ss' [241;241;241;241;0;0;243;243] NSH_ph
    HE HEI HS' Hrv Hsr Hchk eq_refl eq_refl Hh) as Hbd.
  rewrite Hpc in Hbd.
  assert (Hs8 : getr (ms_regs ms') 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx))).
  { rewrite (st_ok_pi_restrict_reg _ E0 ss' ms' 24%bv HS'), Hr24.
    change (SOff 554 0) with (SOff (530 + 24) 0). rewrite nx_sv_SOff0, nx_mkE_cur by lia.
    change (Z_to_bv 5 (Z.of_nat 24)) with (Z_to_bv 5 24).
    replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    pose proof HM as (_ & H24 & _). exact H24. }
  pose proof HM as (_ & _ & _ & _ & _ & _ & (Vf & Vs & Vo & _) & _).
  pose proof hb_psfr as (Hown & Hpl & Hph & Hps8 & Hps4 & Hps47).
  pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & _).
  pose proof (nx_bases B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 HE HEI) as (_ & U60 & _).
  assert (Hpsb : forall x, n_ps cx <= x < n_ps cx + 16 -> mbyte SEGS (rdW W3 (ms_mem ms')) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x).
  { intros x Hx. apply (hb_mbyte_frame E0 (ss_mem hb_ss0) _ _ x HF); [unfold PS_LEN in *; lia|].
    intros (r & Hin & Hr). unfold hb_ss0, nx_ss, nx_regions, nx_regions0 in Hin. cbn [ss_mem app] in Hin.
    destruct (hb_geo_frame (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown Hpl Hph ltac:(unfold PS_LEN; lia)) as (_ & Hgc & _).
    destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base nx_saved_region nx_spill_region nx_frame_region nx_shadow_region
        got_regionP bcell_regionP] in Hr; try lia.
    rewrite U60 in Hr. pose proof asan_consts as (Hac & _). unfold NX_SPILL, NX_STK, AFREAD_STK, PS_LEN in *. lia. }
  assert (Vf' : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_F_OFF) 8 (n_h cx))
    by (eapply PcapSourceClose.vm_frame; [| exact Vf]; intros y Hy; apply Hpsb; cbn in Hy; unfold PS_F_OFF in *; lia).
  assert (Vs' : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_SW_OFF) 4 (n_sw cx))
    by (eapply PcapSourceClose.vm_frame; [| exact Vs]; intros y Hy; apply Hpsb; cbn in Hy; unfold PS_SW_OFF in *; lia).
  assert (Vo' : val_mem SEGS (rdW W3 (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx lh))
    by (eapply PcapSourceClose.vm_frame; [| exact Vo]; intros y Hy; apply Hpsb; cbn in Hy; unfold PS_OL_OFF in *; lia).
  exact (hb_mid_step (ms_mem ms') (hb0_HV (ms_mem ms') HF) (fun a Hp => apresent_grows _ _ _ a HG Hp)
    NP_hd_ra NSH_ph (q + nx_hk (n_C cx) q) (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx) ms' md' NP_exit NSH_ph
    (nx_ol cx lh) eq_refl HM Hbd Hs8 Hfds Hfs Vf' Vs' Vo').
Qed.

Lemma hb_walk_short : forall POST,
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  getr (ms_regs ms3) 10 = w64 (nx_hk (n_C cx) q) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST HEXIT Ha0.
  pose proof hb0_seat as HS.
  pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE.
  pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
  pose proof (paj_branch (PI := PI)) as BR.
  pose proof HJ as HJ0.
  pose proof HM as (_ & _ & _ & _ & _ & Hh0 & _).
  assert (Hk : 0 <= nx_hk (n_C cx) q < 16) by (rewrite hb0_hk; lia).
  assert (Ha0d : sv_denot E0 (SOff 540 0) = Z_to_bv 64 (nx_hk (n_C cx) q)).
  { change (SOff 540 0) with (SOff (530 + 10) 0). rewrite nx_sv_SOff0, nx_mkE_cur by lia.
    change (Z_to_bv 5 (Z.of_nat 10)) with (Z_to_bv 5 10).
    replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact Ha0. }
  assert (Hawr : awr_ok E0 (ss_mem hb_ss0) (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
    (ablocks B ly3 S3) ly3 ((NX_CID, fp) :: n_own cx)).
  { pose proof (nx_bases B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 HE HEI) as (U2 & U60 & _).
    pose proof hb_geo as (Hsp & Hsp47 & Hsp1 & _).
    assert (Hst : n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK /\ spZ (n_regs cx) <= n_sp0 cx) by (hb_base; lia).
    unfold hb_ss0, nx_ss, nx_regions, nx_regions0. cbn [ss_mem app].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_at _ _ _ _ _ _ _ _ _ _ NA_SP1 (n_sp1 cx)); [reflexivity | exact U60 | cbn; unfold NX_STK, AFREAD_STK in *; lia | cbn; unfold NX_SPILL; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  (* 0x819bc .. the `bne a0,16` at 0x819c4 *)
  paj_run_sh RUNP HS HJ0; [exact Hawr|].
  hb_branch BR HS Hc.
  2: { exfalso. rewrite Ha0d in Hc. cbn [branch_taken sv_denot] in Hc. unfold bv_eqb in Hc.
       rewrite !unsigned_lit_small in Hc by lia. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc. lia. }
  (* NP_eof 0x81b34: the `bnez a0` *)
  clear Hc.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) _ |- _ =>
    rename HFr into HFr1; rename HG into HG1; clear HF end.
  paj_run_sh RUNP HS HJ0; [intros a Ha; apply Hawr; exact Ha|].
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) _ |- _ =>
    rename HFr into HFr2; rename HG into HG2; clear HF end.
  hb_branch BR HS Hc2; rewrite Ha0d in Hc2; cbn [branch_taken sv_denot] in Hc2; unfold bv_eqb in Hc2;
    rewrite !unsigned_lit_small in Hc2 by lia.
  - (* k <> 0: KCutH, s6 = -1 *)
    apply Bool.negb_true_iff in Hc2. apply Z.eqb_neq in Hc2.
    paj_run_to_sh RUNTOP HS HJ0 NP_exit; [intros a Ha; apply Hawr; exact Ha|].
    lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HEXIT cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) _ |- _ =>
      pose proof (hb_frame_compose_g E0 _ _ _ _ _ (hb_frame_compose_g E0 _ _ _ _ _ HFr1 HFr2 ltac:(vm_compute; reflexivity)) HFr
        ltac:(vm_compute; reflexivity)) as HFt;
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
        assert (HGt : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem m))) by (intros x Hx; apply HG; apply HG2; apply HG1; exact Hx) end end.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      lazymatch goal with |- nx_exit_inv _ _ _ _ _ _ _ _ _ _ ?md => apply (hb0_leaf m md ss HS HJ0 HFt HGt) end end;
      [ repeat rewrite (proj1 (hb_wb_md _ _ _)); reflexivity
      | repeat rewrite (proj2 (hb_wb_md _ _ _)); reflexivity
      | reflexivity
      | apply (nx_sr_ok_std B KS cx fp HB E0 _ HE); vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | hb_reg HS (22%bv : bv 5) H22; rewrite H22; clear H22 ].
    replace (Z.of_nat (length (n_C cx)) - q =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite hb0_hk in Hc2; lia).
    apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity.
  - (* k = 0: KEnd, s6 := 0 *)
    apply Bool.negb_false_iff in Hc2. apply Z.eqb_eq in Hc2.
    paj_run_to_sh RUNTOP HS HJ0 NP_exit; [intros a Ha; apply Hawr; exact Ha|].
    lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ => apply (HEXIT cx fp k2 ly3 S3 W3 m md HB HJ0 HFR) end.
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) _ |- _ =>
      pose proof (hb_frame_compose_g E0 _ _ _ _ _ (hb_frame_compose_g E0 _ _ _ _ _ HFr1 HFr2 ltac:(vm_compute; reflexivity)) HFr
        ltac:(vm_compute; reflexivity)) as HFt;
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
        assert (HGt : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem m))) by (intros x Hx; apply HG; apply HG2; apply HG1; exact Hx) end end.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      lazymatch goal with |- nx_exit_inv _ _ _ _ _ _ _ _ _ _ ?md => apply (hb0_leaf m md ss HS HJ0 HFt HGt) end end;
      [ repeat rewrite (proj1 (hb_wb_md _ _ _)); reflexivity
      | repeat rewrite (proj2 (hb_wb_md _ _ _)); reflexivity
      | reflexivity
      | apply (nx_sr_ok_std B KS cx fp HB E0 _ HE); vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | hb_reg HS (22%bv : bv 5) H22; rewrite H22; clear H22 ].
    replace (Z.of_nat (length (n_C cx)) - q =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite hb0_hk in Hc2; lia).
    rewrite Ha0d. unfold w64. rewrite Hc2. reflexivity.
Qed.
End g.

End d.

(* ---------------------------------------------------------------------------------------------- *)
(* The phase                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* From the return of the header fread (NP_hd_ra, 0x819bc) to the four cuts that follow it: the
   record loop's head with the next turn (KEmpty), the skip test (cap < incl), the fit path
   (cap >= incl), and the exit (a short header: KCutH with -1, or the end of the file: KEnd with 0). *)
Theorem pb_nx_hdrB : forall (POST : ncx -> world SEGS -> config -> Prop) (R : ncx -> Z -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_sk1_inv B MT KS R) ->
  nx_from SK B KS POST (nx_fit_inv B MT KS) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  nx_from SK B KS POST (nx_hdra_inv B MT KS R).
Proof.
  intros POST R HLOOP HSK1 HFIT HEXIT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR
    (q & lh & HNX & HM & Ha0 & Hhdr & Hs4 & Hs5 & Hs7 & Hs10 & Hq & Hch).
  destruct (Z_lt_le_dec (Z.of_nat (length (n_C cx)) - q) 16) as [Hshort | Hfull].
  - eapply hb_walk_short; eassumption.
  - pose proof HM as (_ & _ & _ & _ & _ & Hh & _).
    assert (Hq0 : 0 <= q).
    { pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
      repeat match goal with H : n_h cx <> 0 -> _ |- _ => specialize (H Hh) end.
      repeat match goal with H : _ /\ _ |- _ => destruct H end. lia. }
    eapply hb_walk_full; try eassumption. lia.
Qed.

End c.
End b.
End a.
