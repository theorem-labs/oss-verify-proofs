(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module paths, module names and addresses changed; 871 of its 953 lines of code are new or changed and 1061 lines of the source are left out. *)
(* Segment C of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan, image B):
   BASE + 0x370 .. BASE + 0x440 (0x80ae4 .. 0x80bb4), 52 slots. seg_C_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_B_end to inv_rec 0, or, with no record, to inv_exit.

   The code (the neutral listing of fuzz_identity.asan-ubsan):
     0x80ae4  call __asan_memset (a0 = SF+432, a1 = 0, a2 = 12)  `hw` cleared (AMEMSET, YC85.aj_intrin_atS)
     0x80ae8 .. 0x80af8   mf+160 := s7 (the frame's shadow address), mf+32 := s3 (&hw), mf+136 := &id + 3
     0x80afc  beqz s2 (n = 0) to 0x81750: mf+24 := hw.have (0), s8 := 0, on to the exit 0x81764 (+0xff0)
     0x80b00 .. 0x80b0c   the UBSan pointer-overflow check of p + 1 (p >= 4096: never taken)
     0x80b14 .. 0x80b24   the ASan check of input[0]: the shadow byte of p; a nonzero byte goes to the
                          partial-granule re-check 0x82620 .. 0x82628 (p mod 8 = 0 < the byte: back to 0x80b28)
     0x80b28 .. 0x80b48   input[0] mod 65 through object 5's reciprocal (mulhu, slli 6, or, sub)
     0x80b3c, 0x80b40     mf+24 := hw.have (0)
     0x80b4c  s8 := n - 1;  0x80b50  mf+96 := nrec
     0x80b54  beqz nrec to 0x81760: s9 := p + 1, on to the exit 0x81764 (+0xff0)
     0x80b58 .. 0x80bb0   a4 := 0, a5 := 1, s9 := p + 1, and the hoisted machine-frame slots
                          mf+152, mf+144, mf+48, mf+104, mf+88, mf+176, mf+80, mf+72, mf+56
   The symbolic engine (IdentBPaLib paj_run_tok) runs each part; the input byte's shadow byte is a region of its
   own (atom 35 = SHADOW_OFF + p / 8, an alias of the address the code computes), and the run is cut in three
   by the input's length: n = 0, n >= 8 (the byte is 0) and 1 <= n < 8 (the byte is n). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here (shadow addresses, the frame's
   alignment) needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states ------------------------------------------------------------------------------------ *)
(* The call slot 0x80ae4: no region (the call reads nothing of the caller's memory itself). *)
Definition ss_cm : sstate := mkSS 0x370 sr_atoms [] None (mkFacts [] [] []).
(* After the call, 0x80ae8. Atoms: the registers; 32 = SHADOW_OFF (the shadow base at mf+168), 33 = input[0],
   34 = SF (the frame address at mf+64), 35 = SHADOW_OFF + p / 8 (the input byte's shadow cell), 36 = its value
   (1 <= n < 8 only); A_OBJ 5 = object 5. Region 0: the machine frame, base s1 (atom 9), writable on
   mf+24 .. mf+184. Region 1: hw.have at SF+432 (s3), 0 after the memset. *)
Definition c_mf : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 24 184
  [YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 34 352))].
Definition c_hw : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition c_shA : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition c_shB : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition c_in : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition c_o5 : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x03f03f03f03f03f1))].
Definition c_atoms0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
   (19%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF 4096 (2 ^ 47) 5)].
Definition c_atoms1 (lo36 hi36 : Z) : list (nat * afact) :=
  c_atoms0 ++ [(18%nat, mkAF 1 (2 ^ 26 - 1) 0); (25%nat, PTR 4); (33%nat, mkAF 0 255 0); (36%nat, mkAF lo36 hi36 0);
               (A_OBJ 5, mkAF IMG_LO IMG_TOP 0)].
Definition c_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 32 0), SOff 35 0)].
Definition ss_c0 : sstate := mkSS 0x374 sr_atoms [c_mf; c_hw] None (mkFacts c_atoms0 [] []).
(* With n >= 1 the state also holds the input byte's shadow cell (c_shA, 0, when n >= 8; c_shB, atom 36 = n, when
   n < 8), input[0] and object 5. *)
Definition ss_c1 (rsh : YP09.region) (lo36 hi36 : Z) : sstate :=
  mkSS 0x374 sr_atoms [c_mf; c_hw; rsh; c_in; c_o5] None (mkFacts (c_atoms1 lo36 hi36) [] c_alias).
(* The run reads no shadow through a token: the shadow base it computes with is atom 32, not Bx_c. *)
Definition Bx_c : sv := SLit SB.
(* The environment: the registers, then the five values above. *)
Definition c_extra (b0 SF p s : Z) : list word := map (Z_to_bv 64) [SB; b0; SF; SB + p / 8; s].

(* ---- input[0] mod 65 as the code computes it (0x80b30 .. 0x80b48): mulhu by object 5's reciprocal, the
   quotient times 65 as (q << 6) | q, and the subtraction; checked for every byte. *)
Definition c_f65 (b : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_SUB b
    (zcanon (zalu_raw 63 64 ALU_OR
      (zcanon (zalu_raw 63 64 ALU_SLL (zcanon (zmd_raw 64 M_MULHU b (zcanon 283796062672454641))) (zcanon 6)))
      (zcanon (zmd_raw 64 M_MULHU b (zcanon 283796062672454641)))))).
Lemma c_f65_ok : forall b, 0 <= b < 256 -> c_f65 b = b mod 65.
Proof.
intros b Hb.
assert (H : forallb (fun k => Z.eqb (c_f65 (Z.of_nat k)) (Z.of_nat k mod 65)) (seq 0 256) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat b)). rewrite in_seq in H. rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq. apply H. lia.
Qed.
Lemma c_nrec_U : forall E b, ew E 33 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SUB (SOff 33 0)
    (SAlu ALU_OR (SAlu ALU_SLL (SMd M_MULHU (SOff 33 0) (SLit 283796062672454641)) (SLit 6))
       (SMd M_MULHU (SOff 33 0) (SLit 283796062672454641)))) = b mod 65.
Proof.
intros E b H Hb. rewrite !U_SAlu, !U_SMd, !U_SLit. rewrite (U_atom E 33 b H) by lia. exact (c_f65_ok b Hb).
Qed.
(* `not` (0x80bac): xor with all ones. *)
Lemma c_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> zcanon (Z.lxor x (zcanon (-1))) = Z.lnot x mod 2 ^ 64.
Proof.
intros x Hx. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (Z.ones 64).
apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 64) as [Hl | Hh].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec, Z.lnot_spec by lia.
  rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- small lemmas -------------------------------------------------------------------------------------------- *)
Lemma c_garr8_moved : forall segs H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros segs H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma c_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma c_vm1 : forall segs H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma c_vm0 : forall segs H (m : word -> option byte) a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview segs H m (a + i) = Some 0) -> val_mem segs (mrestrict H m) a n 0.
Proof.
intros segs H m a n Hz k Hk. pose proof (c_vm1 segs H m (a + Z.of_nat k) 0 (Hz (Z.of_nat k) ltac:(lia)) 0%nat ltac:(lia))
  as Hb.
rewrite Z.add_0_r in Hb. rewrite Hb. f_equal. unfold YO0f.le_byte.
rewrite !Z.mod_0_l by (try apply Z.pow_nonzero; lia). rewrite !Z.shiftr_0_l. rewrite !Z.mod_0_l by lia. reflexivity.
Qed.
Lemma c_vm_mod : forall segs m a (n : nat) v v',
  v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) -> val_mem segs m a n v -> val_mem segs m a n v'.
Proof. intros segs m a n v v' Hm Hv k Hk. rewrite (Hv k Hk). unfold YO0f.le_byte. rewrite Hm. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation acut := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation ecommon := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation e_pre := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation inv_B_end := (inv_B_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation inv_rec := (inv_rec B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation inv_exit := (inv_exit B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation hblocks := (hblocks B).
#[local] Notation rec_live := (rec_live B).

(* +0x374 (0x80ae8), after the memset: `hw`'s twelve bytes are 0; the rest is inv_B_end's. *)
Definition c_mid (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf 0 (BASE + 0x374)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos 0 W2 mem2 /\ hblocks g ly2 S2 [] /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
getr regs2 19 = w64 (SFa g pos + V_hw) /\ getr regs2 18 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g) /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 /\
(forall i, 0 <= i < N_hw -> aview SEGS (w_H W2) mem2 (SFa g pos + V_hw + i) = Some 0)).

Lemma c_memset : forall g pos mf W2 c2, inv_B_end g pos mf W2 c2 -> SRr SEGS W2 c2 (c_mid g pos mf).
Proof.
intros g pos mf W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hid & Hbl & Hmid & Hsh & R19 & R10 & R11 & R12 & R18 & R25 & Sh0 & Sh8).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
(* the machine state at the call slot *)
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (HS : st_ok_pi SEGS VAL E ss_cm
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x370)) mem2 (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. unfold ss_cm. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (AGE : env_agree 32 (Ereg regs2 []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (SHOK : sh_ok SEGS Bx_c [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x370)) with (Z_to_bv 64 (BASE + 0x370)).
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
(* at the memset's entry: the registers it receives *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E (ss_mem ss_cm) (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10. rewrite (EE 11%nat 11%bv eq_refl), R11 in Q11.
rewrite (EE 12%nat 12%bv eq_refl), R12 in Q12. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
assert (HPR : aregs_preserved regs2 (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 (@nil word) HS); [exact AGE | vm_compute; reflexivity]. }
pmkst HS.
pose proof (proj1 HJ) as HARm.
assert (HSFapp' : SF + 1024 <= 0x7fff7000 \/ (0x10007fff8000 <= SF /\ SF + 1024 <= alloc_ceiling)).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp. clear - HSFapp. lia. }
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET W2 (ms_regs ms) (ms_mem ms)
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ 0 (SF + V_hw) 0 12 (mf - sp0)
    (Z_to_bv 64 (BASE + 0x374)) HJ).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - unfold V_hw. clear - HSF0. lia.
  - unfold V_hw. clear - HSF1 C1. lia.
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Hmf0 Hmfb Hshi H47 C1; lia). ring.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - rewrite Hes. clear - Hmfb HSTK' Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. unfold V_hw in Ha. split.
    + right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. clear - Ha. lia.
    + rewrite Hes. clear - Ha HSF1 Hmf0 C1. lia.
  - unfold amem_range, V_hw. rewrite C5, C3, C4. clear - HSFapp' C1. lia.
  - intros x Hx. unfold V_hw in Hx. unfold shadow_of_addr.
    rewrite KEEP0 by (unfold SHADOW_OFF; clear - Hx HSF0 HSF1 C1; lia).
    destruct (Z_lt_le_dec x (SF + V_hw + 8)) as [Hlo | Hhi].
    + exists 0. split; [|left; reflexivity]. rewrite <- Sh0. f_equal. unfold shadow_addr, V_hw in *.
      clear - Hx Hlo HSF64. lia.
    + exists 4. split; [rewrite <- Sh8; f_equal; unfold shadow_addr, V_hw in *; clear - Hx Hhi HSF64; lia|].
      right. unfold V_hw in Hhi. clear - Hx Hhi HSF64. lia.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ 4 pos (SF + V_hw) 12 HARm Hin4);
    rewrite ?EFa, ?HFB; unfold V_hw; lia.
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Heff & Hfr3 & _ & _).
(* what the memset kept: everything but `hw` and its own stack window below mf *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 432 <= a < SF + 444) -> ~ (mf - 4096 <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2. rewrite (Hfr3 a Ha) by (unfold V_hw; rewrite ?Hes; clear - H1 H2; lia). apply KEEP0. exact Ha. }
clear Hfr3 KEEP0 HF HFr HG.
pose proof (aregs_preserved_trans _ _ _ HPR HP3) as HPR3.
assert (RR : forall r : Z, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HPR3.
assert (E2 : getr regs3 2 = getr regs2 2) by exact (RR 2 ltac:(unfold acallee_saved; lia)).
assert (E9 : getr regs3 9 = getr regs2 9) by exact (RR 9 ltac:(unfold acallee_saved; lia)).
assert (E8 : getr regs3 8 = getr regs2 8) by exact (RR 8 ltac:(unfold acallee_saved; lia)).
assert (E3 : getr regs3 3 = getr regs2 3) by exact (RR 3 ltac:(unfold acallee_saved; lia)).
assert (E4 : getr regs3 4 = getr regs2 4) by exact (RR 4 ltac:(unfold acallee_saved; lia)).
assert (E18 : getr regs3 18 = getr regs2 18) by exact (RR 18 ltac:(unfold acallee_saved; lia)).
assert (E19 : getr regs3 19 = getr regs2 19) by exact (RR 19 ltac:(unfold acallee_saved; lia)).
assert (E23 : getr regs3 23 = getr regs2 23) by exact (RR 23 ltac:(unfold acallee_saved; lia)).
assert (E25 : getr regs3 25 = getr regs2 25) by exact (RR 25 ltac:(unfold acallee_saved; lia)).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
(* the transports *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= 2 ^ 47 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 HSF1 C1; lia. }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= 432 \/ 444 <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 mem3) (SF + off) n v).
{ intros off n v H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H0 H1 H2 Hkk HSF0 HSF1 Hmf0 C1; lia. }
assert (SHK : forall a, 0 <= a < 2 ^ 47 -> aview SEGS (w_H W2) mem3 (shadow_addr a) = aview SEGS (w_H W2) mem2 (shadow_addr a)).
{ intros a Ha. apply KEEP; unfold shadow_addr, SHADOW_OFF; clear - Ha HSF0 HSF1 HSFapp' Hmf0 C1; lia. }
apply SRr_ret. unfold c_mid, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite E2; exact Rsp|]. split; [rewrite E9; exact Rs1|]. split; [rewrite E8; exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite E3; exact Rgp|]. split; [rewrite E4; exact Rtp|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact V104]|].
  split; [apply VMF; [clear; lia | clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold bytes_at8 in *. apply (c_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hinb].
  intros j Hj. rewrite length_map, <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hpce & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine2 Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply KEEP; clear - Hj Hpce Hp4096 Hrq Hdf Hmf0 C1; lia. }
change (SFa g pos) with SF.
split.
{ destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
  - unfold bytes_at8 in *. apply (c_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hidb].
    intros j Hj. rewrite length_map in Hj. unfold m_id in Hj. rewrite SlotModel.rec_id_length in Hj.
    unfold RcIdentModel.ID_SIZE in Hj. apply KEEP; unfold V_id; clear - Hj HSF0 HSF1 Hmf0 C1; lia.
  - unfold sh_zero in *. apply (c_zero_shadow_moved (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + V_id) N_id); [|exact Hidz].
    intros ii Hii. unfold N_id in Hii. unfold shadow_of_addr. apply KEEP; unfold V_id, SHADOW_OFF;
    clear - Hii HSF0 HSF1 HSFapp' Hmf0 C1; lia.
  - unfold sh_blk in *. apply (block_shadow_agree (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + V_id) N_id); [|exact Hidk].
    intros ii Hii. unfold N_id in Hii. unfold shadow_of_addr. apply KEEP; unfold V_id, SHADOW_OFF;
    clear - Hii HSF0 HSF1 HSFapp' Hmf0 C1; lia. }
split; [exact Hbl|].
split; [unfold mf_id in *; apply VMS; [clear - Hmfb; lia | clear - Hmfb Hshi H47; lia | exact Hmid]|].
split; [unfold sh_reg in *; rewrite E23; exact Hsh|].
split; [rewrite E19; exact R19|]. split; [rewrite E18; exact R18|]. split; [rewrite E25; exact R25|].
split; [rewrite SHK by (unfold V_hw; clear - HSF0 HSF1 C1; lia); exact Sh0|].
split; [rewrite SHK by (unfold V_hw; clear - HSF0 HSF1 C1; lia); exact Sh8|].
intros i Hi. unfold N_hw in Hi. rewrite (Heff i Hi). reflexivity.
Qed.

(* ---- the facts every end of the segment shares ------------------------------------------------------------ *)
(* Where the frame and the machine frame are, from the journal. *)
Lemma c_geo : forall g pos mf ly2 S2 W2 mem2 md2 k,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k ->
  frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  frame_addr ly2 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  SFa g pos mod 64 = 0 /\
  (SFa g pos + 1024 <= 0x7fff7000 \/ (0x10007fff8000 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling)) /\
  alloc_ceiling + 16384 <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmfb.
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity. assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64|].
split; [clear - HSFapp; lia|]. split; [clear - Hmfb Hceil Hslo HSTK' Has; lia|].
split; [clear - Hshi H47; lia|]. split; [exact Hsp0al | exact C1].
Qed.

(* What a run that writes only mf+24 .. mf+184 keeps of the state after the memset. *)
Lemma c_common_of : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
  ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem4 md4 0 ->
  frames S2 = [(4, pos)] -> hblocks g ly2 S2 [] ->
  id_at g pos 0 W2 mem2 -> mf_id g pos mf W2 mem2 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
  (forall i, 0 <= i < N_hw -> aview SEGS (w_H W2) mem2 (SFa g pos + V_hw + i) = Some 0) ->
  getr regs4 2 = getr regs2 2 -> getr regs4 9 = getr regs2 9 -> getr regs4 8 = getr regs2 8 ->
  getr regs4 3 = getr regs2 3 -> getr regs4 4 = getr regs2 4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 24 <= a < mf + 184) ->
    aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
  val_mem SEGS (rd W2 mem4) (mf + 64) 8 (SFa g pos) -> val_mem SEGS (rd W2 mem4) (mf + 168) 8 SHADOW_OFF ->
  ecommon g pos mf ly2 S2 W2 regs4 mem4 md4 /\ id_at g pos 0 W2 mem4 /\ mf_id g pos mf W2 mem4 /\
  hw_mem g pos 0 W2 mem4 /\ val_mem SEGS (rd W2 mem4) (SFa g pos + V_hw) 4 0.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HC HJ4 Hfrs Hbl Hid Hmid Sh0 Sh8 Hz E2 E9 E8 E3 E4 KEEP V64' V168'.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct (c_geo g pos mf ly2 S2 W2 mem4 md4 0 HJ4 Hfrs Hmfb)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Hmf0 & H47 & Hsp0al & C1).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ4 as (HAR4 & _).
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [Efd Efs].
assert (VK : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= mf + 24 \/ mf + 184 <= a) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem4) a n v).
{ intros a n v H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem4 a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H0 H1 H2 Hkk; lia. }
assert (SHK : forall a, 0 <= a < 2 ^ 47 -> aview SEGS (w_H W2) mem4 (shadow_addr a) = aview SEGS (w_H W2) mem2 (shadow_addr a)).
{ intros a Ha. apply KEEP; unfold shadow_addr, SHADOW_OFF; clear - Ha Hmf0 C1; lia. }
assert (FK : forall a, SF <= a < SF + 1024 -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP; clear - Ha HSF0 HSF1 Hmf0 C1; lia. }
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite E2; exact Rsp|]. split; [rewrite E9; exact Rs1|]. split; [rewrite E8; exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite E3; exact Rgp|]. split; [rewrite E4; exact Rtp|].
  split; [apply VK; [clear - Hmf0 C1; lia | clear - Hmfb H47; lia | clear; lia | exact V16]|].
  split; [exact V64'|].
  split; [apply VK; [clear - Hmf0 C1; lia | clear - Hmfb H47; lia | clear; lia | exact V192]|].
  split; [exact V168'|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V64b]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmfb H47; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VK; [clear - HSF0; lia | clear - HSF1 C1; lia | clear - HSF1 Hmf0; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold bytes_at8 in *. apply (c_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem4 _ _); [|exact Hinb].
  intros j Hj. rewrite length_map, <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem4 md4 (e_p g) (e_n g) HAR4 Hine2) as (_ & Hp4096 & Hpce & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply KEEP; clear - Hj Hpce Hp4096 Hrq Hmf0 C1; lia. }
change (SFa g pos) with SF.
split.
{ destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
  - unfold bytes_at8 in *. apply (c_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem4 _ _); [|exact Hidb].
    intros j Hj. rewrite length_map in Hj. unfold m_id in Hj. rewrite SlotModel.rec_id_length in Hj.
    unfold RcIdentModel.ID_SIZE in Hj. apply FK. unfold V_id. clear - Hj. lia.
  - unfold sh_zero in *. apply (c_zero_shadow_moved (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + V_id) N_id); [|exact Hidz].
    intros ii Hii. unfold N_id in Hii. unfold shadow_of_addr. apply KEEP; unfold V_id, SHADOW_OFF;
    clear - Hii HSF0 HSF1 Hmf0 C1; lia.
  - unfold sh_blk in *. apply (block_shadow_agree (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + V_id) N_id); [|exact Hidk].
    intros ii Hii. unfold N_id in Hii. unfold shadow_of_addr. apply KEEP; unfold V_id, SHADOW_OFF;
    clear - Hii HSF0 HSF1 Hmf0 C1; lia. }
split; [unfold mf_id in *; apply VK; [clear - Hmf0 C1; lia | clear - Hmfb H47; lia | clear; lia | exact Hmid]|].
assert (HZ4 : forall i, 0 <= i < N_hw -> aview SEGS (w_H W2) mem4 (SF + V_hw + i) = Some 0).
{ intros i Hi. rewrite FK by (unfold V_hw, N_hw in *; clear - Hi; lia). exact (Hz i Hi). }
unfold hw_mem. change (SFa g pos) with SF.
split.
{ split; [|split].
  - unfold bytes_at8, garr8. unfold m_hwb, SlotModel.rec_hwb. cbn [SlotModel.rec_hw].
    intros j Hj. rewrite length_map, repeat_length in Hj.
    assert (Hn : nth j (map (fun b : byte => bv_unsigned b) (repeat (RcIdentModel.zb 0) 8)) 0 = 0)
      by (clear - Hj; do 8 (destruct j as [|j]; [reflexivity|]); lia).
    rewrite Hn. split; [|lia].
    apply c_vm1. replace (SF + V_hw + 4 + Z.of_nat j) with (SF + V_hw + (4 + Z.of_nat j)) by lia.
    apply HZ4. unfold N_hw. lia.
  - unfold sh_zero, zero_shadow. intros i Hi. unfold N_hw in Hi. change (12 / 8) with 1 in Hi.
    assert (i = 0) by lia. subst i. rewrite Z.add_0_r. unfold shadow_of_addr.
    change (SHADOW_OFF + (SF + V_hw) / 8) with (shadow_addr (SF + V_hw)).
    rewrite SHK by (unfold V_hw; clear - HSF0 HSF1 C1; lia). exact Sh0.
  - unfold sh_blk, block_shadow. split; [unfold V_hw; clear - HSF64; lia|]. split; [unfold N_hw; lia|].
    intros i Hi. unfold N_hw in Hi. change ((12 + 7) / 8) with 2 in Hi. unfold shadow_of_addr.
    change (SHADOW_OFF + (SF + V_hw) / 8) with (shadow_addr (SF + V_hw)).
    assert (Hi01 : i = 0 \/ i = 1) by lia. destruct Hi01 as [-> | ->].
    + rewrite Z.add_0_r, SHK by (unfold V_hw; clear - HSF0 HSF1 C1; lia). exact Sh0.
    + replace (shadow_addr (SF + V_hw) + 1) with (shadow_addr (SF + V_hw + 8))
        by (unfold shadow_addr, V_hw; clear - HSF64; lia).
      rewrite SHK by (unfold V_hw; clear - HSF0 HSF1 C1; lia). exact Sh8. }
apply c_vm0. intros i Hi. apply HZ4. unfold N_hw. lia.
Qed.

(* The two ends of the segment, from the state after the memset and what the last run computed. *)
Lemma c_exit_of : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
  ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem4 md4 0 ->
  frames S2 = [(4, pos)] -> mo_le MT (e_S g) S2 (0 * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  hblocks g ly2 S2 [] -> id_at g pos 0 W2 mem2 -> mf_id g pos mf W2 mem2 -> sh_reg g pos regs2 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
  (forall i, 0 <= i < N_hw -> aview SEGS (w_H W2) mem2 (SFa g pos + V_hw + i) = Some 0) ->
  m_nrec g = 0%nat ->
  getr regs4 2 = getr regs2 2 -> getr regs4 9 = getr regs2 9 -> getr regs4 8 = getr regs2 8 ->
  getr regs4 3 = getr regs2 3 -> getr regs4 4 = getr regs2 4 -> getr regs4 23 = getr regs2 23 ->
  getr regs4 25 = w64 (e_p g + m_cur g 0) -> getr regs4 24 = w64 (e_n g - m_cur g 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 24 <= a < mf + 184) ->
    aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
  val_mem SEGS (rd W2 mem4) (mf + 64) 8 (SFa g pos) -> val_mem SEGS (rd W2 mem4) (mf + 168) 8 SHADOW_OFF ->
  val_mem SEGS (rd W2 mem4) (mf + 24) 8 0 -> val_mem SEGS (rd W2 mem4) (mf + 32) 8 (SFa g pos + V_hw) ->
  val_mem SEGS (rd W2 mem4) (mf + 136) 8 (SFa g pos + V_id + 3) ->
  val_mem SEGS (rd W2 mem4) (mf + 160) 8 (shadow_addr (SFa g pos)) ->
  inv_exit g pos mf W2 (cfg_at SEGS (BASE + 0xff0) regs4 mem4 md4).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HC HJ4 Hfrs MLE MOK Hbl Hid Hmid Hsh Sh0 Sh8 Hz Hnr
  E2 E9 E8 E3 E4 E23 R25 R24 KEEP V64' V168' V24' V32' V136' V160'.
destruct (c_common_of g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HC HJ4 Hfrs Hbl Hid Hmid Sh0 Sh8 Hz
  E2 E9 E8 E3 E4 KEEP V64' V168') as (HC4 & Hid4 & Hmid4 & Hhw4 & Vhw4).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _).
unfold inv_exit, acut. rewrite Hnr.
exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfrs|]. split; [unfold EV_LLVMF; lia|].
split; [exact MLE|]. split; [exact MOK|]. split; [exact HC4|].
split; [exact Hid4|].
split; [split; [exact Hhw4|]; split; [exact Vhw4|]; exact V24'|].
split; [exact Hbl|]. split; [exact V32'|]. split; [exact V136'|]. split; [exact V160'|].
split; [exact Hmid4|]. split; [unfold sh_reg in *; rewrite E23; exact Hsh|].
split; [|exact R24].
split; [exact R25|]. unfold m_cur. cbn [SlotModel.rec_c]. unfold SlotModel.nlen. rewrite <- Hlen.
pose proof (Z.le_min_l 1 (e_n g)). pose proof (Z.le_min_r 1 (e_n g)).
assert (0 <= e_n g) by (rewrite Hlen; lia). lia.
Qed.

Lemma c_rec0_of : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
  ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem4 md4 0 ->
  frames S2 = [(4, pos)] -> mo_le MT (e_S g) S2 (0 * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  hblocks g ly2 S2 [] -> id_at g pos 0 W2 mem2 -> mf_id g pos mf W2 mem2 -> sh_reg g pos regs2 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
  (forall i, 0 <= i < N_hw -> aview SEGS (w_H W2) mem2 (SFa g pos + V_hw + i) = Some 0) ->
  (0 < m_nrec g)%nat ->
  getr regs4 2 = getr regs2 2 -> getr regs4 9 = getr regs2 9 -> getr regs4 8 = getr regs2 8 ->
  getr regs4 3 = getr regs2 3 -> getr regs4 4 = getr regs2 4 -> getr regs4 23 = getr regs2 23 ->
  getr regs4 14 = w64 0 -> getr regs4 15 = w64 1 ->
  getr regs4 25 = w64 (e_p g + m_cur g 0) -> getr regs4 24 = w64 (e_n g - m_cur g 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 24 <= a < mf + 184) ->
    aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
  val_mem SEGS (rd W2 mem4) (mf + 64) 8 (SFa g pos) -> val_mem SEGS (rd W2 mem4) (mf + 168) 8 SHADOW_OFF ->
  val_mem SEGS (rd W2 mem4) (mf + 24) 8 0 -> val_mem SEGS (rd W2 mem4) (mf + 96) 8 (SlotModel.nrec (e_pl g)) ->
  mf_fixed g pos mf W2 mem4 -> mf_before g pos mf W2 mem4 -> mf_again g pos mf W2 mem4 ->
  inv_rec g pos mf 0 W2 (cfg_at SEGS (BASE + 0x440) regs4 mem4 md4).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HC HJ4 Hfrs MLE MOK Hbl Hid Hmid Hsh Sh0 Sh8 Hz Hnr
  E2 E9 E8 E3 E4 E23 R14 R15 R25 R24 KEEP V64' V168' V24' V96' Hfix Hbef Hag.
destruct (c_common_of g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HC HJ4 Hfrs Hbl Hid Hmid Sh0 Sh8 Hz
  E2 E9 E8 E3 E4 KEEP V64' V168') as (HC4 & Hid4 & Hmid4 & Hhw4 & Vhw4).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
unfold inv_rec, acut.
exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfrs|]. split; [unfold EV_LLVMF; lia|].
split; [exact MLE|]. split; [exact MOK|]. split; [exact HC4|].
split; [exact Hnr|]. split; [exact R14|]. split; [exact R15|]. split; [exact R24|].
split; [unfold sh_reg in *; rewrite E23; exact Hsh|].
unfold rec_live.
split; [exact V96'|]. split; [exact Hfix|]. split; [exact Hbef|]. split; [exact Hag|]. split; [exact Hmid4|].
split.
{ split; [exact R25|]. unfold m_cur. cbn [SlotModel.rec_c]. unfold SlotModel.nlen. rewrite <- Hlen.
  pose proof (Z.le_min_l 1 (e_n g)). pose proof (Z.le_min_r 1 (e_n g)).
  assert (0 <= e_n g) by (rewrite Hlen; lia). lia. }
split; [exact Hid4|].
split; [split; [exact Hhw4|]; split; [exact Vhw4|]; exact V24'|].
exact Hbl.
Qed.

(* ---- reading the symbolic state at the end of a run --------------------------------------------------------- *)
Lemma c_chunk : forall E ss ms i r off (n : N) e b v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_pi_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.
(* The value of the chunk at offset off of region i of HS's state, at base b (Hb : the base atom's value). *)
Ltac c_ck HS i off b Hb :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem ss) in
    let r := eval vm_compute in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    let c := eval vm_compute in (List.find (fun c => Z.eqb (YP09.c_off c) off) (YP09.r_chunks r)) in
    lazymatch c with Some (YP09.mkChunk _ (CVal ?n ?e)) =>
      apply (c_chunk E ss msr i r off n e b _ HS ltac:(vm_compute; reflexivity)
        ltac:(cbn [base_val YP09.r_base]; exact Hb)
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])))
    end
  end.
(* The write windows of a run over [c_mf; ...]: only the machine frame's mf+24 .. mf+184. *)
Ltac c_awr U9 mf sp0 :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo] | cbn [YP09.r_whi] | ];
  [ .. | repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil ].
Ltac c_win U9 :=
  intros ?bb ?wlo ?whi ?aa ?Hin ?Hr; cbn in Hin;
  repeat (destruct Hin as [?Eq | Hin]; [injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9 in Hr; cbv beta; lia|]);
  destruct Hin.

(* ---- n = 0: the guard 0x80afc is taken, 0x81750 .. 0x8175c, the exit -------------------------------------- *)
Lemma c_n0 : forall g pos mf W2 c2, c_mid g pos mf W2 c2 -> e_n g = 0 ->
  SRr SEGS W2 c2 (fun W3 c3 => m_nrec g = 0%nat /\ inv_exit g pos mf W3 c3).
Proof.
intros g pos mf W2 c2 Hst Hn0.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hbl & Hmid & Hsh & R19 & R18 & R25 & Sh0 & Sh8 & Hz).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & V64 & _ & V168 & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _).
destruct (c_geo g pos mf ly2 S2 W2 mem2 md2 0 HJ Hfrs Hmfb)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Hmf0 & H47 & Hsp0al & C1).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hnr : m_nrec g = 0%nat).
{ unfold m_nrec, SlotModel.nrecn, SlotModel.nrec, SlotModel.inb. rewrite Hn0 in Hlen.
  destruct (e_pl g) as [|b0 pl']; [reflexivity | cbn [length] in Hlen; lia]. }
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
remember (Eimg (Ereg regs2 (c_extra 0 SF 0 0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 SF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (ER : regs_ok E sr_atoms regs2) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = SF + V_hw).
{ rewrite (EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small. unfold V_hw. clear - HSF0 HSF1 C1. lia. }
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U34 : bv_unsigned (ew E 34) = SF) by (rewrite E34; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (HS : st_ok_pi SEGS VAL E ss_c0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x374)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_c0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold c_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmfb H47; lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho Hmfb HSTK' Has. lia.
      * constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 34 0) SF);
           [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - HSF0 HSF1 C1; lia | lia | exact V64].
        -- apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SB);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; lia | lia | exact V168].
        -- apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 34 352) (SF + V_id));
           [cbn [sv_denot]; rewrite U34; reflexivity | unfold V_id; clear - HSF0 HSF1 C1; lia | lia | exact Hmid].
    + unfold c_hw, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [unfold V_hw; clear - HSF0; lia|]. split; [unfold V_hw; clear - HSF1 C1; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_hw) 0 4 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply c_vm0. intros i Hi. apply Hz. unfold N_hw. cbn in Hi. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, c_mf, c_hw. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    unfold V_hw. clear - HSF1 Hmf0. lia.
  - unfold facts_ok, c_atoms0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U19, U32, U34. change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r.
    unfold V_hw, SB. clear - Hmf0 Hmfb H47 C1 Hmf32 HSF0 HSF1 HSF64.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS Bx_c [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x374)) with (Z_to_bv 64 (BASE + 0x374)).
(* run 1: 0x80ae8 .. the guard 0x80afc *)
paj_run_tok RUN HS HJ SHOK Bspan; [c_awr U9 mf sp0; clear - Hmfb HSTK' Has; lia |].
rename ms into ms1. rename HFr into HFr1. clear HF HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
2: { exfalso. rewrite branch_eq_U in Hc.
     rewrite (U_atom E 18 0) in Hc by (first [rewrite (EE 18%nat 18%bv eq_refl), R18, Hn0; reflexivity | lia]).
     rewrite U_SLit in Hc. discriminate Hc. }
(* run 2: 0x81750 .. 0x81764 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xff0; [c_awr U9 mf sp0; clear - Hmfb HSTK' Has; lia |].
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 24 <= a < mf + 184) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  rewrite (kept_of_frame E _ (w_H W2) (ms_mem ms1) (ms_mem ms) (fun x => mf + 24 <= x < mf + 184) HFr);
  [| c_win U9 | exact Ha | exact Hw].
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms1) (fun x => mf + 24 <= x < mf + 184) HFr1);
  [c_win U9 | exact Ha | exact Hw]. }
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (24%bv : bv 5) Q24.
rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 9%nat 9%bv eq_refl) in Q9. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
rewrite (EE 3%nat 3%bv eq_refl) in Q3. rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25.
assert (W24 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 24) 8 0) by (c_ck HS 0%nat 24 mf U9; [reflexivity | lia | lia]).
assert (W32 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 32) 8 (SF + V_hw)).
{ c_ck HS 0%nat 32 mf U9; [cbn [sv_denot]; rewrite U19, Z.add_0_r; reflexivity | unfold V_hw; clear - HSF0 HSF1 C1; lia | lia]. }
assert (W136 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 136) 8 (SF + V_id + 3)).
{ c_ck HS 0%nat 136 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_id; f_equal; ring | unfold V_id; clear - HSF0 HSF1 C1; lia | lia]. }
assert (W160 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 160) 8 (shadow_addr SF)).
{ c_ck HS 0%nat 160 mf U9; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 23%nat 23%bv eq_refl); exact Hsh
  | unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1; lia | lia]. }
assert (W64 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 64) 8 SF).
{ c_ck HS 0%nat 64 mf U9; [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | clear - HSF0 HSF1 C1; lia | lia]. }
assert (W168 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 168) 8 SHADOW_OFF).
{ c_ck HS 0%nat 168 mf U9; [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; lia | lia]. }
assert (Hmc : m_cur g 0 = 0).
{ unfold m_cur. cbn [SlotModel.rec_c]. unfold SlotModel.nlen. rewrite <- Hlen, Hn0. reflexivity. }
pmkst HS. apply SRr_ret. split; [exact Hnr|].
refine (c_exit_of g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HC HJ Hfrs MLE MOK Hbl Hid Hmid Hsh
  Sh0 Sh8 Hz Hnr Q2 Q9 Q8 Q3 Q4 Q23 _ _ KEEP W64 W168 W24 W32 W136 W160).
- rewrite Q25, Hmc, Z.add_0_r. reflexivity.
- rewrite Q24, Hmc, Hn0. reflexivity.
Qed.

(* ---- n >= 1: the UBSan and ASan checks of input[0], nrec, the guard 0x80b54 and the loop's head ------------ *)
Lemma c_n1 : forall g pos mf W2 c2, c_mid g pos mf W2 c2 -> 0 < e_n g ->
  SRr SEGS W2 c2 (fun W3 c3 => inv_rec g pos mf 0 W3 c3 \/ (m_nrec g = 0%nat /\ inv_exit g pos mf W3 c3)).
Proof.
intros g pos mf W2 c2 Hst Hn.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hbl & Hmid & Hsh & R19 & R18 & R25 & Sh0 & Sh8 & Hz).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & V64 & _ & V168 & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & HPRE & _ & _ & Hinb).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _ & _ & _ & _ & HROS & _).
destruct (c_geo g pos mf ly2 S2 W2 mem2 md2 0 HJ Hfrs Hmfb)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Hmf0 & H47 & Hsp0al & C1).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
(* the input block: a heap block apart from the frame and the image *)
destruct Hinp as [[Hn0 _] | [[_ Hn26] Hine]]; [lia|].
assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (Hp16 & Hp4096 & Hpce & Hpapp & _).
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as Hpimg.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine2 Hin4) as Hdf.
unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as Hfimg. rewrite EFa, HFB in Hfimg.
assert (Hrq : req_size (e_n g) = e_n g) by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
rewrite Hrq in Hpce, Hpapp, Hpimg, Hdf.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
(* its first shadow cell: 0 when n >= 8, n when n < 8 *)
destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as ((_ & _ & Hbs) & _).
rewrite Hrq in Hbs. specialize (Hbs 0 ltac:(split; [lia | apply Z.div_str_pos; lia])). rewrite Z.add_0_r in Hbs.
set (sv := if 0 <? e_n g / 8 then 0 else e_n g mod 8) in Hbs.
(* input[0] and the model *)
assert (Hmc : m_cur g 0 = 1).
{ unfold m_cur. cbn [SlotModel.rec_c]. unfold SlotModel.nlen. rewrite <- Hlen. lia. }
pose proof Hinb as Hinb0. pose proof Hlen as Hlen0.
destruct (e_pl g) as [|x pl'] eqn:Epl; [cbn [length] in Hlen0; lia|].
set (b0 := bv_unsigned x).
assert (Vb0 : val_mem SEGS (rd W2 mem2) (e_p g + 0) 1 b0 /\ 0 <= b0 < 256).
{ unfold bytes_at8, garr8 in Hinb0. exact (Hinb0 0%nat ltac:(cbn; lia)). }
destruct Vb0 as [Vb0 Hb0r].
assert (Hnrec : SlotModel.nrec (e_pl g) = b0 mod 65) by (unfold SlotModel.nrec, SlotModel.inb; rewrite Epl; reflexivity).
assert (Hmnr : m_nrec g = Z.to_nat (b0 mod 65)) by (unfold m_nrec, SlotModel.nrecn; rewrite Hnrec; reflexivity).
(* object 5 *)
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2)).
{ apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  apply HRO. exact HROS. }
destruct (HIMG W2 mem2 HROc) as (V5 & _).
pose proof (pa_obj_img 5 ltac:(lia)) as Ho5.
pose proof (pa_val_range (A_OBJ 5)) as Ho5r.
(* the environment *)
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *. set (p := e_p g) in *. set (n := e_n g) in *.
remember (Eimg (Ereg regs2 (c_extra b0 SF p sv))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SB + p / 8))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 sv)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E5 : ew E (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (ER : regs_ok E sr_atoms regs2) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE.
assert (Hsvr : 0 <= sv < 8).
{ unfold sv. destruct (0 <? n / 8); [lia | apply Z.mod_pos_bound; lia]. }
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = SF + V_hw).
{ rewrite (EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small. unfold V_hw. clear - HSF0 HSF1 C1. lia. }
assert (U18 : bv_unsigned (ew E 18) = n).
{ rewrite (EE 18%nat 18%bv eq_refl), R18. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E 25) = p).
{ rewrite (EE 25%nat 25%bv eq_refl), R25. apply unsigned_lit_small. clear - Hp4096 Hpce C1 Hn. lia. }
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = SF) by (rewrite E34; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (U35 : bv_unsigned (ew E 35) = SB + p / 8)
  by (rewrite E35; apply unsigned_lit_small; unfold SB; clear - Hp4096 Hpce C1 Hn; lia).
assert (U36 : bv_unsigned (ew E 36) = sv) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U5 : bv_unsigned (ew E (A_OBJ 5)) = VAL (A_OBJ 5)) by (rewrite E5; apply unsigned_lit_small; exact Ho5r).
(* the symbolic state at 0x80ae8, in its two forms *)
assert (HSgen : forall rsh lo hi,
  (rsh = c_shA /\ lo = 0 /\ hi = 0 /\ 8 <= n) \/ (rsh = c_shB /\ lo = 1 /\ hi = 7 /\ n < 8) ->
  st_ok_pi SEGS VAL E (ss_c1 rsh lo hi)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x374)) mem2 (seg_rom SEGS)))).
{ intros rsh lo hi Hcase.
  assert (Hsv : (rsh = c_shA /\ lo = 0 /\ hi = 0 /\ sv = 0) \/ (rsh = c_shB /\ lo = 1 /\ hi = 7 /\ sv = n)).
  { unfold sv. destruct Hcase as [(-> & -> & -> & Hb) | (-> & -> & -> & Hb)]; [left | right]; repeat split.
    - replace (0 <? n / 8) with true by (symmetry; apply Z.ltb_lt; apply Z.div_str_pos; lia). reflexivity.
    - replace (0 <? n / 8) with false by (symmetry; apply Z.ltb_ge; rewrite Z.div_small by lia; lia).
      apply Z.mod_small. lia. }
  clear Hcase.
  destruct Hsv as [(-> & -> & -> & Hsv0) | (-> & -> & -> & Hsv0)].
  all: rewrite restrict_mkst_fx; unfold ss_c1; apply pa_entry_st_ok_full; [exact ER | vm_compute; reflexivity | | |].
  all: cycle 1.
  (* the five regions are apart *)
  1, 4: apply pairwise_disjoint_of_extents;
    unfold c_mf, c_hw, c_shA, c_shB, c_in, c_o5, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U9, U19, U35, U25, U5;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    unfold V_hw, SB; clear - Hmf0 HSF0 HSF1 HSFapp Hfimg Hdf Hp4096 Hpce Hpapp Hpimg Ho5 C1 Hn;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  (* the atom facts and the alias of the shadow cell *)
  1, 3: unfold facts_ok, c_atoms1, c_atoms0, c_alias; cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok];
    split; [|split; [exact I|]];
    [ unfold afact_ok, PTR; cbn [af_lo af_hi af_al2];
      rewrite U2, U9, U19, U32, U34, U18, U25, U33, U36, U5;
      change (2 ^ 5) with 32; change (2 ^ 4) with 16; rewrite !Z.pow_0_r;
      unfold V_hw, SB; clear - Hmf0 Hmfb H47 C1 Hmf32 HSF0 HSF1 HSF64 Hn Hn26 Hp16 Hp4096 Hpce Hb0r Hsv0 Hsvr Ho5;
      repeat match goal with |- _ /\ _ => split end; try exact I; lia
    | split; [|exact I]; apply U_inj; rewrite !U_SAlu; cbn [zalu_raw]; rewrite U_SLit;
      rewrite !U_SOff, U25, U32, U35, !Z.add_0_r;
      change (Z.land (zcanon 3) 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      unfold zcanon, M64, SB; clear - Hp4096 Hpce C1 Hn; rewrite !Z.mod_small by lia; lia ].
  (* the regions *)
  all: constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  all: unfold c_mf, c_hw, c_shA, c_shB, c_in, c_o5, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  all: rewrite ?U9, ?U19, ?U35, ?U25, ?U5.
  (* the machine frame *)
  1, 6: split; [clear - Hmf0 C1; lia|]; split; [clear - Hmfb H47; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply Hpres; clear - Ho Hmfb HSTK' Has; lia
    | constructor; [|constructor; [|constructor; [|constructor]]];
      [ apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 34 0) SF);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - HSF0 HSF1 C1; lia | lia | exact V64]
      | apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; lia | lia | exact V168]
      | apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 34 352) (SF + V_id));
        [cbn [sv_denot]; rewrite U34; reflexivity | unfold V_id; clear - HSF0 HSF1 C1; lia | lia | exact Hmid] ] ].
  (* hw.have *)
  1, 5: split; [unfold V_hw; clear - HSF0; lia|]; split; [unfold V_hw; clear - HSF1 C1; lia|];
    split; [intros o Ho; lia|]; constructor; [|constructor];
    apply (chunk_ok_val SEGS E _ (SF + V_hw) 0 4 (SLit 0) 0); [reflexivity | lia | lia |];
    rewrite Z.add_0_r; apply c_vm0; intros i Hi; apply Hz; unfold N_hw; cbn in Hi; lia.
  (* the shadow cell of input[0] *)
  1, 4: split; [unfold SB; clear - Hp4096; lia|]; split; [unfold SB; clear - Hp4096 Hpce C1 Hn; lia|];
    split; [intros o Ho; lia|]; constructor; [|constructor];
    apply (chunk_ok_val SEGS E _ (SB + p / 8) 0 1 _ sv);
    [ cbn [sv_denot]; rewrite ?U36, ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?Hsv0; reflexivity | lia | lia |];
    rewrite Z.add_0_r; apply c_vm1; unfold shadow_of_addr in Hbs; exact Hbs.
  (* input[0] *)
  1, 3: split; [clear - Hp4096; lia|]; split; [clear - Hpce C1 Hn; lia|];
    split; [intros o Ho; lia|]; constructor; [|constructor];
    apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) b0);
    [ cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | lia | lia | exact Vb0 ].
  (* object 5 *)
  all: split; [lia|]; split; [lia|]; split; [intros o Ho; lia|]; constructor; [|constructor];
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 5)) 0 8 (SLit 0x03f03f03f03f03f1) 0x03f03f03f03f03f1);
    [ reflexivity | lia | lia | rewrite Z.add_0_r; exact V5 ]. }
(* The run, in the two forms of the state (n < 8: c_shB; n >= 8: c_shA), as one tactic per goal:
   0x80ae8 .. the guard 0x80b54 (the UBSan check 0x80b0c and the shadow check 0x80b20 / 0x82624 are decided by the
   atom facts); then nrec = 0: 0x81760 .. the exit, or nrec > 0: the hoisted slots and the loop's head. *)
destruct (Z_lt_le_dec n 8) as [Hsm | Hbg];
[ pose proof (HSgen c_shB 1 7 (or_intror (conj eq_refl (conj eq_refl (conj eq_refl Hsm))))) as HS
| pose proof (HSgen c_shA 0 0 (or_introl (conj eq_refl (conj eq_refl (conj eq_refl Hbg))))) as HS ];
clear HSgen;
assert (SHOK : sh_ok SEGS Bx_c [] E (mrestrict (w_H W2) mem2)) by constructor;
unfold cfg_at; change (w64 (BASE + 0x374)) with (Z_to_bv 64 (BASE + 0x374));
(paj_run_tok RUN HS HJ SHOK Bspan; [c_awr U9 mf sp0; clear - Hmfb HSTK' Has; lia |]);
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into ms1 end;
rename HFr into HFr1; clear HF HG;
psrr_branch_tok RUN BR HS SHOK Bspan;
rewrite branch_eq_U, (c_nrec_U E b0 E33 Hb0r), U_SLit in Hc; change (zcanon 0) with 0 in Hc;
(lazymatch type of Hc with
 | _ = true => paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xff0
 | _ = false => paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x440
 end; [c_awr U9 mf sp0; clear - Hmfb HSTK' Has; lia |]);
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msF end;
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 24 <= a < mf + 184) ->
  aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha Hw;
      rewrite (kept_of_frame E _ (w_H W2) (ms_mem ms1) (ms_mem msF) (fun x => mf + 24 <= x < mf + 184) HFr);
      [ apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms1) (fun x => mf + 24 <= x < mf + 184) HFr1);
        [c_win U9 | exact Ha | exact Hw]
      | c_win U9 | exact Ha | exact Hw ]);
prreg HS (2%bv : bv 5) Q2; prreg HS (9%bv : bv 5) Q9; prreg HS (8%bv : bv 5) Q8; prreg HS (3%bv : bv 5) Q3;
prreg HS (4%bv : bv 5) Q4; prreg HS (23%bv : bv 5) Q23; prreg HS (25%bv : bv 5) Q25; prreg HS (24%bv : bv 5) Q24;
rewrite (EE 2%nat 2%bv eq_refl) in Q2; rewrite (EE 9%nat 9%bv eq_refl) in Q9; rewrite (EE 8%nat 8%bv eq_refl) in Q8;
rewrite (EE 3%nat 3%bv eq_refl) in Q3; rewrite (EE 4%nat 4%bv eq_refl) in Q4; rewrite (EE 23%nat 23%bv eq_refl) in Q23;
rewrite U25 in Q25; rewrite U18 in Q24;
assert (W24 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 24) 8 0) by (c_ck HS 0%nat 24 mf U9; [reflexivity | lia | lia]);
assert (W32 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 32) 8 (SF + V_hw))
  by (c_ck HS 0%nat 32 mf U9; [cbn [sv_denot]; rewrite U19, Z.add_0_r; reflexivity | unfold V_hw; clear - HSF0 HSF1 C1; lia | lia]);
assert (W136 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 136) 8 (SF + V_id + 3))
  by (c_ck HS 0%nat 136 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_id; f_equal; ring | unfold V_id; clear - HSF0 HSF1 C1; lia | lia]);
assert (W160 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 160) 8 (shadow_addr SF))
  by (c_ck HS 0%nat 160 mf U9; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 23%nat 23%bv eq_refl); exact Hsh
      | unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1; lia | lia]);
assert (W64 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 64) 8 SF)
  by (c_ck HS 0%nat 64 mf U9; [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | clear - HSF0 HSF1 C1; lia | lia]);
assert (W168 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 168) 8 SHADOW_OFF)
  by (c_ck HS 0%nat 168 mf U9; [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; lia | lia]);
assert (W96 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 96) 8 (SlotModel.nrec (e_pl g)))
  by (rewrite Hnrec; c_ck HS 0%nat 96 mf U9; [rewrite denot_lit_U, (c_nrec_U E b0 E33 Hb0r); reflexivity | lia | lia]);
pmkst HS; apply SRr_ret;
lazymatch type of Hc with
| _ = true =>
  (* nrec = 0: the exit *)
  right; assert (Hnr0 : m_nrec g = 0%nat) by (rewrite Hmnr; apply Z.eqb_eq in Hc; rewrite Hc; reflexivity);
  (split; [exact Hnr0|]);
  (refine (c_exit_of g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_regs msF) (ms_mem msF) _ HC HJ Hfrs MLE MOK Hbl Hid Hmid Hsh
     Sh0 Sh8 Hz Hnr0 Q2 Q9 Q8 Q3 Q4 Q23 _ _ KEEP W64 W168 W24 W32 W136 W160);
   [ rewrite Q25, Hmc; reflexivity | rewrite Q24, Hmc; unfold w64; f_equal; lia ])
| _ = false =>
  (* nrec > 0: the loop's head, inv_rec 0 *)
  left; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15;
  assert (W48 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 48) 8 (SF + V_v))
    by (c_ck HS 0%nat 48 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_v; reflexivity | unfold V_v; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W72 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 72) 8 (SF + V_ev))
    by (c_ck HS 0%nat 72 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_ev; reflexivity | unfold V_ev; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W80 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 80) 8 (SF + V_again + 28))
    by (c_ck HS 0%nat 80 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_again; f_equal; ring | unfold V_again; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W88 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 88) 8 (SF + V_again + 3))
    by (c_ck HS 0%nat 88 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_again; f_equal; ring | unfold V_again; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W104 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 104) 8 (SF + V_id + 28))
    by (c_ck HS 0%nat 104 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_id; f_equal; ring | unfold V_id; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W144 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 144) 8 (SF + V_s))
    by (c_ck HS 0%nat 144 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_s; reflexivity | unfold V_s; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W152 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 152) 8 (SF + V_before))
    by (c_ck HS 0%nat 152 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_before; reflexivity | unfold V_before; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W176 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 176) 8 (SF + V_again))
    by (c_ck HS 0%nat 176 mf U9; [cbn [sv_denot]; rewrite U34; unfold V_again; reflexivity | unfold V_again; clear - HSF0 HSF1 C1; lia | lia]);
  assert (W56 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 56) 8 (Z.lnot (SF + V_ev)))
    by (apply (c_vm_mod SEGS _ _ 8 (Z.lnot (SF + V_ev) mod 2 ^ 64));
        [change (8 * Z.of_nat 8) with 64; apply Z.mod_mod; lia|];
        c_ck HS 0%nat 56 mf U9;
        [ rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SOff, U34, U_SLit;
          rewrite (zcanon_id (SF + 288)) by (unfold M64; clear - HSF0 HSF1 C1; lia);
          unfold V_ev; apply c_xor_m1; clear - HSF0 HSF1 C1; lia
        | apply Z.mod_pos_bound; lia | lia ]);
  (refine (c_rec0_of g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_regs msF) (ms_mem msF) _ HC HJ Hfrs MLE MOK Hbl Hid Hmid Hsh
     Sh0 Sh8 Hz _ Q2 Q9 Q8 Q3 Q4 Q23 Q14 Q15 _ _ KEEP W64 W168 W24 W96 _ W152 W176);
   [ rewrite Hmnr; apply Z.eqb_neq in Hc; pose proof (Z.mod_pos_bound b0 65 ltac:(lia)); lia
   | rewrite Q25, Hmc; reflexivity
   | rewrite Q24, Hmc; unfold w64; f_equal; lia
   | unfold mf_fixed; change (SFa g pos) with SF;
     split; [exact W32|]; split; [exact W48|]; split; [exact W56|]; split; [exact W72|]; split; [exact W80|];
     split; [exact W88|]; split; [exact W104|]; split; [exact W136|]; split; [exact W144 | exact W160] ])
end.
Qed.

(* ---- the segment ---------------------------------------------------------------------------------------------- *)
Lemma seg_C : seg_C_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf W2 c2 Hst.
eapply SRr_bind; [exact (c_memset g pos mf W2 c2 Hst)|].
intros W3 c3 _ Hmid.
assert (Hn : 0 <= e_n g).
{ destruct Hmid as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & HC & _).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HPRE & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _). rewrite Hlen. lia. }
destruct (Z.eq_dec (e_n g) 0) as [Hn0 | Hn1].
- eapply SRr_mono; [exact (c_n0 g pos mf W3 c3 Hmid Hn0)|].
  intros W4 c4 _ Hx. right. exact Hx.
- exact (c_n1 g pos mf W3 c3 Hmid ltac:(lia)).
Qed.
Check (seg_C : seg_C_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
