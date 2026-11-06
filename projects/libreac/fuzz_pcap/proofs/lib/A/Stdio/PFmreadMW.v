(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the WALK of musl's mread -- the read hook fmemopen
   stores in the FILE and fread calls through f->read -- inside libreac/fuzz_pcap (libreac v1.9.0,
   the memory-checking builds). It proves lib/A/Stdio/PFreadM.v's rmread_contract, text unchanged
   (a Theorem Labs lane's caller-journal form, PFreadM.v as at a working branch 9b4de8c19fc and
   unchanged at ffaa56103b8; PSource.v / PSourceMeta.v as at ffaa56103b8: as_rwa, b + n <= 2^64,
   explicit SK).

   rule 24: at ossv/recipes 568db058c1de (2026-10-28), there was NO DONOR for mread. `proof-index mread` (index v5, built 2026-10-28T21:58:24Z)
   returns rc=0 with four released files, all pcap's OWN plain / ubsan walks in lib/Prog and
   lib/U/Prog (lib/Lib's evt form over rsegs, not the ASan SRr / ajournal form); the four released
   refs hold no cgif-form proof of mread, and cgif_file_fuzzer links no mread at all (it writes a
   file through fopen / fwrite). So this walk is written new, with the plain lib/Prog/mread_c.v
   contract as the arithmetic template (mread_t / mread_rem2 = rread_k / rmread_fill).

   WHAT IS PROVED. rmread_contract_proved, generic in the image: for any segs, B, K, entry pc and
   memcpy-trampoline address tr with
     - mread_code segs pc tr: the 51 non-jal instruction words of mread at pc (MR_CODE, MEASURED),
       and the two `jal` words at pc+0x64 / pc+0xa4 decoded as Jal 1 imm with target tr;
     - aintrin_realizes segs B OCpy tr: the memcpy interceptor's contract at that trampoline;
     - AR_laws segs B, segs_low, wx_segs_nowrap segs, asource_img_laws SK segs B K,
   rmread_contract segs B K pc holds. The two images instantiate it in their own files:
   rmread_contract_asan (PMREAD / TRAMP_MEMCPY) in lib/A/Stdio/PFmreadMWA.v and
   rmread_contract_asan_ubsan (PMREAD_U / TRAMP_MEMCPY_U) in lib/B/Stdio/PFmreadMWB.v; this file
   Requires no image and no image's pc file. The twin's mread has the SAME 51 non-jal words, so it
   needs no second walk, only its own two jal words and its own image facts (its instance file).

   THE WALK (addresses MEASURED on the pinned fuzz_pcap.asan image's unstripped twin
   (sha256 36da3052c383), objdump lines 99225-99278):
     phase 1 (pc .. pc+0x64): the 48-byte frame and the five saved registers, c = f->cookie
       (+152), c->pos, c->len, the saturating subtraction n - p (sub / sltu / addi -1 / and),
       `bgeu s2,s0` at +0x40: when l > n - p it sets F_EOF (ori 16, sw at +0x4c) and cuts the
       count to n - p; both arms reach the first memcpy call with a0 = d, a1 = b + p, a2 = j.
     phase 2 (pc+0x68 .. pc+0xa4): c->pos += j, r = min(n - p - j, bufsiz) (`bltu` at +0x7c),
       rpos = f + 280, rend = f + 280 + r, then the second memcpy of r bytes into the window.
     phase 3 (pc+0xa8 .. pc+0xd0): c->pos += r, a0 = j, the five restores, `addi sp,sp,48`, ret.
   Each phase is a pure msteps lemma (mr_phase1 / mr_phase2 / mr_phase3) over the restricted
   memory; the two calls go through mr_intrin_at (YCbq.v:1953-2004's aj_intrin_at with the
   interceptor's same_but_materialized kept, which the restated post needs for m_fds / m_fs).

   NOT REACHED: mread is musl code, not instrumented, and its only calls are the two memcpy
   trampolines. No __asan_report_* and no CheckFailed entry is stepped: the interceptor's report
   path is inside aintrin_realizes' own contract, which this walk takes as a hypothesis.

   THE STACK: RMREAD_STK = 48 + ESTACK = 4144 (PFreadM.v), mread's own 48-byte frame plus the
   interceptor's ESTACK window; the walk uses the caller's journal window [sp0 - STK, sp0) through
   rread_call and never writes below sp - 48 itself. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP09 YP02 YP03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM.
Import ListNotations.
(* lia guard: the Zify flag leak (YE2e.v:29 / AE2e.v:30, ~120 files) sets the euclidean-division flag to false globally *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. mread's code: 53 words from the entry, MEASURED on fuzz_pcap.asan   *)
(*    v1.9.0 (objdump lines 99226-99278). The two `jal` words (+0x64,      *)
(*    +0xa4) are NOT listed: their offset to the memcpy trampoline is       *)
(*    image-dependent, so mread_code states them decoded.                   *)
(* ---------------------------------------------------------------------- *)
Definition MR_CODE : list (Z * Z) := [
(0x0, 0xfd010113); (0x4, 0x02113423); (0x8, 0x02813023); (0xc, 0x00913c23);
(0x10, 0x01213823); (0x14, 0x01313423); (0x18, 0x00060413); (0x1c, 0x00050493);
(0x20, 0x09853983); (0x24, 0x0009b603); (0x28, 0x0089b503); (0x2c, 0x40c506b3);
(0x30, 0x00d53533); (0x34, 0xfff50513); (0x38, 0x00d57933); (0x3c, 0x00058513);
(0x40, 0x00897c63); (0x44, 0x0004a583); (0x48, 0x0105e593); (0x4c, 0x00b4a023);
(0x50, 0x0009b603); (0x54, 0x00090413); (0x58, 0x0189b583); (0x5c, 0x00c585b3);
(0x60, 0x00040613);
(0x68, 0x0009b503); (0x6c, 0x00850533); (0x70, 0x00a9b023); (0x74, 0x0604b503);
(0x78, 0x40890933); (0x7c, 0x00a96463); (0x80, 0x00050913); (0x84, 0x0584b503);
(0x88, 0x012505b3); (0x8c, 0x00a4b423); (0x90, 0x00b4b823); (0x94, 0x0009b583);
(0x98, 0x0189b603); (0x9c, 0x00b605b3); (0xa0, 0x00090613);
(0xa8, 0x0009b503); (0xac, 0x01250533); (0xb0, 0x00a9b023); (0xb4, 0x00040513);
(0xb8, 0x02813083); (0xbc, 0x02013403); (0xc0, 0x01813483); (0xc4, 0x01013903);
(0xc8, 0x00813983); (0xcc, 0x03010113); (0xd0, 0x00008067)].

Section code.
Context {fx : YK11.FPState}.
Definition mread_code (segs : list Segment) (pc tr : Z) : Prop :=
  0 <= pc /\ pc mod 4 = 0 /\ pc + 0xd4 < 2 ^ 63 /\ 0 <= tr < 2 ^ 63 /\
  (forall off w, In (off, w) MR_CODE -> fetch_word segs (Z_to_bv 64 (pc + off)) = Some (Z_to_bv 32 w)) /\
  (forall off, off = 0x64 \/ off = 0xa4 -> exists (w : bv 32) (imm : bv 21),
     fetch_word segs (Z_to_bv 64 (pc + off)) = Some w /\ is_ecall w = false /\
     decode_any w = Some (Jal 1 imm, 4%Z) /\ btgt (Z_to_bv 64 (pc + off)) (bv_signed imm) = Z_to_bv 64 tr).
End code.

(* The decoded instructions (checked by computation). *)
Lemma D00 : decode_any (Z_to_bv 32 0xfd010113) = Some (OpImm ALU_ADD 2 2 4048, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D04 : decode_any (Z_to_bv 32 0x02113423) = Some (Store SZ8 2 1 40, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D08 : decode_any (Z_to_bv 32 0x02813023) = Some (Store SZ8 2 8 32, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D0c : decode_any (Z_to_bv 32 0x00913c23) = Some (Store SZ8 2 9 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D10 : decode_any (Z_to_bv 32 0x01213823) = Some (Store SZ8 2 18 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D14 : decode_any (Z_to_bv 32 0x01313423) = Some (Store SZ8 2 19 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D18 : decode_any (Z_to_bv 32 0x00060413) = Some (OpImm ALU_ADD 8 12 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D1c : decode_any (Z_to_bv 32 0x00050493) = Some (OpImm ALU_ADD 9 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D20 : decode_any (Z_to_bv 32 0x09853983) = Some (Load SZ8 true 19 10 152, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D24 : decode_any (Z_to_bv 32 0x0009b603) = Some (Load SZ8 true 12 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D28 : decode_any (Z_to_bv 32 0x0089b503) = Some (Load SZ8 true 10 19 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D2c : decode_any (Z_to_bv 32 0x40c506b3) = Some (Op ALU_SUB 13 10 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D30 : decode_any (Z_to_bv 32 0x00d53533) = Some (Op ALU_SLTU 10 10 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D34 : decode_any (Z_to_bv 32 0xfff50513) = Some (OpImm ALU_ADD 10 10 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D38 : decode_any (Z_to_bv 32 0x00d57933) = Some (Op ALU_AND 18 10 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D3c : decode_any (Z_to_bv 32 0x00058513) = Some (OpImm ALU_ADD 10 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D40 : decode_any (Z_to_bv 32 0x00897c63) = Some (Branch BC_GEU 18 8 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D44 : decode_any (Z_to_bv 32 0x0004a583) = Some (Load SZ4 true 11 9 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D48 : decode_any (Z_to_bv 32 0x0105e593) = Some (OpImm ALU_OR 11 11 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D4c : decode_any (Z_to_bv 32 0x00b4a023) = Some (Store SZ4 9 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D50 : decode_any (Z_to_bv 32 0x0009b603) = Some (Load SZ8 true 12 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D54 : decode_any (Z_to_bv 32 0x00090413) = Some (OpImm ALU_ADD 8 18 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D58 : decode_any (Z_to_bv 32 0x0189b583) = Some (Load SZ8 true 11 19 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D5c : decode_any (Z_to_bv 32 0x00c585b3) = Some (Op ALU_ADD 11 11 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D60 : decode_any (Z_to_bv 32 0x00040613) = Some (OpImm ALU_ADD 12 8 0, 4%Z). Proof. vm_refl_bv. Qed.

Lemma D68 : decode_any (Z_to_bv 32 0x0009b503) = Some (Load SZ8 true 10 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D6c : decode_any (Z_to_bv 32 0x00850533) = Some (Op ALU_ADD 10 10 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D70 : decode_any (Z_to_bv 32 0x00a9b023) = Some (Store SZ8 19 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D74 : decode_any (Z_to_bv 32 0x0604b503) = Some (Load SZ8 true 10 9 96, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D78 : decode_any (Z_to_bv 32 0x40890933) = Some (Op ALU_SUB 18 18 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D7c : decode_any (Z_to_bv 32 0x00a96463) = Some (Branch BC_LTU 18 10 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D80 : decode_any (Z_to_bv 32 0x00050913) = Some (OpImm ALU_ADD 18 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D84 : decode_any (Z_to_bv 32 0x0584b503) = Some (Load SZ8 true 10 9 88, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D88 : decode_any (Z_to_bv 32 0x012505b3) = Some (Op ALU_ADD 11 10 18, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D8c : decode_any (Z_to_bv 32 0x00a4b423) = Some (Store SZ8 9 10 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D90 : decode_any (Z_to_bv 32 0x00b4b823) = Some (Store SZ8 9 11 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D94 : decode_any (Z_to_bv 32 0x0009b583) = Some (Load SZ8 true 11 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D98 : decode_any (Z_to_bv 32 0x0189b603) = Some (Load SZ8 true 12 19 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D9c : decode_any (Z_to_bv 32 0x00b605b3) = Some (Op ALU_ADD 11 12 11, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Da0 : decode_any (Z_to_bv 32 0x00090613) = Some (OpImm ALU_ADD 12 18 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Da8 : decode_any (Z_to_bv 32 0x0009b503) = Some (Load SZ8 true 10 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dac : decode_any (Z_to_bv 32 0x01250533) = Some (Op ALU_ADD 10 10 18, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Db0 : decode_any (Z_to_bv 32 0x00a9b023) = Some (Store SZ8 19 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Db4 : decode_any (Z_to_bv 32 0x00040513) = Some (OpImm ALU_ADD 10 8 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Db8 : decode_any (Z_to_bv 32 0x02813083) = Some (Load SZ8 true 1 2 40, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dbc : decode_any (Z_to_bv 32 0x02013403) = Some (Load SZ8 true 8 2 32, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dc0 : decode_any (Z_to_bv 32 0x01813483) = Some (Load SZ8 true 9 2 24, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dc4 : decode_any (Z_to_bv 32 0x01013903) = Some (Load SZ8 true 18 2 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dc8 : decode_any (Z_to_bv 32 0x00813983) = Some (Load SZ8 true 19 2 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dcc : decode_any (Z_to_bv 32 0x03010113) = Some (OpImm ALU_ADD 2 2 48, 4%Z). Proof. vm_refl_bv. Qed.
Lemma Dd0 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.

Ltac INL := cbn [In]; repeat (first [left; reflexivity | right]).

Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.

Lemma mr_vaddi : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
intros z i. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma mr_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply unsigned_lit_small. exact Hz. Qed.

Lemma mr_mx : forall regs z m rom regs' m' ms',
  RiscvSemantics.step segs (mkst regs (Z_to_bv 64 z) m rom) = MachineOk (mkst regs' (v_addi (Z_to_bv 64 z) 4) m' rom) ->
  msteps segs (mkst regs' (Z_to_bv 64 (z + 4)) m' rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof. intros regs z m rom regs' m' ms' Hs Hm. eapply mst_step; [reflexivity | exact Hs |]. rewrite mr_vaddi. exact Hm. Qed.

Lemma mr_mxt : forall regs z m rom regs' m' ms' d,
  RiscvSemantics.step segs (mkst regs (Z_to_bv 64 z) m rom) = MachineOk (mkst regs' (btgt (Z_to_bv 64 z) d) m' rom) ->
  msteps segs (mkst regs' (Z_to_bv 64 (z + d)) m' rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof. intros regs z m rom regs' m' ms' d Hs Hm. eapply mst_step; [reflexivity | exact Hs |]. unfold btgt. rewrite mr_vaddi. exact Hm. Qed.

Lemma mr_nth_le : forall n z i, (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
induction n as [|n IH]; intros z i Hi; [lia|].
destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
- rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma mr_rdn_val : forall m a n v, 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  val_mem segs m a n v -> rdn segs m (Z_to_bv 64 a) n = Some (Z_to_le_bytes n v).
Proof.
intros m a n v Hv Hval. apply rdn_mbytes. split; [apply length_Z_to_le_bytes|].
intros i Hi. rewrite (Hval i Hi), mr_nth_le by exact Hi. f_equal. apply le_byte_small; [exact Hv | exact Hi].
Qed.

Lemma mr_wb_out : forall bs m a (x : word), 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x) -> wbytes m (Z_to_bv 64 a) bs x = m x.
Proof.
intros bs m a x Ha Hn [Hx|Hx].
- apply wbytes_below; rewrite mr_lit by lia; lia.
- apply wbytes_above. rewrite mr_lit by lia. lia.
Qed.

Lemma mr_wb_hit : forall bs m a j, 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m (Z_to_bv 64 a) bs (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros m a j Ha Hn Hj; cbn [length] in Hn, Hj; [lia|].
cbn [wbytes]. rewrite Z_to_bv64_add1.
destruct j as [|j].
- rewrite mr_wb_out; [| lia | lia | left; rewrite mr_lit by lia; lia].
  rewrite Z.add_0_r, bv_eqb_refl. reflexivity.
- replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia.
  rewrite IH by lia. reflexivity.
Qed.

Lemma mr_wb_some : forall bs m a x b, m x = Some b -> exists b', wbytes m a bs x = Some b'.
Proof.
induction bs as [|c bs IH]; intros m a x b Hx; [exists b; exact Hx|].
cbn [wbytes]. apply (IH _ _ x (if bv_eqb x a then c else b)).
destruct (bv_eqb x a); [reflexivity | exact Hx].
Qed.

Lemma mr_val_hit : forall m a n (v : Z), 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  val_mem segs (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes n v)) a n v.
Proof.
intros m a n v Ha Hn Hv k Hk. unfold mbyte.
rewrite mr_wb_hit by (rewrite ?length_Z_to_le_bytes; lia).
f_equal. rewrite le_byte_small by assumption.
pose proof (mr_nth_le n v k Hk) as E. apply nth_error_nth with (d := Z_to_bv 8 0) in E. exact E.
Qed.

Definition present (m : word -> option byte) (a : Z) : Prop := exists b, m (Z_to_bv 64 a) = Some b.

Lemma mr_present_wb : forall bs m a x, present m x -> present (wbytes m a bs) x.
Proof. intros bs m a x [b Hb]. destruct (mr_wb_some bs m a _ b Hb) as [b' Hb']. exists b'. exact Hb'. Qed.

Lemma mr_store_ok : forall m a n, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
intros m a n Ha Hn Hp. apply store_ok_of_all; [rewrite mr_lit by lia; lia|].
intros x Hx. rewrite mr_lit in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb].
replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia. rewrite Z_to_bv_bv_unsigned in Hb.
unfold wview. rewrite Hb. discriminate.
Qed.

Lemma mr_val_wbz : forall m a k x b n v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= b -> b + Z.of_nat n <= 2 ^ 64 ->
  (b + Z.of_nat n <= a \/ a + Z.of_nat k <= b) ->
  val_mem segs m b n v -> val_mem segs (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes k x)) b n v.
Proof.
intros m a k x b n v Ha Hn Hb Hbn Hd Hv j Hj. specialize (Hv j Hj). unfold mbyte in *.
rewrite mr_wb_out; [exact Hv | lia | rewrite length_Z_to_le_bytes; lia |].
rewrite length_Z_to_le_bytes, mr_lit by lia. lia.
Qed.

Lemma mr_ld8 : forall m a v, 0 <= v < 2 ^ 64 -> val_mem segs m a 8 v ->
  rdn segs m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 v) /\ bytes_le_to_Z (Z_to_le_bytes 8 v) = bv_unsigned (Z_to_bv 64 v).
Proof.
intros m a v Hv Hm. split; [apply mr_rdn_val; [exact Hv | exact Hm]|].
rewrite bytes_le_Z_to_le by lia. rewrite mr_lit by exact Hv. apply Z.mod_small. exact Hv.
Qed.

Lemma mr_ld4 : forall m a v, 0 <= v < 2 ^ 32 -> val_mem segs m a 4 v ->
  rdn segs m (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 v) /\ bytes_le_to_Z (Z_to_le_bytes 4 v) = bv_unsigned (Z_to_bv 64 v).
Proof.
intros m a v Hv Hm. split; [apply mr_rdn_val; [exact Hv | exact Hm]|].
rewrite bytes_le_Z_to_le by lia. rewrite mr_lit by lia. apply Z.mod_small. exact Hv.
Qed.

Lemma mr_and_m1 : forall x, 0 <= x < 2 ^ 64 -> v_and (Z_to_bv 64 (-1)) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
intros x Hx. unfold v_and. rewrite (mr_lit x) by exact Hx. f_equal.
change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
apply Z.mod_small. exact Hx.
Qed.
End h.

Ltac rg := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].
Ltac mr_zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac mr_simm := repeat match goal with
  | |- context [bv_signed ?b] => check_closed_term b; let v := eval vm_compute in (bv_signed b) in change (bv_signed b) with v
  end.
Ltac mr_vwb V := repeat (eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]); exact V.
Ltac mr_prs PS := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; repeat apply mr_present_wb; apply PS; lia.
Ltac mr_addr := rg; mr_simm; repeat match goal with H : getr _ _ = _ |- _ => rewrite H end; rewrite ?mr_vaddi; f_equal; lia.


(* ---------------------------------------------------------------------- *)
(* 2. One step per instruction kind, at a code offset of mread.            *)
(* ---------------------------------------------------------------------- *)
Section x. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variables pc tr : Z.
Hypothesis CODE : mread_code segs pc tr.

Lemma mr_F : forall z off w, z = pc + off -> In (off, w) MR_CODE -> fetch_word segs (Z_to_bv 64 z) = Some (Z_to_bv 32 w).
Proof. intros z off w -> Hin. destruct CODE as (_ & _ & _ & _ & HC & _). exact (HC off w Hin). Qed.

Lemma mx_addi : forall regs z m rom off w rd rs imm v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  msteps segs (mkst (regupd regs rd v) (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rd rs imm v ms' Hz Hin He Hd Hrd Hv Hm.
eapply (mr_mx segs); [| exact Hm].
exact (step_addi_at segs regs _ m rom _ rd rs imm v (mr_F z off w Hz Hin) He Hd Hrd Hv).
Qed.

Lemma mx_ori : forall regs z m rom off w rd rs imm v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_OR rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  v_ori (getr regs rs) (bv_signed imm) = v ->
  msteps segs (mkst (regupd regs rd v) (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rd rs imm v ms' Hz Hin He Hd Hrd Hv Hm.
eapply (mr_mx segs); [| exact Hm].
rewrite (step_ori segs regs _ m rom _ rd rs imm (mr_F z off w Hz Hin) He Hd), Hrd, Hv. reflexivity.
Qed.

Lemma mx_op : forall regs z m rom off w op rd rs1 rs2 v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Op op rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  alu64 op (getr regs rs1) (getr regs rs2) = v ->
  msteps segs (mkst (regupd regs rd v) (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w op rd rs1 rs2 v ms' Hz Hin He Hd Hrd Hv Hm.
eapply (mr_mx segs); [| exact Hm].
rewrite (step_op_gen segs regs _ m rom _ op rd rs1 rs2 (mr_F z off w Hz Hin) He Hd), Hrd, Hv. reflexivity.
Qed.

Lemma mx_ld : forall regs z m rom off w rd rs imm a v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= v < 2 ^ 64 -> val_mem segs m a 8 v ->
  msteps segs (mkst (regupd regs rd (Z_to_bv 64 v)) (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rd rs imm a v ms' Hz Hin He Hd Hrd Ha Hv Hval Hm.
eapply (mr_mx segs); [| exact Hm].
destruct (mr_ld8 segs m a v Hv Hval) as [R Bq].
rewrite (step_ld segs regs _ m rom _ rd rs imm (Z_to_le_bytes 8 v) (Z_to_bv 64 v) (mr_F z off w Hz Hin) He Hd
  ltac:(rewrite Ha; exact R) Bq), Hrd. reflexivity.
Qed.

Lemma mx_lw : forall regs z m rom off w rd rs imm a v v' ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= v < 2 ^ 32 -> val_mem segs m a 4 v ->
  v_lw (Z_to_bv 64 v) = v' ->
  msteps segs (mkst (regupd regs rd v') (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rd rs imm a v v' ms' Hz Hin He Hd Hrd Ha Hv Hval Hv' Hm.
eapply (mr_mx segs); [| exact Hm].
destruct (mr_ld4 segs m a v Hv Hval) as [R Bq].
rewrite (step_lw segs regs _ m rom _ rd rs imm (Z_to_le_bytes 4 v) (Z_to_bv 64 v) (mr_F z off w Hz Hin) He Hd
  ltac:(rewrite Ha; exact R) Bq), Hrd, Hv'. reflexivity.
Qed.

Lemma mx_sd : forall regs z m rom off w rs1 rs2 imm a v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a -> bv_unsigned (getr regs rs2) = v ->
  0 <= a -> a + 8 < 2 ^ 64 -> (forall i, 0 <= i < 8 -> present m (a + i)) ->
  msteps segs (mkst regs (Z_to_bv 64 (z + 4)) (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 8 v)) rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm a v ms' Hz Hin He Hd Ha Hv Ha0 Ha8 Hp Hm.
eapply (mr_mx segs); [| exact Hm].
rewrite (step_sd_at segs regs _ m rom _ rs1 rs2 imm (Z_to_bv 64 a) (getr regs rs2) (mr_F z off w Hz Hin) He Hd Ha eq_refl
  (mr_store_ok segs m a 8 Ha0 Ha8 Hp)).
unfold word_to_le_bytes. rewrite Hv. reflexivity.
Qed.

Lemma mx_sw : forall regs z m rom off w rs1 rs2 imm a v ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a -> bv_unsigned (getr regs rs2) = v ->
  0 <= a -> a + 4 < 2 ^ 64 -> (forall i, 0 <= i < 4 -> present m (a + i)) ->
  msteps segs (mkst regs (Z_to_bv 64 (z + 4)) (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 4 v)) rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm a v ms' Hz Hin He Hd Ha Hv Ha0 Ha8 Hp Hm.
eapply (mr_mx segs); [| exact Hm].
rewrite (step_sw_at segs regs _ m rom _ rs1 rs2 imm (Z_to_bv 64 a) (getr regs rs2) (mr_F z off w Hz Hin) He Hd Ha eq_refl
  (mr_store_ok segs m a 4 Ha0 Ha8 Hp)).
unfold word_to_le_bytes. rewrite Hv. reflexivity.
Qed.

Lemma mx_bgeu_tk : forall regs z m rom off w rs1 rs2 imm d ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false -> bv_signed imm = d ->
  msteps segs (mkst regs (Z_to_bv 64 (z + d)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm d ms' Hz Hin He Hd Hc Hi Hm. subst d.
eapply (mr_mxt segs); [| exact Hm].
exact (step_bgeu_tk segs regs _ m rom _ rs1 rs2 imm (mr_F z off w Hz Hin) He Hd Hc).
Qed.

Lemma mx_bgeu_ft : forall regs z m rom off w rs1 rs2 imm ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  msteps segs (mkst regs (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm ms' Hz Hin He Hd Hc Hm.
eapply (mr_mx segs); [| exact Hm].
exact (step_bgeu_ft segs regs _ m rom _ rs1 rs2 imm (mr_F z off w Hz Hin) He Hd Hc).
Qed.

Lemma mx_bltu_tk : forall regs z m rom off w rs1 rs2 imm d ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true -> bv_signed imm = d ->
  msteps segs (mkst regs (Z_to_bv 64 (z + d)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm d ms' Hz Hin He Hd Hc Hi Hm. subst d.
eapply (mr_mxt segs); [| exact Hm].
exact (step_bltu_tk segs regs _ m rom _ rs1 rs2 imm (mr_F z off w Hz Hin) He Hd Hc).
Qed.

Lemma mx_bltu_ft : forall regs z m rom off w rs1 rs2 imm ms',
  z = pc + off -> In (off, w) MR_CODE -> is_ecall (Z_to_bv 32 w) = false ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  msteps segs (mkst regs (Z_to_bv 64 (z + 4)) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom off w rs1 rs2 imm ms' Hz Hin He Hd Hc Hm.
eapply (mr_mx segs); [| exact Hm].
exact (step_bltu_ft segs regs _ m rom _ rs1 rs2 imm (mr_F z off w Hz Hin) He Hd Hc).
Qed.

Lemma mx_jal : forall regs z m rom ms', (z = pc + 0x64 \/ z = pc + 0xa4) ->
  msteps segs (mkst (regupd regs 1 (Z_to_bv 64 (z + 4))) (Z_to_bv 64 tr) m rom) ms' ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) ms'.
Proof.
intros regs z m rom ms' Hz Hm.
destruct CODE as (_ & _ & _ & _ & _ & HJ).
assert (Ho : exists off, (off = 0x64 \/ off = 0xa4) /\ z = pc + off) by (destruct Hz as [Hz|Hz]; eexists; split; [left; reflexivity | exact Hz | right; reflexivity | exact Hz]).
destruct Ho as (off & Hoff & ->).
destruct (HJ off Hoff) as (w & imm & F & E & D & T).
eapply mst_step; [reflexivity | exact (step_jal_link segs regs _ m rom w 1 imm F E D) |].
change (bv_eqb (1 : bv 5) 0) with false. cbv iota. rewrite T, mr_vaddi. exact Hm.
Qed.
Lemma mx_ret : forall regs z m rom ra, z = pc + 0xd0 -> getr regs 1 = ra -> YK0s.ret_ok ra ->
  msteps segs (mkst regs (Z_to_bv 64 z) m rom) (mkst regs ra m rom).
Proof.
intros regs z m rom ra Hz Hra Hret.
eapply mst_step; [reflexivity | exact (step_jalr_x0 segs regs _ m rom _ 1 0 ra (mr_F z 0xd0 _ Hz ltac:(INL)) eq_refl Dd0 Hra) |].
mr_simm. unfold YK0s.ret_ok in Hret. rewrite Hret. apply mst_refl.
Qed.
End x.

(* ---------------------------------------------------------------------- *)
(* 3. Phase 1: entry -> the first memcpy call (+0x64 jal), both branches.  *)
(* ---------------------------------------------------------------------- *)
Section p. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variables pc tr : Z.
Hypothesis CODE : mread_code segs pc tr.

Definition p1_mem (m : word -> option byte) (regs : bvmap 5 word) (sp f : Z) (eof : bool) : word -> option byte :=
  let m5 := wbytes (wbytes (wbytes (wbytes (wbytes m
               (Z_to_bv 64 (sp - 8)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 1))))
               (Z_to_bv 64 (sp - 16)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 8))))
               (Z_to_bv 64 (sp - 24)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 9))))
               (Z_to_bv 64 (sp - 32)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 18))))
               (Z_to_bv 64 (sp - 40)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 19))) in
  if eof then wbytes m5 (Z_to_bv 64 f) (Z_to_le_bytes 4 24) else m5.

Lemma mr_phase1 : forall regs m rom (f d l b p n sp : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 d ->
  getr regs 12 = Z_to_bv 64 l ->
  4096 <= sp <= 2 ^ 47 -> 0 < f -> f + SRC_FILE_BLOCK <= sp - 48 -> 0 <= d < 2 ^ 63 ->
  1 <= l <= 2 ^ 26 -> 0 <= p <= n -> n < 2 ^ 63 -> 0 <= b -> b + n < 2 ^ 63 ->
  (forall a, sp - 48 <= a < sp -> present m a) ->
  (forall a, f <= a < f + 4 -> present m a) ->
  val_mem segs m (f + 152) 8 (f + 232) -> val_mem segs m (f + 232) 8 p ->
  val_mem segs m (f + 240) 8 n -> val_mem segs m (f + 256) 8 b ->
  val_mem segs m f 4 8 ->
  exists regs1,
    msteps segs (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs1 (Z_to_bv 64 tr) (p1_mem m regs sp f (l >? n - p)) rom) /\
    getr regs1 1 = Z_to_bv 64 (pc + 0x68) /\ getr regs1 2 = Z_to_bv 64 (sp - 48) /\
    getr regs1 8 = Z_to_bv 64 (rread_k l n p) /\ getr regs1 9 = Z_to_bv 64 f /\
    getr regs1 10 = Z_to_bv 64 d /\ getr regs1 11 = Z_to_bv 64 (b + p) /\
    getr regs1 12 = Z_to_bv 64 (rread_k l n p) /\ getr regs1 18 = Z_to_bv 64 (n - p) /\
    getr regs1 19 = Z_to_bv 64 (f + 232) /\
    (forall r : bv 5, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv ->
       r <> 13%bv -> r <> 18%bv -> r <> 19%bv -> getr regs1 r = getr regs r).
Proof.
intros regs m rom f d l b p n sp G2 G10 G11 G12 Hsp Hf0 Hf Hd Hl Hp Hn Hb0 Hbn PS PF V152 Vpos Vlen Vbuf Vfl.
unfold SRC_FILE_BLOCK in Hf.
pose proof CODE as (Hpc0 & Hpc4 & Hpc1 & Htr & _).
unfold p1_mem.
destruct (Z.ltb_spec (n - p) l) as [EOF|NEOF].
- (* l > n - p: F_EOF is set and k = n - p *)
  replace (l >? n - p) with true by (symmetry; apply Z.gtb_lt; lia).
  eexists. split.
  +
    eapply (mx_addi segs pc tr CODE) with (off := 0x0) (v := Z_to_bv 64 (sp - 48)); [lia | INL | reflexivity | exact D00 | reflexivity | mr_addr |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x4) (a := sp - 8) (v := bv_unsigned (getr regs 1)); [lia | INL | reflexivity | exact D04 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x8) (a := sp - 16) (v := bv_unsigned (getr regs 8)); [lia | INL | reflexivity | exact D08 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0xc) (a := sp - 24) (v := bv_unsigned (getr regs 9)); [lia | INL | reflexivity | exact D0c | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x10) (a := sp - 32) (v := bv_unsigned (getr regs 18)); [lia | INL | reflexivity | exact D10 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x14) (a := sp - 40) (v := bv_unsigned (getr regs 19)); [lia | INL | reflexivity | exact D14 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x18) (v := Z_to_bv 64 l); [lia | INL | reflexivity | exact D18 | reflexivity | mr_addr |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x1c) (v := Z_to_bv 64 f); [lia | INL | reflexivity | exact D1c | reflexivity | mr_addr |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x20) (a := f + 152) (v := f + 232); [lia | INL | reflexivity | exact D20 | reflexivity | mr_addr | lia | mr_vwb V152 |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x24) (a := f + 232) (v := p); [lia | INL | reflexivity | exact D24 | reflexivity | mr_addr | lia | mr_vwb Vpos |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x28) (a := f + 240) (v := n); [lia | INL | reflexivity | exact D28 | reflexivity | mr_addr | lia | mr_vwb Vlen |].
    eapply (mx_op segs pc tr CODE) with (off := 0x2c) (v := Z_to_bv 64 (n - p)); [lia | INL | reflexivity | exact D2c | reflexivity | rg; rewrite alu_sub; unfold v_sub; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_op segs pc tr CODE) with (off := 0x30) (v := Z_to_bv 64 0); [lia | INL | reflexivity | exact D30 | reflexivity | rg; rewrite alu_sltu; unfold v_sltu; rewrite c_ltu_ltb, !mr_lit by lia; destruct (Z.ltb_spec n (n - p)); [lia | reflexivity] |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x34) (v := Z_to_bv 64 (-1)); [lia | INL | reflexivity | exact D34 | reflexivity | mr_addr |].
    eapply (mx_op segs pc tr CODE) with (off := 0x38) (v := Z_to_bv 64 (n - p)); [lia | INL | reflexivity | exact D38 | reflexivity | rg; rewrite alu_and; apply mr_and_m1; lia |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x3c) (v := Z_to_bv 64 d); [lia | INL | reflexivity | exact D3c | reflexivity | mr_addr |].
    eapply (mx_bgeu_ft segs pc tr CODE) with (off := 0x40); [lia | INL | reflexivity | exact D40 | rg; rewrite c_ltu_ltb, !mr_lit by lia; apply Z.ltb_lt; lia |].
    eapply (mx_lw segs pc tr CODE) with (off := 0x44) (a := f) (v := 8) (v' := Z_to_bv 64 8);
      [lia | INL | reflexivity | exact D44 | reflexivity | mr_addr | lia | mr_vwb Vfl | apply bv_eq; vm_compute; reflexivity |].
    eapply (mx_ori segs pc tr CODE) with (off := 0x48) (v := Z_to_bv 64 24);
      [lia | INL | reflexivity | exact D48 | reflexivity | rg; apply bv_eq; vm_compute; reflexivity |].
    eapply (mx_sw segs pc tr CODE) with (off := 0x4c) (a := f) (v := 24);
      [lia | INL | reflexivity | exact D4c | mr_addr | rg; reflexivity | lia | lia | mr_prs PF |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x50) (a := f + 232) (v := p);
      [lia | INL | reflexivity | exact D50 | reflexivity | mr_addr | lia | mr_vwb Vpos |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x54) (v := Z_to_bv 64 (n - p));
      [lia | INL | reflexivity | exact D54 | reflexivity | mr_addr |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x58) (a := f + 256) (v := b); [lia | INL | reflexivity | exact D58 | reflexivity | mr_addr | lia | mr_vwb Vbuf |].
    eapply (mx_op segs pc tr CODE) with (off := 0x5c) (v := Z_to_bv 64 (b + p)); [lia | INL | reflexivity | exact D5c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x60) (v := Z_to_bv 64 (rread_k l n p)); [lia | INL | reflexivity | exact D60 | reflexivity | rg; mr_simm; rewrite mr_vaddi; f_equal; unfold rread_k; lia |].
    eapply (mx_jal segs pc tr CODE); [left; lia |].
    apply mst_refl.
  + rg. repeat split; try (f_equal; unfold rread_k; lia); try reflexivity.
    intros r H1 H2 H8 H9 H10 H11 H12 H13 H18 H19. repeat (rewrite getr_other by assumption). reflexivity.
- (* l <= n - p: k = l *)
  replace (l >? n - p) with false by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; lia).
  eexists. split.
  +
    eapply (mx_addi segs pc tr CODE) with (off := 0x0) (v := Z_to_bv 64 (sp - 48)); [lia | INL | reflexivity | exact D00 | reflexivity | mr_addr |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x4) (a := sp - 8) (v := bv_unsigned (getr regs 1)); [lia | INL | reflexivity | exact D04 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x8) (a := sp - 16) (v := bv_unsigned (getr regs 8)); [lia | INL | reflexivity | exact D08 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0xc) (a := sp - 24) (v := bv_unsigned (getr regs 9)); [lia | INL | reflexivity | exact D0c | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x10) (a := sp - 32) (v := bv_unsigned (getr regs 18)); [lia | INL | reflexivity | exact D10 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x14) (a := sp - 40) (v := bv_unsigned (getr regs 19)); [lia | INL | reflexivity | exact D14 | mr_addr | rg; reflexivity | lia | lia | mr_prs PS |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x18) (v := Z_to_bv 64 l); [lia | INL | reflexivity | exact D18 | reflexivity | mr_addr |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x1c) (v := Z_to_bv 64 f); [lia | INL | reflexivity | exact D1c | reflexivity | mr_addr |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x20) (a := f + 152) (v := f + 232); [lia | INL | reflexivity | exact D20 | reflexivity | mr_addr | lia | mr_vwb V152 |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x24) (a := f + 232) (v := p); [lia | INL | reflexivity | exact D24 | reflexivity | mr_addr | lia | mr_vwb Vpos |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x28) (a := f + 240) (v := n); [lia | INL | reflexivity | exact D28 | reflexivity | mr_addr | lia | mr_vwb Vlen |].
    eapply (mx_op segs pc tr CODE) with (off := 0x2c) (v := Z_to_bv 64 (n - p)); [lia | INL | reflexivity | exact D2c | reflexivity | rg; rewrite alu_sub; unfold v_sub; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_op segs pc tr CODE) with (off := 0x30) (v := Z_to_bv 64 0); [lia | INL | reflexivity | exact D30 | reflexivity | rg; rewrite alu_sltu; unfold v_sltu; rewrite c_ltu_ltb, !mr_lit by lia; destruct (Z.ltb_spec n (n - p)); [lia | reflexivity] |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x34) (v := Z_to_bv 64 (-1)); [lia | INL | reflexivity | exact D34 | reflexivity | mr_addr |].
    eapply (mx_op segs pc tr CODE) with (off := 0x38) (v := Z_to_bv 64 (n - p)); [lia | INL | reflexivity | exact D38 | reflexivity | rg; rewrite alu_and; apply mr_and_m1; lia |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x3c) (v := Z_to_bv 64 d); [lia | INL | reflexivity | exact D3c | reflexivity | mr_addr |].
    eapply (mx_bgeu_tk segs pc tr CODE) with (off := 0x40) (d := 24); [lia | INL | reflexivity | exact D40 | rg; rewrite c_ltu_ltb, !mr_lit by lia; apply Z.ltb_ge; lia | vm_compute; reflexivity |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x58) (a := f + 256) (v := b); [lia | INL | reflexivity | exact D58 | reflexivity | mr_addr | lia | mr_vwb Vbuf |].
    eapply (mx_op segs pc tr CODE) with (off := 0x5c) (v := Z_to_bv 64 (b + p)); [lia | INL | reflexivity | exact D5c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x60) (v := Z_to_bv 64 (rread_k l n p)); [lia | INL | reflexivity | exact D60 | reflexivity | rg; mr_simm; rewrite mr_vaddi; f_equal; unfold rread_k; lia |].
    eapply (mx_jal segs pc tr CODE); [left; lia |].
    apply mst_refl.
  + rg. repeat split; try (f_equal; unfold rread_k; lia); try reflexivity.
    intros r H1 H2 H8 H9 H10 H11 H12 H13 H18 H19. repeat (rewrite getr_other by assumption). reflexivity.
Qed.
End p.

(* ---------------------------------------------------------------------- *)
(* 4. Phase 2: after the first memcpy (+0x68) -> the second call (+0xa4).  *)
(* ---------------------------------------------------------------------- *)
Section p2. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variables pc tr : Z.
Hypothesis CODE : mread_code segs pc tr.

Definition p2_mem (m : word -> option byte) (f c r : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (f + 232)) (Z_to_le_bytes 8 c))
    (Z_to_bv 64 (f + 8)) (Z_to_le_bytes 8 (f + 280))) (Z_to_bv 64 (f + 16)) (Z_to_le_bytes 8 (f + 280 + r)).

Lemma mr_phase2 : forall regs m rom (f b p n k sp : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 k -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 18 = Z_to_bv 64 (n - p) -> getr regs 19 = Z_to_bv 64 (f + 232) ->
  0 < f -> f + SRC_FILE_BLOCK < 2 ^ 47 -> 0 <= k -> p + k <= n -> 0 <= p -> n < 2 ^ 63 -> 0 <= b -> b + n < 2 ^ 63 ->
  (forall a, f + 232 <= a < f + 240 -> present m a) -> (forall a, f + 8 <= a < f + 24 -> present m a) ->
  val_mem segs m (f + 232) 8 p -> val_mem segs m (f + 96) 8 SRC_BUFSIZ -> val_mem segs m (f + 88) 8 (f + 280) ->
  val_mem segs m (f + 256) 8 b ->
  exists regs1,
    msteps segs (mkst regs (Z_to_bv 64 (pc + 0x68)) m rom)
      (mkst regs1 (Z_to_bv 64 tr) (p2_mem m f (p + k) (Z.min (n - p - k) SRC_BUFSIZ)) rom) /\
    getr regs1 1 = Z_to_bv 64 (pc + 0xa8) /\ getr regs1 10 = Z_to_bv 64 (f + 280) /\
    getr regs1 11 = Z_to_bv 64 (b + (p + k)) /\ getr regs1 12 = Z_to_bv 64 (Z.min (n - p - k) SRC_BUFSIZ) /\
    getr regs1 18 = Z_to_bv 64 (Z.min (n - p - k) SRC_BUFSIZ) /\
    (forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 18%bv -> getr regs1 r = getr regs r).
Proof.
intros regs m rom f b p n k sp G2 G8 G9 G18 G19 Hf0 Hf Hk Hpk Hp Hn Hb0 Hbn PC PW Vpos Vbs Vbb Vbuf.
unfold SRC_FILE_BLOCK, SRC_BUFSIZ in *.
pose proof CODE as (Hpc0 & Hpc4 & Hpc1 & Htr & _).
unfold p2_mem.
destruct (Z.ltb_spec (n - p - k) 1024) as [SM|BG].
- replace (Z.min (n - p - k) 1024) with (n - p - k) by lia.
  eexists. split.
  + eapply (mx_ld segs pc tr CODE) with (off := 0x68) (a := f + 232) (v := p); [lia | INL | reflexivity | exact D68 | reflexivity | mr_addr | lia | exact Vpos |].
    eapply (mx_op segs pc tr CODE) with (off := 0x6c) (v := Z_to_bv 64 (p + k)); [lia | INL | reflexivity | exact D6c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite G8, !mr_lit by lia; reflexivity |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x70) (a := f + 232) (v := p + k); [lia | INL | reflexivity | exact D70 | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PC |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x74) (a := f + 96) (v := 1024); [lia | INL | reflexivity | exact D74 | reflexivity | mr_addr | lia | mr_vwb Vbs |].
    eapply (mx_op segs pc tr CODE) with (off := 0x78) (v := Z_to_bv 64 (n - p - k)); [lia | INL | reflexivity | exact D78 | reflexivity | rg; rewrite alu_sub; unfold v_sub; rewrite G18, G8, !mr_lit by lia; f_equal; lia |].
    eapply (mx_bltu_tk segs pc tr CODE) with (off := 0x7c) (d := 8); [lia | INL | reflexivity | exact D7c | rg; rewrite c_ltu_ltb, !mr_lit by lia; apply Z.ltb_lt; lia | vm_compute; reflexivity |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x84) (a := f + 88) (v := f + 280); [lia | INL | reflexivity | exact D84 | reflexivity | mr_addr | lia | mr_vwb Vbb |].
    eapply (mx_op segs pc tr CODE) with (off := 0x88) (v := Z_to_bv 64 (f + 280 + (n - p - k))); [lia | INL | reflexivity | exact D88 | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x8c) (a := f + 8) (v := f + 280); [lia | INL | reflexivity | exact D8c | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PW |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x90) (a := f + 16) (v := f + 280 + (n - p - k)); [lia | INL | reflexivity | exact D90 | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PW |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x94) (a := f + 232) (v := p + k); [lia | INL | reflexivity | exact D94 | reflexivity | mr_addr | lia |
      repeat (eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]); apply mr_val_hit; mr_zl |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x98) (a := f + 256) (v := b); [lia | INL | reflexivity | exact D98 | reflexivity | mr_addr | lia | mr_vwb Vbuf |].
    eapply (mx_op segs pc tr CODE) with (off := 0x9c) (v := Z_to_bv 64 (b + (p + k))); [lia | INL | reflexivity | exact D9c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_addi segs pc tr CODE) with (off := 0xa0) (v := Z_to_bv 64 (n - p - k)); [lia | INL | reflexivity | exact Da0 | reflexivity | mr_addr |].
    eapply (mx_jal segs pc tr CODE); [right; lia |].
    apply mst_refl.
  + rg. repeat split; try (f_equal; lia); try reflexivity.
    intros r H1 H10 H11 H12 H18. repeat (rewrite getr_other by assumption). reflexivity.
- replace (Z.min (n - p - k) 1024) with 1024 by lia.
  eexists. split.
  + eapply (mx_ld segs pc tr CODE) with (off := 0x68) (a := f + 232) (v := p); [lia | INL | reflexivity | exact D68 | reflexivity | mr_addr | lia | exact Vpos |].
    eapply (mx_op segs pc tr CODE) with (off := 0x6c) (v := Z_to_bv 64 (p + k)); [lia | INL | reflexivity | exact D6c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite G8, !mr_lit by lia; reflexivity |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x70) (a := f + 232) (v := p + k); [lia | INL | reflexivity | exact D70 | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PC |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x74) (a := f + 96) (v := 1024); [lia | INL | reflexivity | exact D74 | reflexivity | mr_addr | lia | mr_vwb Vbs |].
    eapply (mx_op segs pc tr CODE) with (off := 0x78) (v := Z_to_bv 64 (n - p - k)); [lia | INL | reflexivity | exact D78 | reflexivity | rg; rewrite alu_sub; unfold v_sub; rewrite G18, G8, !mr_lit by lia; f_equal; lia |].
    eapply (mx_bltu_ft segs pc tr CODE) with (off := 0x7c); [lia | INL | reflexivity | exact D7c | rg; rewrite c_ltu_ltb, !mr_lit by lia; apply Z.ltb_ge; lia |].
    eapply (mx_addi segs pc tr CODE) with (off := 0x80) (v := Z_to_bv 64 1024); [lia | INL | reflexivity | exact D80 | reflexivity | mr_addr |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x84) (a := f + 88) (v := f + 280); [lia | INL | reflexivity | exact D84 | reflexivity | mr_addr | lia | mr_vwb Vbb |].
    eapply (mx_op segs pc tr CODE) with (off := 0x88) (v := Z_to_bv 64 (f + 280 + 1024)); [lia | INL | reflexivity | exact D88 | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x8c) (a := f + 8) (v := f + 280); [lia | INL | reflexivity | exact D8c | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PW |].
    eapply (mx_sd segs pc tr CODE) with (off := 0x90) (a := f + 16) (v := f + 280 + 1024); [lia | INL | reflexivity | exact D90 | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PW |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x94) (a := f + 232) (v := p + k); [lia | INL | reflexivity | exact D94 | reflexivity | mr_addr | lia |
      repeat (eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]); apply mr_val_hit; mr_zl |].
    eapply (mx_ld segs pc tr CODE) with (off := 0x98) (a := f + 256) (v := b); [lia | INL | reflexivity | exact D98 | reflexivity | mr_addr | lia | mr_vwb Vbuf |].
    eapply (mx_op segs pc tr CODE) with (off := 0x9c) (v := Z_to_bv 64 (b + (p + k))); [lia | INL | reflexivity | exact D9c | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite !mr_lit by lia; reflexivity |].
    eapply (mx_addi segs pc tr CODE) with (off := 0xa0) (v := Z_to_bv 64 1024); [lia | INL | reflexivity | exact Da0 | reflexivity | mr_addr |].
    eapply (mx_jal segs pc tr CODE); [right; lia |].
    apply mst_refl.
  + rg. repeat split; try (f_equal; lia); try reflexivity.
    intros r H1 H10 H11 H12 H18. repeat (rewrite getr_other by assumption). reflexivity.
Qed.
End p2.

(* ---------------------------------------------------------------------- *)
(* 5. Phase 3: after the second memcpy (+0xa8) -> the return.              *)
(* ---------------------------------------------------------------------- *)
Section p3. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variables pc tr : Z.
Hypothesis CODE : mread_code segs pc tr.

Lemma mr_phase3 : forall regs m rom (f c k r sp : Z) (ra v8 v9 v18 v19 : word),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 k -> getr regs 18 = Z_to_bv 64 r ->
  getr regs 19 = Z_to_bv 64 (f + 232) ->
  0 < f -> f + SRC_FILE_BLOCK <= sp - 48 -> 4096 <= sp <= 2 ^ 47 -> 0 <= c -> 0 <= r -> c + r < 2 ^ 63 -> 0 <= k < 2 ^ 63 ->
  YK0s.ret_ok ra ->
  (forall a, f + 232 <= a < f + 240 -> present m a) ->
  val_mem segs m (f + 232) 8 c ->
  val_mem segs m (sp - 8) 8 (bv_unsigned ra) -> val_mem segs m (sp - 16) 8 (bv_unsigned v8) ->
  val_mem segs m (sp - 24) 8 (bv_unsigned v9) -> val_mem segs m (sp - 32) 8 (bv_unsigned v18) ->
  val_mem segs m (sp - 40) 8 (bv_unsigned v19) ->
  exists regs1,
    msteps segs (mkst regs (Z_to_bv 64 (pc + 0xa8)) m rom)
      (mkst regs1 ra (wbytes m (Z_to_bv 64 (f + 232)) (Z_to_le_bytes 8 (c + r))) rom) /\
    getr regs1 1 = ra /\ getr regs1 2 = Z_to_bv 64 sp /\ getr regs1 8 = v8 /\ getr regs1 9 = v9 /\
    getr regs1 10 = Z_to_bv 64 k /\ getr regs1 18 = v18 /\ getr regs1 19 = v19 /\
    (forall q : bv 5, q <> 1%bv -> q <> 2%bv -> q <> 8%bv -> q <> 9%bv -> q <> 10%bv -> q <> 18%bv -> q <> 19%bv ->
       getr regs1 q = getr regs q).
Proof.
intros regs m rom f c k r sp ra v8 v9 v18 v19 G2 G8 G18 G19 Hf0 Hf Hsp Hc Hr Hcr Hk Hret PC Vc V1 V8 V9 V18 V19.
unfold SRC_FILE_BLOCK in *.
pose proof CODE as (Hpc0 & Hpc4 & Hpc1 & Htr & _).
pose proof (u64_range ra). pose proof (u64_range v8). pose proof (u64_range v9). pose proof (u64_range v18). pose proof (u64_range v19).
eexists. split.
- eapply (mx_ld segs pc tr CODE) with (off := 0xa8) (a := f + 232) (v := c); [lia | INL | reflexivity | exact Da8 | reflexivity | mr_addr | lia | exact Vc |].
  eapply (mx_op segs pc tr CODE) with (off := 0xac) (v := Z_to_bv 64 (c + r)); [lia | INL | reflexivity | exact Dac | reflexivity | rg; rewrite alu_add; unfold v_add; rewrite G18, !mr_lit by lia; reflexivity |].
  eapply (mx_sd segs pc tr CODE) with (off := 0xb0) (a := f + 232) (v := c + r); [lia | INL | reflexivity | exact Db0 | mr_addr | rg; rewrite mr_lit by lia; reflexivity | lia | lia | mr_prs PC |].
  eapply (mx_addi segs pc tr CODE) with (off := 0xb4) (v := Z_to_bv 64 k); [lia | INL | reflexivity | exact Db4 | reflexivity | mr_addr |].
  eapply (mx_ld segs pc tr CODE) with (off := 0xb8) (a := sp - 8) (v := bv_unsigned ra); [lia | INL | reflexivity | exact Db8 | reflexivity | mr_addr | lia | mr_vwb V1 |].
  eapply (mx_ld segs pc tr CODE) with (off := 0xbc) (a := sp - 16) (v := bv_unsigned v8); [lia | INL | reflexivity | exact Dbc | reflexivity | mr_addr | lia | mr_vwb V8 |].
  eapply (mx_ld segs pc tr CODE) with (off := 0xc0) (a := sp - 24) (v := bv_unsigned v9); [lia | INL | reflexivity | exact Dc0 | reflexivity | mr_addr | lia | mr_vwb V9 |].
  eapply (mx_ld segs pc tr CODE) with (off := 0xc4) (a := sp - 32) (v := bv_unsigned v18); [lia | INL | reflexivity | exact Dc4 | reflexivity | mr_addr | lia | mr_vwb V18 |].
  eapply (mx_ld segs pc tr CODE) with (off := 0xc8) (a := sp - 40) (v := bv_unsigned v19); [lia | INL | reflexivity | exact Dc8 | reflexivity | mr_addr | lia | mr_vwb V19 |].
  eapply (mx_addi segs pc tr CODE) with (off := 0xcc) (v := Z_to_bv 64 sp); [lia | INL | reflexivity | exact Dcc | reflexivity | mr_addr |].
  rewrite !Z_to_bv_bv_unsigned.
  apply (mx_ret segs pc tr CODE); [lia | rg; reflexivity | exact Hret].
- rg. rewrite ?Z_to_bv_bv_unsigned. repeat split; try reflexivity.
  intros q Q1 Q2 Q8 Q9 Q10 Q18 Q19. repeat (rewrite getr_other by assumption). reflexivity.
Qed.
End p3.

(* ---------------------------------------------------------------------- *)
(* 6. Glue lemmas for the walk inside the caller's journal.                *)
(* ---------------------------------------------------------------------- *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_intrin_at (YCbq.v:1953-2004), with the interceptor's same_but_materialized kept in the post:
   the contract pins m_fds / m_fs, which the journal alone relates only through fds_rel / fs_rel. *)
Lemma mr_intrin_at : forall op pc, aintrin_realizes segs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.

Lemma mr_present_ap : forall H mem a, apresent H mem a -> present (mrestrict H mem) a.
Proof. intros H mem a [Hh [b Hb]]. exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.

Lemma mr_val8_uniq : forall m a v1 v2, 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
  val_mem segs m a 8 v1 -> val_mem segs m a 8 v2 -> v1 = v2.
Proof.
intros m a v1 v2 H1 H2 V1 V2.
pose proof (mr_rdn_val segs m a 8 v1 H1 V1) as R1. pose proof (mr_rdn_val segs m a 8 v2 H2 V2) as R2.
assert (E : Z_to_le_bytes 8 v1 = Z_to_le_bytes 8 v2) by congruence. apply (f_equal bytes_le_to_Z) in E.
rewrite !bytes_le_Z_to_le in E by lia. rewrite !Z.mod_small in E by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia). exact E.
Qed.

Lemma mr_win_len : forall m f W, 0 < f -> f + SRC_FILE_BLOCK < 2 ^ 64 ->
  source_window segs m f W -> source_window segs m f [] -> length W = 0%nat.
Proof.
intros m f W Hf Hfb HW H0.
destruct HW as [(-> & _ & _) | (i & Hi & HiW & R1 & R2 & _)]; [reflexivity|].
unfold SRC_FILE_BLOCK, SRC_BUF_OFF, SRC_BUFSIZ in *.
assert (X1 : 0 <= f + 280 + i < 2 ^ 64) by lia.
assert (X2 : 0 <= f + 280 + i + Z.of_nat (length W) < 2 ^ 64) by lia.
destruct H0 as [(_ & Z1 & Z2) | (i' & Hi' & Hi'W & R1' & R2' & _)].
- exfalso. pose proof (mr_val8_uniq _ _ (f + 280 + i) 0 X1 ltac:(lia) R1 Z1) as E. lia.
- unfold SRC_BUF_OFF, SRC_BUFSIZ in *. cbn [length] in Hi'W, R2'.
  assert (X3 : 0 <= f + 280 + i' < 2 ^ 64) by lia.
  assert (X4 : 0 <= f + 280 + i' + 0 < 2 ^ 64) by lia.
  pose proof (mr_val8_uniq _ _ _ _ X1 X3 R1 R1') as E1.
  pose proof (mr_val8_uniq _ _ _ _ X2 X4 R2 R2') as E2. lia.
Qed.

Lemma mr_val1_xfer : forall H H' m m' x y v, aview segs H' m' x = aview segs H m y ->
  val_mem segs (mrestrict H m) y 1 v -> val_mem segs (mrestrict H' m') x 1 v.
Proof.
intros H H' m m' x y v E V k Hk. assert (k = 0%nat) by lia. subst k.
specialize (V 0%nat Hk). change (Z.of_nat 0) with 0 in *. rewrite !Z.add_0_r in *.
unfold aview in E. rewrite V in E.
destruct (mbyte segs (mrestrict H' m') x) as [b1|] eqn:E1; cbn in E; [|discriminate].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma mr_ra_kept : forall (ma mb : word -> option byte) H a len,
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs H mb s = aview segs H ma s) ->
  0 <= a -> a + len <= kHighMemEnd -> range_addressable (aview segs H ma) SHADOW_OFF a len ->
  range_addressable (aview segs H mb) SHADOW_OFF a len.
Proof.
intros ma mb H a len AVB Ha Hl HR. eapply range_addressable_agree; [|exact HR]. intros z Hz.
change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z). apply AVB. apply shadow_addr_bounds. zlia.
Qed.

Lemma mr_hull_kept : forall (ma mb : word -> option byte) H a len,
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs H mb s = aview segs H ma s) ->
  0 <= a -> 1 <= len -> a + len <= kHighMemEnd -> shadow_hull_vis (aview segs H ma) a len ->
  shadow_hull_vis (aview segs H mb) a len.
Proof.
intros ma mb H a len AVB Ha Hl1 Hl HVS s Hs. rewrite AVB; [exact (HVS s Hs)|].
pose proof (shadow_addr_bounds a ltac:(zlia)) as [B1 B2]. pose proof (shadow_addr_bounds (a + len - 1) ltac:(zlia)) as [T1 T2].
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (a + len - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (a + len - 1)) 8 ltac:(lia)).
unfold kLowMemEnd, kHighShadowEnd in *. lia.
Qed.

Lemma mr_ra_sub : forall rd a n a' n', range_addressable rd SHADOW_OFF a n -> a <= a' -> a' + n' <= a + n ->
  range_addressable rd SHADOW_OFF a' n'.
Proof. intros rd a n a' n' HR H1 H2 x Hx. apply HR. lia. Qed.

Lemma mr_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> a <= a' -> 1 <= n' -> a' + n' <= a + n ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV H1 H2 H3 s Hs. apply HV.
pose proof (shadow_mono a a' H1). pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)).
assert (shadow_addr a / 8 * 8 <= shadow_addr a' / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
assert (shadow_addr (a' + n' - 1) / 8 * 8 <= shadow_addr (a + n - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma mr_unr_eq : forall (H : word -> bool) (memc m1 : word -> option byte) (Wr : Z -> Prop),
  (forall x : word, ~ Wr (bv_unsigned x) -> m1 x = mrestrict H memc x) ->
  forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H (munrestrict H memc m1) x = mrestrict H memc x.
Proof.
intros H memc m1 Wr Hm x Hx. unfold mrestrict, munrestrict.
destruct (H x) eqn:E; [reflexivity|]. rewrite (Hm x Hx). unfold mrestrict. rewrite E. reflexivity.
Qed.

Lemma mr_unr_grows : forall (H : word -> bool) (memc m1 : word -> option byte),
  mem_grows (mrestrict H memc) m1 -> mem_grows (mrestrict H memc) (mrestrict H (munrestrict H memc m1)).
Proof.
intros H memc m1 G x Hx. unfold mrestrict, munrestrict in *. destruct (H x) eqn:E; [exact Hx|]. apply G. rewrite E. exact Hx.
Qed.

Lemma mr_unr_hid : forall (H : word -> bool) (memc m1 : word -> option byte) x, H x = true -> munrestrict H memc m1 x = memc x.
Proof. intros H memc m1 x E. unfold munrestrict. rewrite E. reflexivity. Qed.
End G.

(* ---------------------------------------------------------------------- *)
(* 7. What the three phases leave in memory.                               *)
(* ---------------------------------------------------------------------- *)
Section mf. Context {fx : YK11.FPState}.
Variable segs : list Segment.

Lemma mr_p1_out : forall m regs sp f eof (x : word), 48 <= sp <= 2 ^ 47 -> 0 <= f -> f + 4 <= 2 ^ 47 ->
  ~ ((sp - 40 <= bv_unsigned x < sp) \/ (f <= bv_unsigned x < f + 4)) -> p1_mem m regs sp f eof x = m x.
Proof.
intros m regs sp f eof x Hsp Hf Hf4 Hx. pose proof (u64_range x).
unfold p1_mem. destruct eof;
  repeat (rewrite mr_wb_out; [| lia | rewrite length_Z_to_le_bytes; mr_zl | rewrite length_Z_to_le_bytes; mr_zl]); reflexivity.
Qed.

Lemma mr_p1_slots : forall m regs sp f eof, 48 <= sp <= 2 ^ 47 -> 0 <= f -> f + 4 <= sp - 48 ->
  val_mem segs (p1_mem m regs sp f eof) (sp - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem segs (p1_mem m regs sp f eof) (sp - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem segs (p1_mem m regs sp f eof) (sp - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem segs (p1_mem m regs sp f eof) (sp - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem segs (p1_mem m regs sp f eof) (sp - 40) 8 (bv_unsigned (getr regs 19)).
Proof.
intros m regs sp f eof Hsp Hf Hf4.
pose proof (u64_range (getr regs 1)). pose proof (u64_range (getr regs 8)). pose proof (u64_range (getr regs 9)).
pose proof (u64_range (getr regs 18)). pose proof (u64_range (getr regs 19)).
unfold p1_mem. destruct eof; repeat split;
  repeat (first [apply mr_val_hit; mr_zl | eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]]).
Qed.

Lemma mr_p1_flags : forall m regs sp f eof, 48 <= sp <= 2 ^ 47 -> 0 <= f -> f + 4 <= sp - 48 ->
  val_mem segs m f 4 8 -> val_mem segs (p1_mem m regs sp f eof) f 4 (if eof then 24 else 8).
Proof.
intros m regs sp f eof Hsp Hf Hf4 V. unfold p1_mem. destruct eof.
- apply mr_val_hit; mr_zl.
- repeat (eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]). exact V.
Qed.

Lemma mr_p2_out : forall m f c r (x : word), 0 <= f -> f + 1304 <= 2 ^ 47 ->
  ~ ((f + 232 <= bv_unsigned x < f + 240) \/ (f + 8 <= bv_unsigned x < f + 24)) -> p2_mem m f c r x = m x.
Proof.
intros m f c r x Hf Hfb Hx. pose proof (u64_range x).
unfold p2_mem.
repeat (rewrite mr_wb_out; [| lia | rewrite length_Z_to_le_bytes; mr_zl | rewrite length_Z_to_le_bytes; mr_zl]); reflexivity.
Qed.

Lemma mr_p2_vals : forall m f c r, 0 <= f -> f + 1304 <= 2 ^ 47 -> 0 <= c < 2 ^ 64 -> 0 <= r <= 1024 ->
  val_mem segs (p2_mem m f c r) (f + 232) 8 c /\ val_mem segs (p2_mem m f c r) (f + 8) 8 (f + 280) /\
  val_mem segs (p2_mem m f c r) (f + 16) 8 (f + 280 + r).
Proof.
intros m f c r Hf Hfb Hc Hr. unfold p2_mem. repeat split;
  repeat (first [apply mr_val_hit; mr_zl | eapply mr_val_wbz; [lia | mr_zl | lia | mr_zl | mr_zl |]]).
Qed.

Lemma mr_p3_out : forall m f c (x : word), 0 <= f -> f + 1304 <= 2 ^ 47 ->
  ~ (f + 232 <= bv_unsigned x < f + 240) -> wbytes m (Z_to_bv 64 (f + 232)) (Z_to_le_bytes 8 c) x = m x.
Proof.
intros m f c x Hf Hfb Hx. pose proof (u64_range x).
rewrite mr_wb_out; [reflexivity | lia | rewrite length_Z_to_le_bytes; mr_zl | rewrite length_Z_to_le_bytes; mr_zl].
Qed.

Lemma mr_ap_unr : forall (H : word -> bool) (memc m1 : word -> option byte) a,
  mem_grows (mrestrict H memc) m1 -> apresent H memc a -> apresent H (munrestrict H memc m1) a.
Proof.
intros H memc m1 a G [Hh [b Hb]]. split; [exact Hh|]. unfold munrestrict. rewrite Hh.
assert (Hs : mrestrict H memc (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (G _ Hs). destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | contradiction].
Qed.

Lemma mr_nth_fs : forall (C : list Z) a c i, (i < a)%nat -> nth i (firstn a (skipn c C)) 0 = nth (c + i) C 0.
Proof.
intros C a c. revert C a. induction c as [|c IH]; intros C a i Hi.
- cbn [skipn Nat.add]. revert C i Hi. induction a as [|a IHa]; intros C i Hi; [lia|].
  destruct C as [|x C]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IHa. lia.
- destruct C as [|x C]; [cbn [skipn]; destruct a; destruct i; reflexivity|]. cbn [skipn]. rewrite IH by exact Hi. reflexivity.
Qed.
End mf.

(* ---------------------------------------------------------------------- *)
(* 8. The theorem: PFreadM.v's rmread_contract, at mread's entry pc.       *)
(* ---------------------------------------------------------------------- *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Variables pc tr : Z.
(* The image facts (as cgif's AE27.v takes LAWS / TB / AIL as Section hypotheses). *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis ASIL : asource_img_laws SK segs B K.
Hypothesis CODE : mread_code segs pc tr.
Hypothesis MEMCPY : aintrin_realizes segs B OCpy tr.

Lemma mr_cs : forall (R R' : bvmap 5 word) (r : bv 5), aregs_preserved R R' -> acallee_saved (bv_unsigned r) -> getr R' r = getr R r.
Proof. intros R R' r AP Hc. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply AP. exact Hc. Qed.

Ltac neq := let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.
Ltac csv := unfold acallee_saved; repeat match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Theorem rmread_contract_proved : rmread_contract segs B K pc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f d l b p mo C PRE.
destruct PRE as (CALL & G10 & G11 & G12 & HFb & Hbb & Hboff & HSRC & HFL & HMO & WRF & Hl & DEST).
destruct CALL as (HJ & Hret & Hra4 & Hgp & Htp & Hal & Hwin & Hsp0 & Hch).
destruct DEST as (DF & DB & Hd0 & Hdam & Hdat & WRD & Hdra & Hdhull).
assert (RS : RMREAD_STK = 4144) by reflexivity. rewrite RS in *.
assert (FB : SRC_FILE_BLOCK = 1304) by reflexivity. rewrite FB in *.
set (n := Z.of_nat (length C)) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (En : n = Z.of_nat (length C)) by reflexivity.
set (sp := spZ regs) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & JF1 & JF2 & JF3 & JF4 & Hgone & Hpres & Hstatic & JF5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hsp_lo : alloc_ceiling + 4144 <= sp) by lia.
assert (Hsp_hi : sp <= 2 ^ 47) by lia.
assert (E2 : getr regs 2 = Z_to_bv 64 sp) by (unfold sp, spZ; symmetry; apply Z_to_bv_bv_unsigned).
destruct (al_blocks _ _ LAWS _ _ _ _ _ f 1304 HAR HFb) as (Hf16 & Hf4096 & Hfceil & Hfapp & Hfbytes & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hbb) as (_ & Hb4096 & Hbceil & Hbapp & Hbbytes & _ & _).
change (req_size 1304) with 1304 in *.
assert (Hrq : n <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
pose proof CODE as (Hpc0 & Hpc4 & Hpc1 & Htr & _).
(* the stream at entry: its window is empty, so the cookie position is p *)
destruct HSRC as (HAT & HWIN0).
destruct HAT as (Wd0 & cpos & fl0 & md00 & HAT). cbv zeta in HAT.
destruct HAT as (Hp0 & Hpc & Hcn & Hn63 & Hbn64 & Hcpos & HWd0 & Hbok & HC & HST & HWIN & HFL0 & HFL24 & HMD0 & HCP & HENV & HHEAD & Hfnz).
pose proof (mr_win_len segs _ f Wd0 ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) HWIN HWIN0) as HW0.
rewrite HW0 in Hcpos. change (Z.of_nat 0) with 0 in Hcpos. rewrite Z.add_0_r in Hcpos. subst cpos.
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & S240 & S248 & S256 & S264 & S152 & S32 & S40 & S48 & S56 & S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & SFB).
unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ in *.
assert (PSm : forall a, sp - 48 <= a < sp -> present (mrestrict (w_H W) memc) a).
{ intros a Ha. apply mr_present_ap. apply Hpres. lia. }
assert (PFm : forall a, f <= a < f + 1304 -> present (mrestrict (w_H W) memc) a).
{ intros a Ha. apply mr_present_ap. exact (proj1 (Hfbytes a Ha)). }
assert (Hdl : d + l <= 2 ^ 47) by (clear - Hdam C4 C5 Hl; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Hj : 0 <= rread_k l n p <= l /\ rread_k l n p <= n - p) by (unfold rread_k; lia).
assert (Hr : 0 <= rmread_fill l n p <= 1024 /\ rmread_fill l n p <= n - p - rread_k l n p) by (unfold rmread_fill, SRC_BUFSIZ; lia).
set (j := rread_k l n p) in *.
set (r := rmread_fill l n p) in *.
assert (Er : Z.min (n - p - j) 1024 = r) by reflexivity.
(* ------------------------------------------------------------------ *)
(* phase 1                                                             *)
(* ------------------------------------------------------------------ *)
destruct (mr_phase1 segs pc tr CODE regs (mrestrict (w_H W) memc) (seg_rom segs) f d l b p n sp E2 G10 G11 G12
  ltac:(lia) ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) Hl ltac:(lia) Hn63 ltac:(lia) ltac:(lia)
  PSm (fun a Ha => PFm a ltac:(lia)) S152 HCP S240 S256 (proj1 HFL))
  as (regs1 & HMS1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_12 & R1_18 & R1_19 & R1_oth).
fold j in R1_8, R1_12.
unfold cfg_at, w64.
set (m1 := p1_mem (mrestrict (w_H W) memc) regs sp f (l >? n - p)) in *.
eapply (SRr_msteps segs Hwx W _ (mkst regs1 (Z_to_bv 64 tr) m1 (seg_rom segs)) mdc).
{ rewrite restrict_mkst_fx. exact HMS1. }
intros md1 Hsbm1 Hcl1.
pose proof (mrestrict_unrestrict_mem (w_H W) memc _ Hcl1) as EA. cbn [ms_mem unrestrict mkst] in EA.
set (memA := munrestrict (w_H W) memc m1) in *.
match goal with |- SRr _ _ {| cfg_ms := ?X; cfg_model := _ |} _ => change X with (mkst regs1 (Z_to_bv 64 tr) memA (seg_rom segs)) end.
assert (HJ1 : ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memA md1 k).
{ eapply (ajournal_exec segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memA md1
    (fun a => (sp - 40 <= a < sp) \/ (f <= a < f + 4)) HJ).
  - apply (mr_unr_eq (w_H W) memc m1 (fun a => (sp - 40 <= a < sp) \/ (f <= a < f + 4))). intros x Hx. apply mr_p1_out; [lia | lia | lia | exact Hx].
  - apply mr_unr_grows. exact (msteps_mem_grows segs _ _ HMS1).
  - intros x Hx. apply mr_unr_hid. exact Hx.
  - exact Hsbm1.
  - intros a [Ha|Ha]; [unfold awr_byte; left; lia | exact (proj1 (WRF a ltac:(lia)))]. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 40 <= a < sp) \/ (f <= a < f + 4)) ->
  aview segs (w_H W) memA a = aview segs (w_H W) memc a).
{ intros a Ha Hna. apply aview_eq_of.
  apply (mr_unr_eq (w_H W) memc m1 (fun a => (sp - 40 <= a < sp) \/ (f <= a < f + 4))).
  - intros x Hx. apply mr_p1_out; [lia | lia | lia | exact Hx].
  - rewrite mr_lit by lia. exact Hna. }
assert (PA : forall a, apresent (w_H W) memc a -> apresent (w_H W) memA a).
{ intros a Ha. apply mr_ap_unr; [exact (msteps_mem_grows segs _ _ HMS1) | exact Ha]. }
pose proof (mr_p1_slots segs (mrestrict (w_H W) memc) regs sp f (l >? n - p) ltac:(lia) ltac:(lia) ltac:(lia))
  as (VA1 & VA8 & VA9 & VA18 & VA19).
pose proof (mr_p1_flags segs (mrestrict (w_H W) memc) regs sp f (l >? n - p) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 HFL)) as VAF.
fold m1 in VA1, VA8, VA9, VA18, VA19, VAF. rewrite <- EA in VA1, VA8, VA9, VA18, VA19, VAF.
assert (BANDA : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) memA s = aview segs (w_H W) memc s).
{ intros s Hs. apply KA; [unfold kLowMemEnd, kHighShadowEnd in Hs; lia|]. clear - Hs Hfapp Hsp_lo C1 C2 C3 C4 C5. zlia. }
(* ------------------------------------------------------------------ *)
(* the first memcpy: d .. d + j from b + p                              *)
(* ------------------------------------------------------------------ *)
assert (Ho1 : spZ regs1 = sp0 + (sp - 48 - sp0)) by (unfold spZ; rewrite R1_2, mr_lit by lia; lia).
assert (Hgp1 : getr regs1 3 = w64 (as_gp B)) by (rewrite R1_oth by neq; exact Hgp).
assert (Htp1 : getr regs1 4 = w64 (as_tp B)) by (rewrite R1_oth by neq; exact Htp).
assert (Hraw1 : YK0s.ret_ok (Z_to_bv 64 (pc + 0x68))) by (apply ret_ok_even; rewrite mr_lit by lia; lia).
assert (Hbp : forall a, b <= a < b + n -> apresent (w_H W) memA a) by (intros a Ha; apply PA; exact (proj1 (Hbbytes a ltac:(lia)))).
eapply SRr_bind.
{ eapply (mr_intrin_at segs B LAWS segs_low OCpy tr MEMCPY W regs1 memA STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k
    d (b + p) j (sp - 48 - sp0) (Z_to_bv 64 (pc + 0x68)) HJ1 R1_10 R1_11 R1_12).
  - lia.
  - lia.
  - lia.
  - exact Ho1.
  - clear - Hal Hal16. lia.
  - lia.
  - unfold ESTACK. lia.
  - exact Hgp1.
  - exact Htp1.
  - exact R1_1.
  - exact Hraw1.
  - intros a Ha. destruct (WRD a ltac:(lia)) as [Hw Hnw]. split; [exact Hw | unfold ESTACK; lia].
  - clear - Hdam Hj. unfold amem_range in *. lia.
  - apply (mr_ra_kept segs memc memA (w_H W) d j BANDA); [lia | unfold kHighMemEnd; lia |].
    apply (mr_ra_sub _ d l); [exact Hdra | lia | lia].
  - intros Hj0. apply (mr_hull_kept segs memc memA (w_H W) d j BANDA); [lia | lia | unfold kHighMemEnd; lia |].
    apply (mr_hull_sub _ d l); [apply Hdhull; lia | lia | lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply aview_some_of_apresent; apply Hbp; lia | rewrite Ho1; unfold ESTACK; lia]. }
    split; [lia|]. split; [apply (amem_range_of_block segs B LAWS lyc Sc W memc mdc b n); [exact HAR | exact Hbb | lia | lia]|].
    split; [apply (range_addressable_of_block segs B LAWS lyc Sc W memA md1 b n); [exact (proj1 HJ1) | exact Hbb | lia | lia]|].
    intros Hj0. destruct (al_shadow _ _ LAWS lyc Sc W memA md1 b n (proj1 HJ1) Hbb) as (_ & HHb).
    apply (mr_hull_sub _ b (req_size n)); [exact HHb | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & AP2 & R2_10 & EFF2 & KEEP2 & PRES2 & SBM2).
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + j) -> ~ (sp - 4144 <= a < sp) -> ~ (f <= a < f + 4) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2 H3. rewrite (KEEP2 a Ha H1 ltac:(unfold ESTACK; lia)). apply KA; [exact Ha | lia]. }
(* ------------------------------------------------------------------ *)
(* phase 2                                                             *)
(* ------------------------------------------------------------------ *)
assert (R2_2 : getr regs2 2 = Z_to_bv 64 (sp - 48)) by (rewrite (mr_cs regs1 regs2 2 AP2) by csv; exact R1_2).
assert (R2_8 : getr regs2 8 = Z_to_bv 64 j) by (rewrite (mr_cs regs1 regs2 8 AP2) by csv; exact R1_8).
assert (R2_9 : getr regs2 9 = Z_to_bv 64 f) by (rewrite (mr_cs regs1 regs2 9 AP2) by csv; exact R1_9).
assert (R2_18 : getr regs2 18 = Z_to_bv 64 (n - p)) by (rewrite (mr_cs regs1 regs2 18 AP2) by csv; exact R1_18).
assert (R2_19 : getr regs2 19 = Z_to_bv 64 (f + 232)) by (rewrite (mr_cs regs1 regs2 19 AP2) by csv; exact R1_19).
assert (PF2 : forall a, f <= a < f + 1304 -> apresent (w_H W) mem2 a) by (intros a Ha; apply PRES2; apply PA; exact (proj1 (Hfbytes a Ha))).
assert (VK2 : forall a nn v, f + 4 <= a -> a + Z.of_nat nn <= f + 1304 ->
  val_mem segs (mrestrict (w_H W) memc) a nn v -> val_mem segs (mrestrict (w_H W) mem2) a nn v).
{ intros a nn v H1 H2 V. apply (val_mem_kept segs (w_H W) (w_H W) memc mem2); [|exact V].
  intros q Hq. apply K2c; lia. }
destruct (mr_phase2 segs pc tr CODE regs2 (mrestrict (w_H W) mem2) (seg_rom segs) f b p n j sp R2_2 R2_8 R2_9 R2_18 R2_19
  ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hn63 ltac:(lia) ltac:(lia)
  (fun a Ha => mr_present_ap _ _ _ (PF2 a ltac:(lia))) (fun a Ha => mr_present_ap _ _ _ (PF2 a ltac:(lia)))
  (VK2 (f + 232) 8%nat p ltac:(lia) ltac:(cbn; lia) HCP) (VK2 (f + 96) 8%nat 1024 ltac:(lia) ltac:(cbn; lia) S96)
  (VK2 (f + 88) 8%nat (f + 280) ltac:(lia) ltac:(cbn; lia) S88) (VK2 (f + (232 + 24)) 8%nat b ltac:(lia) ltac:(cbn; lia) S256))
  as (regs3 & HMS2 & R3_1 & R3_10 & R3_11 & R3_12 & R3_18 & R3_oth).
unfold SRC_BUFSIZ in HMS2, R3_12, R3_18. rewrite Er in HMS2, R3_12, R3_18.
set (m3 := p2_mem (mrestrict (w_H W) mem2) f (p + j) r) in *.
eapply (SRr_msteps segs Hwx W _ (mkst regs3 (Z_to_bv 64 tr) m3 (seg_rom segs)) md2).
{ rewrite restrict_mkst_fx. exact HMS2. }
intros md3 Hsbm3 Hcl3.
pose proof (mrestrict_unrestrict_mem (w_H W) mem2 _ Hcl3) as EB. cbn [ms_mem unrestrict mkst] in EB.
set (memB := munrestrict (w_H W) mem2 m3) in *.
match goal with |- SRr _ _ {| cfg_ms := ?X; cfg_model := _ |} _ => change X with (mkst regs3 (Z_to_bv 64 tr) memB (seg_rom segs)) end.
assert (HJ3 : ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB md3 k).
{ eapply (ajournal_exec segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k memB md3
    (fun a => (f + 232 <= a < f + 240) \/ (f + 8 <= a < f + 24)) HJ2).
  - apply (mr_unr_eq (w_H W) mem2 m3 (fun a => (f + 232 <= a < f + 240) \/ (f + 8 <= a < f + 24))).
    intros x Hx. apply mr_p2_out; [lia | lia | exact Hx].
  - apply mr_unr_grows. exact (msteps_mem_grows segs _ _ HMS2).
  - intros x Hx. apply mr_unr_hid. exact Hx.
  - exact Hsbm3.
  - intros a [Ha|Ha]; exact (proj1 (WRF a ltac:(lia))). }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ ((f + 232 <= a < f + 240) \/ (f + 8 <= a < f + 24)) ->
  aview segs (w_H W) memB a = aview segs (w_H W) mem2 a).
{ intros a Ha Hna. apply aview_eq_of.
  apply (mr_unr_eq (w_H W) mem2 m3 (fun a => (f + 232 <= a < f + 240) \/ (f + 8 <= a < f + 24))).
  - intros x Hx. apply mr_p2_out; [lia | lia | exact Hx].
  - rewrite mr_lit by lia. exact Hna. }
assert (PB : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memB a).
{ intros a Ha. apply mr_ap_unr; [exact (msteps_mem_grows segs _ _ HMS2) | exact Ha]. }
pose proof (mr_p2_vals segs (mrestrict (w_H W) mem2) f (p + j) r ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (VB232 & VB8 & VB16).
fold m3 in VB232, VB8, VB16. rewrite <- EB in VB232, VB8, VB16.
(* ------------------------------------------------------------------ *)
(* the second memcpy: f + 280 .. f + 280 + r from b + p + j              *)
(* ------------------------------------------------------------------ *)
assert (R3_2 : getr regs3 2 = Z_to_bv 64 (sp - 48)) by (rewrite R3_oth by neq; exact R2_2).
assert (Ho3 : spZ regs3 = sp0 + (sp - 48 - sp0)) by (unfold spZ; rewrite R3_2, mr_lit by lia; lia).
assert (Hgp3 : getr regs3 3 = w64 (as_gp B)) by (rewrite R3_oth by neq; rewrite (mr_cs regs1 regs2 3 AP2) by csv; exact Hgp1).
assert (Htp3 : getr regs3 4 = w64 (as_tp B)) by (rewrite R3_oth by neq; rewrite (mr_cs regs1 regs2 4 AP2) by csv; exact Htp1).
assert (Hraw3 : YK0s.ret_ok (Z_to_bv 64 (pc + 0xa8))) by (apply ret_ok_even; rewrite mr_lit by lia; lia).
assert (KBc : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + j) -> ~ (sp - 4144 <= a < sp) -> ~ (f <= a < f + 4) ->
   ~ (f + 8 <= a < f + 24) -> ~ (f + 232 <= a < f + 240) -> aview segs (w_H W) memB a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2 H3 H4 H5. rewrite (KB a Ha ltac:(lia)). apply K2c; assumption. }
assert (Hbp3 : forall a, b <= a < b + n -> apresent (w_H W) memB a) by (intros a Ha; apply PB; apply PRES2; apply Hbp; exact Ha).
eapply SRr_bind.
{ eapply (mr_intrin_at segs B LAWS segs_low OCpy tr MEMCPY W regs3 memB STK sp0 FP ly S W0 mem0 md0 own lyc Sc md3 k
    (f + 280) (b + (p + j)) r (sp - 48 - sp0) (Z_to_bv 64 (pc + 0xa8)) HJ3 R3_10 R3_11 R3_12).
  - lia.
  - lia.
  - lia.
  - exact Ho3.
  - clear - Hal Hal16. lia.
  - lia.
  - unfold ESTACK. lia.
  - exact Hgp3.
  - exact Htp3.
  - exact R3_1.
  - exact Hraw3.
  - intros a Ha. split; [exact (proj1 (WRF a ltac:(lia))) | unfold ESTACK; lia].
  - apply (amem_range_of_block segs B LAWS lyc Sc W memc mdc f 1304); [exact HAR | exact HFb | lia | change (req_size 1304) with 1304; lia].
  - apply (range_addressable_of_block segs B LAWS lyc Sc W memB md3 f 1304); [exact (proj1 HJ3) | exact HFb | lia | change (req_size 1304) with 1304; lia].
  - intros Hr0. destruct (al_shadow _ _ LAWS lyc Sc W memB md3 f 1304 (proj1 HJ3) HFb) as (_ & HHf).
    change (req_size 1304) with 1304 in HHf. apply (mr_hull_sub _ f 1304); [exact HHf | lia | lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply aview_some_of_apresent; apply Hbp3; lia | rewrite Ho3; unfold ESTACK; lia]. }
    split; [lia|]. split; [apply (amem_range_of_block segs B LAWS lyc Sc W memc mdc b n); [exact HAR | exact Hbb | lia | lia]|].
    split; [apply (range_addressable_of_block segs B LAWS lyc Sc W memB md3 b n); [exact (proj1 HJ3) | exact Hbb | lia | lia]|].
    intros Hr0. destruct (al_shadow _ _ LAWS lyc Sc W memB md3 b n (proj1 HJ3) Hbb) as (_ & HHb).
    apply (mr_hull_sub _ b (req_size n)); [exact HHb | lia | lia | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & AP4 & R4_10 & EFF4 & KEEP4 & PRES4 & SBM4).
(* ------------------------------------------------------------------ *)
(* phase 3                                                             *)
(* ------------------------------------------------------------------ *)
assert (R4_2 : getr regs4 2 = Z_to_bv 64 (sp - 48)) by (rewrite (mr_cs regs3 regs4 2 AP4) by csv; exact R3_2).
assert (R4_8 : getr regs4 8 = Z_to_bv 64 j) by (rewrite (mr_cs regs3 regs4 8 AP4) by csv; rewrite R3_oth by neq; exact R2_8).
assert (R4_18 : getr regs4 18 = Z_to_bv 64 r) by (rewrite (mr_cs regs3 regs4 18 AP4) by csv; exact R3_18).
assert (R4_19 : getr regs4 19 = Z_to_bv 64 (f + 232)) by (rewrite (mr_cs regs3 regs4 19 AP4) by csv; rewrite R3_oth by neq; exact R2_19).
assert (DW : forall a, d <= a < d + j -> ~ (sp - 4144 <= a < sp)) by (intros a Ha; exact (proj2 (WRD a ltac:(lia)))).
assert (K4c : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + j) -> ~ (sp - 4144 <= a < sp) -> ~ (f <= a < f + 4) ->
   ~ (f + 8 <= a < f + 24) -> ~ (f + 232 <= a < f + 240) -> ~ (f + 280 <= a < f + 280 + r) ->
   aview segs (w_H W) mem4 a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2 H3 H4 H5 H6. rewrite (KEEP4 a Ha H6 ltac:(unfold ESTACK; lia)). apply KBc; assumption. }
assert (VK4slot : forall a v, sp - 40 <= a -> a + 8 <= sp ->
   val_mem segs (mrestrict (w_H W) memA) a 8 v -> val_mem segs (mrestrict (w_H W) mem4) a 8 v).
{ intros a v H1 H2 V. apply (val_mem_kept segs (w_H W) (w_H W) memA mem4); [|exact V].
  intros q Hq. cbn in Hq.
  rewrite (KEEP4 (a + q) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
  rewrite (KB (a + q) ltac:(lia) ltac:(lia)).
  apply (KEEP2 (a + q) ltac:(lia)); [intros X; apply (DW _ X); lia | unfold ESTACK; lia]. }
assert (PF4 : forall a, f <= a < f + 1304 -> apresent (w_H W) mem4 a) by (intros a Ha; apply PRES4; apply PB; apply PF2; exact Ha).
assert (V4c : val_mem segs (mrestrict (w_H W) mem4) (f + 232) 8 (p + j)).
{ apply (val_mem_kept segs (w_H W) (w_H W) memB mem4); [|exact VB232].
  intros q Hq. cbn in Hq. apply KEEP4; [lia | lia | unfold ESTACK; lia]. }
destruct (mr_phase3 segs pc tr CODE regs4 (mrestrict (w_H W) mem4) (seg_rom segs) f (p + j) j r sp
  (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) R4_2 R4_8 R4_18 R4_19
  ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
  (fun a Ha => mr_present_ap _ _ _ (PF4 a ltac:(lia))) V4c
  (VK4slot (sp - 8) _ ltac:(lia) ltac:(lia) VA1) (VK4slot (sp - 16) _ ltac:(lia) ltac:(lia) VA8)
  (VK4slot (sp - 24) _ ltac:(lia) ltac:(lia) VA9) (VK4slot (sp - 32) _ ltac:(lia) ltac:(lia) VA18)
  (VK4slot (sp - 40) _ ltac:(lia) ltac:(lia) VA19))
  as (regs5 & HMS3 & R5_1 & R5_2 & R5_8 & R5_9 & R5_10 & R5_18 & R5_19 & R5_oth).
set (m5 := wbytes (mrestrict (w_H W) mem4) (Z_to_bv 64 (f + 232)) (Z_to_le_bytes 8 (p + j + r))) in *.
eapply (SRr_msteps segs Hwx W _ (mkst regs5 (getr regs 1) m5 (seg_rom segs)) md4).
{ rewrite restrict_mkst_fx. exact HMS3. }
intros md5 Hsbm5 Hcl5.
pose proof (mrestrict_unrestrict_mem (w_H W) mem4 _ Hcl5) as EC. cbn [ms_mem unrestrict mkst] in EC.
set (memC := munrestrict (w_H W) mem4 m5) in *.
match goal with |- SRr _ _ {| cfg_ms := ?X; cfg_model := _ |} _ => change X with (mkst regs5 (getr regs 1) memC (seg_rom segs)) end.
assert (HJ5 : ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memC md5 k).
{ eapply (ajournal_exec segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem4 md4 k memC md5
    (fun a => f + 232 <= a < f + 240) HJ4).
  - apply (mr_unr_eq (w_H W) mem4 m5 (fun a => f + 232 <= a < f + 240)).
    intros x Hx. apply mr_p3_out; [lia | lia | exact Hx].
  - apply mr_unr_grows. exact (msteps_mem_grows segs _ _ HMS3).
  - intros x Hx. apply mr_unr_hid. exact Hx.
  - exact Hsbm5.
  - intros a Ha; exact (proj1 (WRF a ltac:(lia))). }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (f + 232 <= a < f + 240) -> aview segs (w_H W) memC a = aview segs (w_H W) mem4 a).
{ intros a Ha Hna. apply aview_eq_of.
  apply (mr_unr_eq (w_H W) mem4 m5 (fun a => f + 232 <= a < f + 240)).
  - intros x Hx. apply mr_p3_out; [lia | lia | exact Hx].
  - rewrite mr_lit by lia. exact Hna. }
assert (PC : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) memC a).
{ intros a Ha. apply mr_ap_unr; [exact (msteps_mem_grows segs _ _ HMS3) | exact Ha]. }
assert (VC232 : val_mem segs (mrestrict (w_H W) memC) (f + 232) 8 (p + j + r)).
{ rewrite EC. unfold m5. apply mr_val_hit; [lia | mr_zl | lia]. }
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + j) -> ~ (sp - 4144 <= a < sp) -> ~ (f <= a < f + 4) ->
   ~ (f + 8 <= a < f + 24) -> ~ (f + 232 <= a < f + 240) -> ~ (f + 280 <= a < f + 280 + r) ->
   aview segs (w_H W) memC a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2 H3 H4 H5 H6. rewrite (KC a Ha H5). apply K4c; assumption. }
assert (PALL : forall a, apresent (w_H W) memc a -> apresent (w_H W) memC a).
{ intros a Ha. apply PC, PRES4, PB, PRES2, PA. exact Ha. }
assert (SBM : same_but_materialized mdc md5).
{ eapply same_but_materialized_trans; [exact Hsbm1|]. eapply same_but_materialized_trans; [exact SBM2|].
  eapply same_but_materialized_trans; [exact Hsbm3|]. eapply same_but_materialized_trans; [exact SBM4 | exact Hsbm5]. }
pose proof (same_but_materialized_frame _ _ SBM) as (_ & _ & _ & _ & _ & _ & _ & _ & Efds & _ & _ & Efs & _).
(* where the destination lies: not in the shadow band, not in the image, below the ceiling or on the stack *)
assert (DOFF : forall a, d <= a < d + l -> ~ (kLowMemEnd <= a < kHighShadowEnd) /\ ~ in_img segs a).
{ intros a Ha. destruct Hdat as [(cid & pos & Hin & Hfr) | [(Hlo & Hhi) | (bb & nn & Hin & Hb1 & Hb2)]].
  - pose proof (Hfr a Ha) as Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & F3).
    split; [clear - Hz F3 C1 C2 C3 C4 C5; zlia|].
    apply (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin). lia.
  - split; [clear - Hlo Ha Eslo Hceil C1 C2 C3 C4 C5; zlia|]. intros Hi. pose proof (segs_low a Hi). clear - H Hlo Ha Eslo Hceil C1 C5. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ bb nn HAR Hin) as (_ & _ & Hbbc & Hbbapp & _ & _ & _).
    assert (Hrqb : nn <= req_size nn) by (unfold req_size; destruct (nn =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
    split; [clear - Hb1 Hb2 Ha Hbbapp Hrqb C1 C2 C3 C4 C5; zlia|].
    apply (blk_img segs B LAWS lyc Sc W memc mdc bb nn a HAR Hin). lia. }
assert (FOFF : forall a, f <= a < f + 1304 -> ~ (kLowMemEnd <= a < kHighShadowEnd) /\ ~ in_img segs a).
{ intros a Ha. split; [clear - Ha Hfapp C1 C2 C3 C4 C5; zlia|].
  apply (blk_img segs B LAWS lyc Sc W memc mdc f 1304 a HAR HFb). change (req_size 1304) with 1304. lia. }
assert (KIMG : forall a, in_img segs a -> aview segs (w_H W) memC a = aview segs (w_H W) memc a).
{ intros a Hi. pose proof (segs_low a Hi) as Ha. apply KALL; try lia.
  - intros X. apply (proj2 (DOFF a ltac:(lia))). exact Hi.
  - intros X. apply (proj2 (FOFF a ltac:(lia))). exact Hi.
  - intros X. apply (proj2 (FOFF a ltac:(lia))). exact Hi.
  - intros X. apply (proj2 (FOFF a ltac:(lia))). exact Hi.
  - intros X. apply (proj2 (FOFF a ltac:(lia))). exact Hi. }
assert (KENV : forall a, asrc_env_addr K a -> aview segs (w_H W) memC a = aview segs (w_H W) memc a).
{ intros a Ha. apply KIMG. exact (proj1 (asil_env _ _ _ _ ASIL a Ha)). }
assert (KFILE : forall a, f + 24 <= a < f + 232 \/ f + 240 <= a < f + 280 -> aview segs (w_H W) memC a = aview segs (w_H W) memc a).
{ intros a Ha. apply KALL; lia. }
assert (VKF : forall a nn v, (f + 24 <= a /\ a + Z.of_nat nn <= f + 232) \/ (f + 240 <= a /\ a + Z.of_nat nn <= f + 280) ->
  val_mem segs (mrestrict (w_H W) memc) a nn v -> val_mem segs (mrestrict (w_H W) memC) a nn v).
{ intros a nn v Hr' V. apply (val_mem_kept segs (w_H W) (w_H W) memc memC); [|exact V]. intros q Hq. apply KFILE. lia. }
assert (VKE : forall a nn v, (forall q, 0 <= q < Z.of_nat nn -> asrc_env_addr K (a + q)) ->
  val_mem segs (mrestrict (w_H W) memc) a nn v -> val_mem segs (mrestrict (w_H W) memC) a nn v).
{ intros a nn v He V. apply (val_mem_kept segs (w_H W) (w_H W) memc memC); [|exact V]. intros q Hq. apply KENV. apply He. exact Hq. }
assert (VC8 : val_mem segs (mrestrict (w_H W) memC) (f + 8) 8 (f + 280)).
{ apply (val_mem_kept segs (w_H W) (w_H W) memB memC); [|exact VB8]. intros q Hq. cbn in Hq.
  rewrite (KC (f + 8 + q) ltac:(lia) ltac:(lia)). apply KEEP4; [lia | lia | unfold ESTACK; lia]. }
assert (VC16 : val_mem segs (mrestrict (w_H W) memC) (f + 16) 8 (f + 280 + r)).
{ apply (val_mem_kept segs (w_H W) (w_H W) memB memC); [|exact VB16]. intros q Hq. cbn in Hq.
  rewrite (KC (f + 16 + q) ltac:(lia) ltac:(lia)). apply KEEP4; [lia | lia | unfold ESTACK; lia]. }
assert (VCF : val_mem segs (mrestrict (w_H W) memC) f 4 (if l >? n - p then 24 else 8)).
{ apply (val_mem_kept segs (w_H W) (w_H W) memA memC); [|exact VAF]. intros q Hq. cbn in Hq.
  rewrite (KC (f + q) ltac:(lia) ltac:(lia)). rewrite (KEEP4 (f + q) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
  rewrite (KB (f + q) ltac:(lia) ltac:(lia)). apply (KEEP2 (f + q) ltac:(lia)); [lia | unfold ESTACK; lia]. }
cbn in EFF2, EFF4.
(* ------------------------------------------------------------------ *)
(* the post                                                            *)
(* ------------------------------------------------------------------ *)
apply SRr_ret. unfold rread_post_base.
exists lyc, Sc, regs5, memC, md5.
split; [reflexivity|].
split; [exact HJ5|].
split.
{ intros z Hz.
  assert (Hzc : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/
    z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
  destruct Hzc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R5_2. symmetry; exact E2.
  - rewrite R5_oth by neq. rewrite (AP4 3 Hz). rewrite R3_oth by neq. rewrite (AP2 3 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 4 Hz). rewrite R3_oth by neq. rewrite (AP2 4 Hz). rewrite R1_oth by neq. reflexivity.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R5_8. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R5_9. reflexivity.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R5_18. reflexivity.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R5_19. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 20 Hz). rewrite R3_oth by neq. rewrite (AP2 20 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 21 Hz). rewrite R3_oth by neq. rewrite (AP2 21 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 22 Hz). rewrite R3_oth by neq. rewrite (AP2 22 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 23 Hz). rewrite R3_oth by neq. rewrite (AP2 23 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 24 Hz). rewrite R3_oth by neq. rewrite (AP2 24 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 25 Hz). rewrite R3_oth by neq. rewrite (AP2 25 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 26 Hz). rewrite R3_oth by neq. rewrite (AP2 26 Hz). rewrite R1_oth by neq. reflexivity.
  - rewrite R5_oth by neq. rewrite (AP4 27 Hz). rewrite R3_oth by neq. rewrite (AP2 27 Hz). rewrite R1_oth by neq. reflexivity. }
split.
{ unfold rread_kept, rread_wrset, SRC_FILE_BLOCK.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw Hn'. apply KALL; lia.
  - intros b' m' i Hin Hi Hn'. destruct (al_blocks _ _ LAWS _ _ _ _ _ b' m' HAR Hin) as (_ & Hb'4 & Hb'c & _).
    apply KALL; lia.
  - intros a Hi _ _. apply KIMG. exact Hi.
  - intros cid pos a Hin Hz Hn'. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb0. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
    destruct Hz as [Hz | Hz].
    + apply KALL; lia.
    + pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(clear - F1 F2 C1 C4 Hfb0; zlia)) as [B1 B2].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb0) as Hse.
      pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(clear - F2 F1 C1 C4 Hfb0; zlia)) as [T1 T2].
      apply KALL; unfold kLowMemEnd, kHighShadowEnd in *; lia.
  - intros a Ha Hw Hp'. apply PALL. exact Hp'.
  - intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP5 & _). apply HP5. lia. }
unfold rmread_post. cbv zeta. change (Z.of_nat (length C)) with n. change (rread_k l n p) with j. change (rmread_fill l n p) with r.
split; [reflexivity|]. split; [reflexivity|].
split; [exact R5_10|].
split.
{ intros i Hi. rewrite length_firstn, length_skipn in Hi. fold n in Hi.
  rewrite mr_nth_fs by lia.
  split.
  - apply (mr_val1_xfer segs (w_H W) (w_H W) memc memC (d + Z.of_nat i) (b + Z.of_nat (Z.to_nat p + i))).
    + pose proof (DW (d + Z.of_nat i) ltac:(lia)) as Hdw.
      rewrite (KC (d + Z.of_nat i) ltac:(lia) ltac:(lia)).
      rewrite (KEEP4 (d + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
      rewrite (KB (d + Z.of_nat i) ltac:(lia) ltac:(lia)).
      rewrite (EFF2 (Z.of_nat i) ltac:(lia)).
      rewrite (KA (b + p + Z.of_nat i) ltac:(lia) ltac:(lia)).
      f_equal. lia.
    + exact (proj1 (HC (Z.to_nat p + i)%nat ltac:(lia))).
  - exact (proj2 (HC (Z.to_nat p + i)%nat ltac:(lia))). }
assert (HLW : Z.of_nat (length (firstn (Z.to_nat r) (skipn (Z.to_nat (p + j)) C))) = r)
  by (rewrite length_firstn, length_skipn; fold n; lia).
split.
{ exists (firstn (Z.to_nat r) (skipn (Z.to_nat (p + j)) C)), (p + j + r), (if l >? n - p then 24 else 8), mo.
  cbv zeta. change (Z.of_nat (length C)) with n.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hn63|]. split; [exact Hbn64|].
  split; [lia|].
  split; [replace (p + j + r - (p + j)) with r by lia; reflexivity|].
  split; [exact Hbok|].
  split.
  { apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) memC) b C HC). intros a Ha. fold n in Ha.
    apply mbyte_of_aview. apply KALL; lia. }
  split.
  { unfold source_static, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK.
    repeat split; first [apply VKF; [cbn; lia | assumption] | assumption | lia]. }
  split.
  { right. exists 0. unfold SRC_BUF_OFF, SRC_BUFSIZ. split; [lia|]. split; [lia|].
    split; [rewrite Z.add_0_r; exact VC8|]. split; [rewrite Z.add_0_r, HLW; exact VC16|].
    intros i Hi. rewrite mr_nth_fs by (rewrite length_firstn, length_skipn in Hi; lia).
    rewrite length_firstn, length_skipn in Hi. fold n in Hi.
    split.
    - apply (mr_val1_xfer segs (w_H W) (w_H W) memc memC (f + 280 + 0 + Z.of_nat i) (b + Z.of_nat (Z.to_nat (p + j) + i))).
      + rewrite (KC (f + 280 + 0 + Z.of_nat i) ltac:(lia) ltac:(lia)).
        replace (f + 280 + 0 + Z.of_nat i) with (f + 280 + Z.of_nat i) by lia.
        rewrite (EFF4 (Z.of_nat i) ltac:(lia)).
        rewrite (KBc (b + (p + j) + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        f_equal. lia.
      + exact (proj1 (HC (Z.to_nat (p + j) + i)%nat ltac:(lia))).
    - exact (proj2 (HC (Z.to_nat (p + j) + i)%nat ltac:(lia))). }
  split; [split; [exact VCF | destruct (l >? n - p); auto]|].
  split; [destruct (Z.gtb_spec l (n - p)) as [E|E]; [intros _; unfold j, rread_k; lia | intros X; discriminate X]|].
  split.
  { destruct HMO as [HMO1 HMO2]. split; [apply VKF; [cbn; lia | exact HMO1] | exact HMO2]. }
  split; [exact VC232|].
  split.
  { unfold asrc_stdio_env in HENV |- *. destruct HENV as (E1 & E2' & E3 & E4 & E5 & (cv & Hcv & E6)).
    split; [apply VKE; [intros q Hq; unfold asrc_env_addr; cbn in Hq; left; lia | exact E1]|].
    split; [apply VKE; [intros q Hq; unfold asrc_env_addr; cbn in Hq; right; left; lia | exact E2']|].
    split; [apply VKE; [intros q Hq; unfold asrc_env_addr; cbn in Hq; right; right; left; lia | exact E3]|].
    split.
    { apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) memC) _ _ E4). intros a Ha. cbn in Ha.
      apply mbyte_of_aview. apply KENV. unfold asrc_env_addr. right; right; right; left. lia. }
    split.
    { apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) memC) _ _ E5). intros a Ha. cbn in Ha.
      apply mbyte_of_aview. apply KENV. unfold asrc_env_addr. right; right; right; right; left. lia. }
    exists cv. split; [exact Hcv|]. apply VKE; [intros q Hq; unfold asrc_env_addr; cbn in Hq; right; right; right; right; right; lia | exact E6]. }
  split.
  { apply VKE; [intros q Hq; unfold asrc_env_addr, as_ofl_head in *; cbn in Hq; right; right; left; lia | exact HHEAD]. }
  exact Hfnz. }
split; [exact VC232|].
split; [exact VC8|].
split; [exact VC16|].
split; [split; [exact VCF | destruct (l >? n - p); auto]|].
split.
{ destruct HMO as [HMO1 HMO2]. split; [apply VKF; [cbn; lia | exact HMO1] | exact HMO2]. }
split; [exact Efds|].
split; [exact Efs|].
intros s Hs. apply KALL; try (unfold kLowMemEnd, kHighShadowEnd in *; lia).
all: intros X; first [apply (proj1 (DOFF s ltac:(lia))); exact Hs | apply (proj1 (FOFF s ltac:(lia))); exact Hs].
Qed.
End T.
