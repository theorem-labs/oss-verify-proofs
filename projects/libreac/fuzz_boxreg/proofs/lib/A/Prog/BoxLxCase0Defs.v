(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths, module names and numbers changed; 438 of its 509 lines of code are new or changed and 734 lines of the source are left out. *)
(* The cuts inside LLVMFuzzerTestOneInput's case op & 3 = 0, declare (fuzz_boxreg.c:213-286), on the ASan build
   (fuzz_boxreg.asan 0x802ec .. 0x80ab4), between the phase cuts GI_T 0 and GI_K of BoxLxDefs.v.

   The case makes six calls: read_name (&in) at 0x8051c, range_free (&prev, base, nch, fabric) at 0x80564 or
   lowest_free (&prev, nch, fabric) at 0x80934, reac_boxreg_declare (r, nch, given, base) at 0x8095c, bcmp
   (r->box[idx].mac, ZERO, 6) at 0x809d4, strncmp (r->box[idx].name, given or "", 31) at 0x80a48 and free (name) at
   0x80aa8. The walk is cut at the slot after each call that is followed by more of the case (and at 0x8093c, where
   the three ways of computing `want` meet), so that each piece is one straight walk to the next call and that
   call's contract:
     N  0x5d4 (0x80520)  read_name returned the name;
     W  0x9f0 (0x8093c)  `want` is in the spill slot 0x30;
     D  0xa14 (0x80960)  reac_boxreg_declare returned idx;
     B  0xa8c (0x809d8)  bcmp of the new row's MAC with ZERO returned 0 (only when the declare placed a row);
     S  0xb00 (0x80a4c)  strncmp of the new row's name returned 0 (only when the declare placed a row);
     F  0xb58 (0x80aa4)  every check is passed; free (name) follows.
   Each cut keeps the facts of GI_T that the rest of the turn needs (c0_mf), the table before the turn (bs, also in
   prev) and after the call (bs'), and the case's own values: nch = c0_nch pl, base = c0_base pl, the name (at nm,
   its bytes c0_nb, its C string c0_s), where pl = the input left at the case's start (Pau's
   lib/Prog/LLVMFuzzerTestOneInput_case0.v names). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cuts' pcs, as offsets in the listing (address - 0x7ff4c) ---- *)
Definition GC_N : Z := 0x5d4.   (* 0x80520: read_name returned            *)
Definition GC_W : Z := 0x9f0.   (* 0x8093c: want in the slot 0x30          *)
Definition GC_D : Z := 0xa14.   (* 0x80960: reac_boxreg_declare returned   *)
Definition GC_B : Z := 0xa8c.   (* 0x809d8: bcmp returned                  *)
Definition GC_S : Z := 0xb00.   (* 0x80a4c: strncmp returned               *)
Definition GC_F : Z := 0xb58.   (* 0x80aa4: free (name) follows            *)


(* ---- generic facts on symbolic words ---- *)
Lemma c0_zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma c0_zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
intros z Hz. unfold zcanon, M64.
replace (z mod 2 ^ 64) with ((z + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
apply Z.mod_small. lia.
Qed.
Lemma c0_U_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply c0_zcanon_in. exact Hx. Qed.
Lemma c0_U_off_neg : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> - 2 ^ 64 <= v + x < 0 ->
  U E (SOff n x) = v + x + 2 ^ 64.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply c0_zcanon_neg. exact Hx. Qed.
Lemma c0_U_lit_val : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply c0_zcanon_in. exact Hz. Qed.
Lemma c0_U_lit_neg : forall E z, - 2 ^ 64 <= z < 0 -> U E (SLit z) = z + 2 ^ 64.
Proof. intros E z Hz. rewrite U_SLit. apply c0_zcanon_neg. exact Hz. Qed.
Lemma c0_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma c0_denot_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.


Ltac c0_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* ---- the case's values, from the input left at its start ---- *)
Definition c0_pl (cx : bcx) (pos : Z) : list byte := skipn (Z.to_nat pos) (c_pl cx).
Definition c0_nch (cx : bcx) (pos : Z) : Z := LLVMFuzzerTestOneInput_case0.c0_nch (c0_pl cx pos).
Definition c0_base (cx : bcx) (pos : Z) : Z := LLVMFuzzerTestOneInput_case0.c0_base (c0_pl cx pos).
(* What read_name reads: the input after nch and base. *)
Definition c0_pl2 (cx : bcx) (pos : Z) : list byte := skipn 2 (c0_pl cx pos).
Definition c0_nk (cx : bcx) (pos : Z) : Z := read_name_c.rn_k (c0_pl2 cx pos).
(* The name block's bytes, its C string, and the cursor after read_name. *)
Definition c0_nb (cx : bcx) (pos : Z) : list byte :=
  Boxreg.bsub (c0_pl2 cx pos) 1 (c0_nk cx pos) ++ [Z_to_bv 8 0].
Definition c0_s (cx : bcx) (pos : Z) : list Z := LLVMFuzzerTestOneInput_rn.nm_str (c0_nb cx pos).
Definition c0_pos2 (cx : bcx) (pos : Z) : Z :=
  pos + LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) + tread_name_used (c0_pl2 cx pos).
(* The name declare gets: NULL when op & 8, else the name. *)
Definition c0_given (op nm : Z) : Z := if Z.land op 8 =? 0 then nm else 0.
Definition c0_gs (cx : bcx) (pos op : Z) : list Z := if Z.land op 8 =? 0 then c0_s cx pos else [].
(* The table after a placed declare (the contract's bytes, Pau's decl_bytes). *)
Definition c0_placed (bs : list byte) (b k p : Z) (s : list Z) : list byte :=
  BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s).


Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The machine state's control part at a pc of the case and the registers every phase keeps. *)
Definition c0_ms (cx : bcx) (fp : Z) (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\ gregs cx fp ms3.

(* The memory facts of GI_T the whole case keeps: none of these bytes is written in the case. *)
Definition c0_mf (i : Z) (cx : bcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (r : Z) (bs : list byte) : Prop :=
  gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 GSH_it /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  gslots_fr cx fp W3 ms3 /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gprev cx fp W3 ms3 bs /\ gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\
  gslot cx W3 ms3 0x68 i /\ gslot cx W3 ms3 0x48 (Boxreg.bx_n bs).

(* The bytes of the name block. *)
Definition c0_name (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) (pos nm : Z) : Prop :=
  forall j, 0 <= j <= c0_nk cx pos ->
    aview SEGS (w_H W3) (ms_mem ms3) (nm + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_nb cx pos) (Z_to_bv 8 0))).

(* The part every cut after read_name has: the turn's i, the journal's event count and allocator spending, the two
   blocks of the turn (r, the name), the table before the turn, the cursor, the name's bytes and op. *)
Definition c0_turn (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (r : Z) (bs : list byte) (pos op nm : Z) : Prop :=
  c0_mf i cx fp W3 ms3 r bs /\ 0 <= i < 64 /\ k <= 2 + 2 * i /\
  acc <= GB_A MT i + mo_malloc MT (c0_nk cx pos + 1) /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] /\
  Boxreg.boxreg_inv bs /\ 0 <= pos <= c_n cx /\ gcursor cx W3 ms3 (c0_pos2 cx pos) /\
  4096 <= nm /\ c0_name cx W3 ms3 pos nm /\
  0 <= op < 256 /\ Z.land op 3 = 0 /\
  getr (ms_regs ms3) 20 = w64 r.

(* N, 0x80520: read_name returned nm in a0; s3 = nch, s10 = base << 56, s11 = base (sign-extended), s6 = op,
   s9 = the fabric. *)
Definition C0_N (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op nm,
  c0_ms cx fp GC_N ms3 /\ c0_turn i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm /\
  greg B ly3 S3 W3 ms3 r bs /\
  getr (ms_regs ms3) 10 = w64 nm /\
  getr (ms_regs ms3) 19 = w64 (c0_nch cx pos) /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\
  getr (ms_regs ms3) 26 = w64 (c0_base cx pos * 2 ^ 56) /\ getr (ms_regs ms3) 27 = w64 (c0_base cx pos).

(* W, 0x8093c: as N, with the name in s7 and Pau's `want` (c0_want) in the slot 0x30. *)
Definition C0_W (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op nm want,
  c0_ms cx fp GC_W ms3 /\ c0_turn i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm /\
  greg B ly3 S3 W3 ms3 r bs /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nch cx pos) (c0_base cx pos) want /\ -1 <= want < 128 /\
  gslot cx W3 ms3 0x30 (want mod 2 ^ 64) /\
  getr (ms_regs ms3) 23 = w64 nm /\
  getr (ms_regs ms3) 19 = w64 (c0_nch cx pos) /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\
  getr (ms_regs ms3) 26 = w64 (c0_base cx pos * 2 ^ 56) /\ getr (ms_regs ms3) 27 = w64 (c0_base cx pos).

(* D, 0x80960: reac_boxreg_declare returned idx in a0; the name is in the slot 0x58, s9 = op & 8; the table holds
   bs' as the contract gives it: refused (idx = -1, bs' = bs) or placed (idx = n, the new row). *)
Definition C0_D (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op nm want,
  c0_ms cx fp GC_D ms3 /\ c0_turn i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nch cx pos) (c0_base cx pos) want /\ -1 <= want < 128 /\
  gslot cx W3 ms3 0x30 (want mod 2 ^ 64) /\ gslot cx W3 ms3 0x58 nm /\
  getr (ms_regs ms3) 19 = w64 (c0_nch cx pos) /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Z.land op 8) /\
  getr (ms_regs ms3) 26 = w64 (c0_base cx pos * 2 ^ 56) /\ getr (ms_regs ms3) 27 = w64 (c0_base cx pos) /\
  ((reac_boxreg_declare_c.declare_refused bs (c0_nch cx pos) (c0_base cx pos) /\
    greg B ly3 S3 W3 ms3 r bs /\ getr (ms_regs ms3) 10 = w64 (-1)) \/
   (exists b p, reac_boxreg_declare_c.declare_placed bs (c0_nch cx pos) (c0_base cx pos) b p /\
    greg B ly3 S3 W3 ms3 r (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) /\
    getr (ms_regs ms3) 10 = w64 (Boxreg.bx_n bs))).

(* B, 0x809d8 (a placed row only): bcmp returned 0; s6 = the row r + 56 n, s7 = idx = n. *)
Definition C0_B (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op nm want b p,
  c0_ms cx fp GC_B ms3 /\ c0_turn i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nch cx pos) (c0_base cx pos) want /\ -1 <= want < 128 /\
  gslot cx W3 ms3 0x30 (want mod 2 ^ 64) /\ gslot cx W3 ms3 0x58 nm /\
  reac_boxreg_declare_c.declare_placed bs (c0_nch cx pos) (c0_base cx pos) b p /\
  greg B ly3 S3 W3 ms3 r (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) /\
  getr (ms_regs ms3) 10 = w64 0 /\
  getr (ms_regs ms3) 19 = w64 (c0_nch cx pos) /\
  getr (ms_regs ms3) 22 = w64 (r + 56 * Boxreg.bx_n bs) /\ getr (ms_regs ms3) 23 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 25 = w64 (Z.land op 8) /\
  getr (ms_regs ms3) 26 = w64 (c0_base cx pos * 2 ^ 56) /\ getr (ms_regs ms3) 27 = w64 (c0_base cx pos).

(* S, 0x80a4c (a placed row only): strncmp returned 0; s3 = the row, s7 = idx = n. *)
Definition C0_S (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op nm want b p,
  c0_ms cx fp GC_S ms3 /\ c0_turn i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nch cx pos) (c0_base cx pos) want /\ -1 <= want < 128 /\
  gslot cx W3 ms3 0x30 (want mod 2 ^ 64) /\ gslot cx W3 ms3 0x58 nm /\
  reac_boxreg_declare_c.declare_placed bs (c0_nch cx pos) (c0_base cx pos) b p /\
  greg B ly3 S3 W3 ms3 r (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) /\
  getr (ms_regs ms3) 10 = w64 0 /\
  getr (ms_regs ms3) 19 = w64 (r + 56 * Boxreg.bx_n bs) /\ getr (ms_regs ms3) 23 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 25 = w64 (Z.land op 8) /\ getr (ms_regs ms3) 27 = w64 (c0_base cx pos).

(* F, 0x80aa4: every check is passed: r holds bs' with Pau's checks and llvm_kept for ren = -1; the name (nn
   bytes) is in the slot 0x58; s9 = the fabric again. *)
Definition C0_F (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs bs' pos nm nn,
  c0_ms cx fp GC_F ms3 /\ c0_mf i cx fp W3 ms3 r bs /\ 0 <= i < 64 /\ k <= 2 + 2 * i /\
  1 <= nn <= 48 /\ acc <= GB_A MT i + mo_malloc MT nn /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, nn)] /\ 4096 <= nm /\
  greg B ly3 S3 W3 ms3 r bs' /\
  Boxreg.boxreg_inv bs /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' (-1) /\
  gcursor cx W3 ms3 pos /\ gslot cx W3 ms3 0x58 nm /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs).


(* ---- the machine state of a cut, the stack pointers ---- *)
Lemma c0_mkst : forall cx fp pc ms3 (H : word -> bool), c0_ms cx fp pc ms3 ->
  restrict H ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict H (ms_mem ms3)) (seg_rom SEGS).
Proof.
intros cx fp pc [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0] H (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & _).
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
subst. reflexivity.
Qed.
Lemma c0_sp : forall cx, gb_base B MT cx ->
  alloc_ceiling + GB_STK <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 288 < c_sp1 cx <= spZ (c_regs cx) - 256 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
rewrite Hsp1. split; [lia|]. split; [lia|]. split; [|exact Hal16].
rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section d.
Hypothesis LAWS : AR_laws SEGS B.

Lemma c0_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma c0_nev : forall cx fp k ly3 S3 W3 mem md, gb_base B MT cx -> k <= 128 ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  st_nev S3 + 1 < EV_MAX.
Proof.
intros cx fp k ly3 S3 W3 mem md HB Hk HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & Hev & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn & _). unfold GB_EV in Hev. lia.
Qed.
Lemma c0_blk_twice : forall ly S W mem md l1 l2 l3 x, AR SEGS B ly S W mem md ->
  ablocks B ly S = l1 ++ x :: l2 ++ x :: l3 -> 0 < snd x -> False.
Proof.
intros ly S W mem md l1 l2 l3 [p n] HAR E Hn. cbn [snd] in Hn.
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md (p, n) (p, n) l1 l2 l3 HAR E) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (req_size_pos n ltac:(lia)) as [Hq _]. lia.
Qed.

Lemma c0_achain0 : forall cx (rd' : reader) sp', gb_base B MT cx ->
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> rd' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword rd' (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain (c_ly cx) rd' sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros cx rd' sp' HB Hk H8 H16 Hsp'.
destruct HB as (HPRE & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
unfold gch.
destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
- apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd'
           (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hk);
    [ replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact H8
    | replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16) by lia; exact H16
    | exact Hra4 | lia | exact Hal8 | lia | exact Hsp' ].
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma c0_achain : forall cx fp k ly3 S3 W3 mem md sp', gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  gsaved cx W3 (mkst (c_regs cx) (Z_to_bv 64 0) mem (seg_rom SEGS)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros cx fp k ly3 S3 W3 mem md sp' HB HJ (H8 & Hsj) Hsp. cbn [ms_mem mkst] in H8, Hsj.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
apply c0_achain0; [exact HB | intros a Ha; apply F1; unfold GB_STK in *; lia | exact H8 | | exact Hsp].
pose proof (Hsj 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
rewrite H0. unfold s0Z. do 3 f_equal.
Qed.

Lemma c0_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.
Lemma c0_budget : forall i nn acc, ameter_laws MT -> 0 <= i < 64 -> 1 <= nn <= 48 ->
  acc <= GB_A MT i + mo_malloc MT nn -> acc + mo_free MT <= GB_A MT (i + 1) /\ GB_A MT (i + 1) + mo_free MT <= GB_NEED MT.
Proof.
intros i nn acc ML Hi Hnn Hacc.
pose proof (mo_malloc_mono MT ML nn 48 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT ML 48 ltac:(lia)) as M2.
pose proof (mo_free_nonneg MT ML) as M3.
unfold GB_NEED, GB_A in *. split; [nia|]. nia.
Qed.
Lemma c0_rdword_eq : forall (m m' : word -> option byte) (H : word -> bool) a v,
  (forall j, 0 <= j < 8 -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
intros m m' H a v K Hr.
pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
pose proof (K 7 ltac:(lia)) as K7.
unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Definition c0_zone (cx : bcx) (fp a : Z) : Prop :=
  (c_sp1 cx <= a < 2 ^ 64 /\ ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) /\ ~ (c_sp1 cx + 0x58 <= a < c_sp1 cx + 0x60) /\
   ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98)) \/
  (c_p cx <= a < c_p cx + c_n cx) \/ (gF cx fp <= a < gF cx fp + 512) \/ (gSH cx fp <= a < gSH cx fp + 64).
Lemma c0_mf_keep : forall i cx fp W (ms ms' : machine_state) r bs, gb_base B MT cx ->
  (forall a, c0_zone cx fp a -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  c0_mf i cx fp W ms r bs -> c0_mf i cx fp W ms' r bs.
Proof.
intros i cx fp W ms ms' r bs HB K (SV & SH & FL & (F18 & F28 & F70 & F78 & F80) & GI & GP & (S10 & S20 & S38 & S40 & S50 & S60) & S68 & S48).
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & _).
assert (SL : forall off v, 0x10 <= off <= 0x80 -> (off + 8 <= 0x30 \/ 0x38 <= off) -> (off + 8 <= 0x58 \/ 0x60 <= off) ->
  gslot cx W ms off v -> gslot cx W ms' off v).
{ intros off v H1 H2 H3 Hv. unfold gslot in *. apply (c0_rdword_eq (ms_mem ms) (ms_mem ms') (w_H W)); [|exact Hv].
  intros j Hj. apply K. left. repeat split; lia. }
assert (Hfb : fs_frame_bytes GB_CID = 512) by reflexivity.
assert (Hlsh : length GSH_it = 52%nat) by reflexivity.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- destruct SV as (S8 & Sj). split.
  + apply (c0_rdword_eq (ms_mem ms) (ms_mem ms') (w_H W)); [|exact S8]. intros j Hj. apply K. left. repeat split; lia.
  + intros j Hj. apply (c0_rdword_eq (ms_mem ms) (ms_mem ms') (w_H W)); [|exact (Sj j Hj)].
    intros jj Hjj. apply K. left. repeat split; lia.
- intros j Hj. unfold gshadow in SH. rewrite K; [exact (SH j Hj)|]. right; right; right. lia.
- apply (c0_rdword_eq (ms_mem ms) (ms_mem ms') (w_H W)); [|exact FL]. intros j Hj. apply K. right; right; left.
  rewrite Hfb. lia.
- split; [|split; [|split; [|split]]]; (apply SL; [lia | lia | lia | assumption]).
- apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. apply (mbyte_of_aview SEGS). apply K.
  rewrite length_map in Ha. right; left. unfold c_n. lia.
- intros j Hj. rewrite K; [exact (GP j Hj)|]. right; right; left. unfold GO_PREV, REG_SIZE in *. lia.
- split; [|split; [|split; [|split; [|split]]]]; (apply SL; [lia | lia | lia | assumption]).
- apply (c0_rdword_eq (ms_mem ms) (ms_mem ms') (w_H W)); [|exact S68]. intros j Hj. apply K. left. repeat split; lia.
- apply SL; [lia | lia | lia | assumption].
Qed.

Lemma c0_mf_keep2 : forall i cx fp W W' (ms ms' : machine_state) r bs, gb_base B MT cx ->
  (forall a, c0_zone cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  c0_mf i cx fp W ms r bs -> c0_mf i cx fp W' ms' r bs.
Proof.
intros i cx fp W W' ms ms' r bs HB K (SV & SH & FL & (F18 & F28 & F70 & F78 & F80) & GI & GP & (S10 & S20 & S38 & S40 & S50 & S60) & S68 & S48).
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & _).
assert (SL : forall off v, 0x10 <= off <= 0x80 -> (off + 8 <= 0x30 \/ 0x38 <= off) -> (off + 8 <= 0x58 \/ 0x60 <= off) ->
  gslot cx W ms off v -> gslot cx W' ms' off v).
{ intros off v H1 H2 H3 Hv. unfold gslot in *. rewrite <- Hv. apply rdword_ext.
  intros j Hj. apply K. left. repeat split; lia. }
assert (Hfb : fs_frame_bytes GB_CID = 512) by reflexivity.
assert (Hlsh : length GSH_it = 52%nat) by reflexivity.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- destruct SV as (S8 & Sj). split.
  + rewrite <- S8. apply rdword_ext. intros j Hj. apply K. left. repeat split; lia.
  + intros j Hj. rewrite <- (Sj j Hj). apply rdword_ext. intros jj Hjj. apply K. left. repeat split; lia.
- intros j Hj. unfold gshadow in SH. rewrite K; [exact (SH j Hj)|]. right; right; right. lia.
- rewrite <- FL. apply rdword_ext. intros j Hj. apply K. right; right; left. rewrite Hfb. lia.
- split; [|split; [|split; [|split]]]; (apply SL; [lia | lia | lia | assumption]).
- apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. apply (mbyte_of_aview SEGS). apply K.
  rewrite length_map in Ha. right; left. unfold c_n. lia.
- intros j Hj. rewrite K; [exact (GP j Hj)|]. right; right; left. unfold GO_PREV, REG_SIZE in *. lia.
- split; [|split; [|split; [|split; [|split]]]]; (apply SL; [lia | lia | lia | assumption]).
- unfold gslot in *. rewrite <- S68. apply rdword_ext. intros j Hj. apply K. left. repeat split; lia.
- apply SL; [lia | lia | lia | assumption].
Qed.

Lemma c0_geo : forall cx fp k ly3 S3 W3 mem md, gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GB_CID, fp)] ->
  (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) /\
  frame_addr ly3 GB_CID fp = gF cx fp /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ gF cx fp mod 64 = 0 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8.
Proof.
intros cx fp k ly3 S3 W3 mem md HB HJ HFR.
pose proof HB as (HPRE & _ & _ & Hinp & _).
pose proof HPRE as (HAR0 & _).
pose proof HJ as (HAR & Hly & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly) as (_ & Efa & _).
assert (EgF : frame_addr ly3 GB_CID fp = gF cx fp) by (unfold gF; apply Efa).
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF1 & HF2 & _).
pose proof (frame_al64 SEGS B _ _ _ _ _ _ _ HAR Hfin) as (HA64 & _).
rewrite EgF in HF1, HF2, HA64. change (fs_frame_bytes GB_CID) with 512 in HF2.
split.
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
split; [exact EgF|]. split; [lia|]. split; [lia|]. split; [exact HA64|].
reflexivity.
Qed.
Lemma c0_zone_range : forall cx fp a, (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) ->
  4096 <= gF cx fp -> gF cx fp + 512 <= alloc_ceiling -> gSH cx fp = SHADOW_OFF + gF cx fp / 8 -> c_sp1 cx >= 0 ->
  c0_zone cx fp a -> 0 <= a < 2 ^ 64.
Proof.
intros cx fp a Hin HF0 HF1 HSH Hsp Ha. pose proof asan_consts as (C1 & _).
destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hin; lia | lia |].
rewrite HSH in Ha. unfold SHADOW_OFF in *.
pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Definition c0_newblk (cx : bcx) (ly3 : alayout) (S3 : astate) (Er : Z -> Prop) : Prop :=
  forall a, Er a -> exists b m, In (b, m) (ablocks B ly3 S3) /\ ~ In (b, m) (ablocks B (c_ly cx) (c_S cx)) /\ b <= a < b + req_size m.
Lemma c0_zone_blocks : forall cx fp k ly3 S3 W3 memc md (Er : Z -> Prop) (Kf : Z -> Prop),
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 memc md k ->
  frames S3 = [(GB_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  c0_newblk cx ly3 S3 Er ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> c_sp1 cx <= a -> Kf a) ->
  (forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m -> ~ Er (b + i) -> Kf (b + i)) ->
  (forall a, (in_zr a (frame_rng ly3 (GB_CID, fp)) \/ in_zr a (shadow_addr (frame_addr ly3 GB_CID fp), fs_frame_bytes GB_CID / 8)) ->
     ~ Er a -> Kf a) ->
  forall a, c0_zone cx fp a -> Kf a.
Proof.
intros cx fp k ly3 S3 W3 memc md Er Kf HB HJ HFR Hsub HNB K1 K2 K4 a Ha.
pose proof HJ as (HAR & _).
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & _). unfold GB_STK in Hsp.
pose proof (c0_geo cx fp k ly3 S3 W3 memc md HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH).
pose proof HB as (_ & _ & _ & Hpn & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (NFZ : forall a, (in_zr a (frame_rng ly3 (GB_CID, fp)) \/ in_zr a (shadow_addr (frame_addr ly3 GB_CID fp), fs_frame_bytes GB_CID / 8)) -> ~ Er a).
{ intros a0 Hz He. destruct (HNB a0 He) as (b & m & Hb & _ & Hr).
  apply (block_not_frame_zone SEGS B LAWS ly3 S3 W3 memc md b m (a0 - b) GB_CID fp HAR Hb Hfin); [lia|].
  replace (b + (a0 - b)) with a0 by lia. exact Hz. }
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- apply K1; lia.
- destruct Hpn as [(Hn0 & _) | (Hn & Hin)]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply Hsub; exact Hin).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx)); [exact Hin3 | lia |].
  intros He. destruct (HNB _ He) as (b & m & Hb & Hnc & Hr).
  assert (Hne : (b, m) <> (c_p cx, c_n cx)) by (intros E; rewrite E in Hnc; exact (Hnc Hin)).
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 memc md b m (c_p cx) (c_n cx) HAR Hb Hin3 Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
- assert (Hz : in_zr a (frame_rng ly3 (GB_CID, fp)) \/ in_zr a (shadow_addr (frame_addr ly3 GB_CID fp), fs_frame_bytes GB_CID / 8)).
  { left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EgF. change (fs_frame_bytes GB_CID) with 512. lia. }
  apply K4; [exact Hz | exact (NFZ a Hz)].
- assert (Hz : in_zr a (frame_rng ly3 (GB_CID, fp)) \/ in_zr a (shadow_addr (frame_addr ly3 GB_CID fp), fs_frame_bytes GB_CID / 8)).
  { right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EgF. change (fs_frame_bytes GB_CID / 8) with 64.
    rewrite HSH in Ha. exact Ha. }
  apply K4; [exact Hz | exact (NFZ a Hz)].
Qed.
Lemma c0_zone_acall : forall cx fp k ly3 S3 W3 memc md W2 mem2 slo (Er : Z -> Prop),
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 memc md k ->
  frames S3 = [(GB_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  c0_newblk cx ly3 S3 Er ->
  acall_kept SEGS B ly3 S3 W3 memc W2 mem2 slo (c_sp1 cx) Er ->
  forall a, c0_zone cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) memc a.
Proof.
intros cx fp k ly3 S3 W3 memc md W2 mem2 slo Er HB HJ HFR Hsub HNB (K1 & K2 & _ & K4 & _).
apply (c0_zone_blocks cx fp k ly3 S3 W3 memc md Er _ HB HJ HFR Hsub HNB).
- intros a Ha Hs. apply K1; [lia | lia].
- intros b m i Hb Hi He. apply (K2 b m i Hb Hi He).
- intros a Hz He. apply (K4 GB_CID fp a); [rewrite HFR; left; reflexivity | exact Hz | exact He].
Qed.

Lemma c0_last_split : forall (l l1 l2 : list (Z * Z)) x, l ++ [x] = l1 ++ x :: l2 -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
intros l l1 l2 x E Hn. destruct l2 as [|y l2'].
- split; [|reflexivity]. symmetry. exact (proj1 (app_inj_tail l l1 x x E)).
- exfalso. assert (Hne : y :: l2' <> []) by discriminate.
  destruct (exists_last Hne) as (l2'' & z & Ez). rewrite Ez in E.
  rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as (E1 & E2). subst z.
  apply Hn. rewrite E1. apply in_or_app. right. left. reflexivity.
Qed.

Lemma c0_body : forall i cx fp pc W ms r bs, c0_ms cx fp pc ms -> c0_mf i cx fp W ms r bs -> gb_body cx fp pc W ms GSH_it.
Proof.
intros i cx fp pc W ms r bs (H1 & H2 & H3 & H4 & H5 & H6 & H7) (M1 & M2 & M3 & M4 & M5 & _).
unfold gb_body. do 9 (split; [assumption|]). split; [reflexivity|]. split; [assumption|]. split; assumption.
Qed.
Lemma c0_ms_mkst : forall cx fp pc (regs regs0 : bvmap 5 word) mem pcv,
  gregs cx fp (mkst regs0 pcv mem (seg_rom SEGS)) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs r = getr regs0 r) ->
  c0_ms cx fp pc (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof.
intros cx fp pc regs regs0 mem pcv (G2 & G8 & G9 & G3 & G4 & G18 & G24) KP. cbn [ms_regs mkst] in *.
unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. unfold gregs. cbn [ms_regs mkst].
split; [rewrite KP; [exact G2 | c0_cs]|]. split; [rewrite KP; [exact G8 | c0_cs]|]. split; [rewrite KP; [exact G9 | c0_cs]|]. split; [rewrite KP; [exact G3 | c0_cs]|]. split; [rewrite KP; [exact G4 | c0_cs]|]. split; [rewrite KP; [exact G18 | c0_cs]|]. rewrite KP; [exact G24 | c0_cs].
Qed.
Lemma c0_gregs_mkst : forall cx fp (ms : machine_state) pcv mem, gregs cx fp ms -> gregs cx fp (mkst (ms_regs ms) pcv mem (seg_rom SEGS)).
Proof. intros cx fp ms pcv mem H. exact H. Qed.

Lemma c0_ms_mkst21 : forall cx fp pc (regs regs0 : bvmap 5 word) mem pcv,
  gregs cx fp (mkst regs0 pcv mem (seg_rom SEGS)) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 21 -> getr regs r = getr regs0 r) ->
  c0_ms cx fp pc (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof.
intros cx fp pc regs regs0 mem pcv HG KP. apply (c0_ms_mkst cx fp pc regs regs mem (Z_to_bv 64 0)); [|intros; reflexivity].
destruct HG as (G2 & G8 & G9 & G3 & G4 & G18 & G24). cbn [ms_regs mkst] in *. unfold gregs. cbn [ms_regs mkst].
split; [rewrite KP; [exact G2 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G8 | c0_cs | c0_cs]|].
split; [rewrite KP; [exact G9 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G3 | c0_cs | c0_cs]|].
split; [rewrite KP; [exact G4 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G18 | c0_cs | c0_cs]|].
rewrite KP; [exact G24 | c0_cs | c0_cs].
Qed.

Definition c0_csl : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition c0_csl21 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma c0_cs_in : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r c0_csl.
Proof.
intros r H. rewrite <- (Z_to_bv_bv_unsigned _ r). unfold acallee_saved in H.
assert (Hc : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/
  bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; cbn [c0_csl In]; repeat (first [left; apply bv_eq; reflexivity | right])|]).
rewrite Hc; cbn [c0_csl In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma c0_cs_in21 : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 21 -> In r c0_csl21.
Proof.
intros r H H21. rewrite <- (Z_to_bv_bv_unsigned _ r). unfold acallee_saved in H.
assert (Hc : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 22 \/
  bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; cbn [c0_csl21 In]; repeat (first [left; apply bv_eq; reflexivity | right])|]).
rewrite Hc; cbn [c0_csl21 In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

End d.

End c.
End b.
End a.

(* The phase files call these helpers with the Section's B, MT inferred and LAWS given. *)
Arguments c0_sp {rc PI B MT} cx _.
Arguments c0_nev {rc SK PI B MT} cx fp k ly3 S3 W3 mem md _ _ _.
Arguments c0_blk_twice {rc PI B} LAWS ly S W mem md l1 l2 l3 x _ _ _.
Arguments c0_achain0 {rc PI B MT} cx rd' sp' _ _ _ _ _.
Arguments c0_achain {fx rc SK PI B MT} cx fp k ly3 S3 W3 mem md sp' _ _ _ _.
Arguments c0_budget {MT} i nn acc _ _ _ _.
Arguments c0_mf_keep {rc PI B MT} i cx fp W ms ms' r bs _ _ _.
Arguments c0_mf_keep2 {rc PI B MT} i cx fp W W' ms ms' r bs _ _ _.
Arguments c0_geo {rc SK PI B MT} LAWS cx fp k ly3 S3 W3 mem md _ _ _.
Arguments c0_zone_blocks {rc SK PI B MT} LAWS cx fp k ly3 S3 W3 memc md Er Kf _ _ _ _ _ _ _ _ a _.
Arguments c0_zone_acall {rc SK PI B MT} LAWS cx fp k ly3 S3 W3 memc md W2 mem2 slo Er _ _ _ _ _ _ a _.
