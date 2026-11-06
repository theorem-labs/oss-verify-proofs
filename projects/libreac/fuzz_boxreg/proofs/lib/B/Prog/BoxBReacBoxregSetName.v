(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue_defect.v, with its module paths and module names changed; 637 of its 708 lines of code are new or changed and 584 lines of the source are left out. *)
(* reac_boxreg_set_name (fuzz_boxreg.asan-ubsan 0x8229c, 47 instructions): the contract of the ASan+UBSan build's code.
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; sd ra,8(sp)) and returns at once when
   idx < 0 (bltz a1). It then checks r for UBSan: r = NULL (beqz a0) and r not 4-byte aligned (andi a2,a0,3; bnez)
   branch to the trap `unimp` at 0x82340; both are refuted by the allocator's block law (a block's address is a
   multiple of 16 and at least 4096). It loads n, the 4-byte word at r + 280, after checking that word's shadow byte
   (the report path, __asan_report_load4, is refuted by the block's shadow, which AR's shadow law gives for the
   288-byte block r), and returns when idx >= n (bge, signed). Two more UBSan checks branch to the same trap: idx >= 5
   as unsigned (bgeu, the bound of the 5 rows), refuted by idx < n and Pau's boxreg_B1 (n <= 5); and the pointer
   overflow of r + 56 * idx (not a2,a0; bltu a2,a4), refuted because the block lies below the allocator's ceiling.
   Otherwise it sets
   a0 = r + 56 * idx + 24 (the name field of row idx), a1 = 32, a2 = "%s" (A_OBJ 10, 0x20d40), a3 = name or, when name
   is NULL, "" (A_OBJ 11, 0x20d60), restores ra, pops its frame and TAIL-calls snprintf (`j 0x41490`,
   __interceptor_trampoline_snprintf; the listing's PTail BB___interceptor_trampoline_snprintf).
   The tail call: at the call its own frame is gone (sp is the entry sp, ra the caller's), so the stack it needs is the
   snprintf wrapper's 2 * ESTACK (lib/B/Rt/SnprintfDefB.v absnprintf_realizes, taken at
   pa_sigma BB___interceptor_trampoline_snprintf; its own 16-byte frame lies inside that window), and its post is the
   snprintf post at the caller's return address: the struct's name field holds firstn 31 name ++ [0], every other byte
   of the struct and every byte outside the window are kept, callee-saved registers are kept, and the FP state is the
   wrapper's fx' (apost_baseF: f registers equal except f10, fcsr the entry's or rounding mode 0; the two early
   returns never reach the wrapper and take fx' := fx). a0 is not stated: the function returns void.
   Hazards: the registry struct is 288 bytes (rows 0..280, n at +280, fabric at +284); the name field
   r + 56 * idx + 24 .. + 56 lies inside it only for idx <= 4, which comes from idx < n and boxreg_B1 (0 <= n <= 5);
   the name string must be NUL-terminated, with the rest of its NUL's 8-byte word readable (musl's memchr word loop
   under strnlen), outside the struct and the window, and its shadow addressable (the wrapper's printf_common check);
   the four UBSan traps above. The function makes no call before the tail call and writes only its own frame, so
   the name premises, stated at entry, hold at the call; a caller re-derives them at its own call (for a heap name:
   the block's bytes, which journals keep, AR's shadow law, and absn_blk_tail_vis of lib/B/Rt/SnprintfDefB.v).
   The image's "%s" (A_OBJ 10, 0x20d40) and "" (A_OBJ 11, 0x20d60) and the read-only image the wrapper reads
   (absn_rom_kept, lib/B/Rt/SnprintfDefB.v) are stated by facts that hold in every state, so that a caller has them
   at its call after any earlier call (an ajournal keeps no shadow byte of the image, lib/Reusable/YCbq.v:358, and
   keeps an image byte only when it is neither an owned static nor an errno byte, :362):
   - absn_rom_kept: arodata_okP on the read-only segments; arodata_okP is carried by every journal
     (lib/A/Prog/BoxBase.v arodata_ok_journalP);
   - their bytes: absn_rom_bytes / absn_rom_str (state-free: read-only image bytes that are no owned static and no
     errno byte, read through absn_rom_kept; the rest of "" 's 8-byte word may be owned and is read through aview's
     image fallback, `seg_rom ... <> None`);
   - their shadow: globs_marked G with In (q, sz) G (range_addressable) and img_shadow_vis with the 64-byte margins
     (shadow_hull_vis), lib/A/Prog/BoxRo.v ro_read_ok_glob; both hold in every AR state;
   - 0 < q, amem_range, apart from the window and from the destination: from the margins, alloc_ceiling below the
     stack, and AR_client_img_law (a heap byte is no image byte).
   Image difference: the asan build (lib/A/Prog/ReacBoxregSetName.v) has no UBSan checks; the stored bytes are the same.
   The memory model is Pau's plain one, used as it is: lib/Prog/Boxreg.v (bx_n, boxreg_B1) and the post of
   lib/Prog/reac_boxreg_set_name_c.v (pf_bytes (firstn 31 s ++ [0]) at r + 56 * idx + 24 when 0 <= idx < bx_n bs,
   nothing otherwise), written into the struct's bytes with lib/Lib/Mem.v upd_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
(* The walk layer (lib/B/Prog/BoxBPaLib.v, lib/A/Prog/YC4b.v, lib/B/Prog/YC85.v), imported before the spec's own
   modules so that every name the spec text uses resolves as it does without the walk. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC85.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The struct's 288 bytes after the call (REG_SIZEB: lib/B/Prog/BoxBReacBoxregInit.v): unchanged when idx < 0 or
   idx >= n, else the name field of row idx holds Pau's pf_bytes (firstn 31 s ++ [0]). *)
Definition tbreac_boxreg_set_name_bytes (bs : list byte) (idx : Z) (s : list Z) : list byte :=
if (idx <? 0) || (Boxreg.bx_n bs <=? idx) then bs
else Lib.Mem.upd_bytes bs (Z.to_nat (56 * idx + 24)) (printf_facts_c.pf_bytes (firstn 31 s ++ [0])).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: the snprintf wrapper's 2 * ESTACK, taken at the entry
   sp because the tail call is made after the function pops its 16-byte frame. *)
Definition AB_reac_boxreg_set_nameP : Z := BASE + AF_reac_boxreg_set_name.
Definition REAC_BOXREG_SET_NAME_STKB : Z := 2 * ESTACK.
(* The name argument q: NULL (the call prints ""), or the NUL-terminated string s at q, with the rest of its NUL's
   8-byte word readable, outside the window below sp and outside the struct r, its shadow addressable (Pau's name_ok,
   lib/Prog/reac_boxreg_set_name_c.v, over the ASan view). *)
Definition tbreac_boxreg_set_name_name_ok (W : world SEGS) (mem : word -> option byte) (sp r q : Z) (s : list Z)
  : Prop :=
(q = 0 /\ s = []) \/
(0 < q /\ Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
 (forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) mem (q + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
 (forall a, q + Z.of_nat (length s) < a < absn_word_end q (Z.of_nat (length s)) -> aview SEGS (w_H W) mem a <> None) /\
 amem_range q (Z.of_nat (length s) + 8) /\
 (forall a, q <= a < absn_word_end q (Z.of_nat (length s)) -> ~ (sp - REAC_BOXREG_SET_NAME_STKB <= a < sp)) /\
 (absn_word_end q (Z.of_nat (length s)) <= r \/ r + REG_SIZEB <= q) /\
 range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q (Z.of_nat (length s) + 1) /\
 shadow_hull_vis (aview SEGS (w_H W) mem) q (Z.of_nat (length s) + 1)).
Section h.
Variable B : asyms.
Definition tbreac_boxreg_set_name_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r idx : Z) (bs : list byte)
  (s : list Z) : world SEGS -> config -> Prop :=
apost_baseF SEGS B REAC_BOXREG_SET_NAME_STKB [(r, r + REG_SIZEB)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W') mem' (r + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (tbreac_boxreg_set_name_bytes bs idx s) (Z_to_bv 8 0))))).
Definition tbreac_boxreg_set_name_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r idx q : Z) (bs : list byte) (s : list Z) (G : list (Z * Z)),
afn_pre SEGS B REAC_BOXREG_SET_NAME_STKB ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 idx -> getr regs 12 = w64 q -> -2 ^ 31 <= idx < 2 ^ 31 ->
(* the registry struct: a heap block holding bs *)
In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
(* the name *)
tbreac_boxreg_set_name_name_ok W mem (spZ regs) r q s ->
(* facts of the image and of the runtime's symbols, true in every state *)
img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the image's "%s" (A_OBJ 10) and "" (A_OBJ 11): bytes of the read-only image, registered globals *)
absn_rom_bytes SEGS B (VAL (A_OBJ 10)) ABSN_FMT -> In (VAL (A_OBJ 10), 3) G ->
IMG_LO + 64 <= VAL (A_OBJ 10) -> VAL (A_OBJ 10) + 3 + 64 <= IMG_HI ->
(* R2 (a Theorem Labs lane 15:05Z): the format below image B's GOT canary slot, which the snprintf contract now asks (P2) *)
VAL (A_OBJ 10) + 3 <= 0x99f60 ->
absn_rom_str SEGS B (VAL (A_OBJ 11)) [] -> In (VAL (A_OBJ 11), 1) G ->
IMG_LO + 64 <= VAL (A_OBJ 11) -> VAL (A_OBJ 11) + 1 + 64 <= IMG_HI ->
(* the rounding mode at entry, which this function hands to the snprintf wrapper (SnprintfDefB.v) *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (cfg_at SEGS AB_reac_boxreg_set_nameP regs mem md)
(tbreac_boxreg_set_name_post regs ly S W mem md r idx bs s).
(* ---- The walk ------------------------------------------------------------------------------------------------------
   The engine runs the code from the entry to each stop: bltz idx (0x822a4), bge idx, n (0x822dc), bltu ~r, 56 * idx
   (0x822f8), bnez name (0x82310), the tail call (0x82330) and the return (0x8233c). It decides by itself the UBSan
   checks of r (beqz, andi/bnez: r >= 4096 and r mod 16 = 0 are atom 10's facts) and of idx (bgeu idx, 5, once atom 11
   lies in 0 .. 4), and the shadow check of the word r + 280 (the engine's shadow token: the word's granule lies inside
   the block's shadow entry sn_SH, so the __asan_report_load4 path at 0x82350 is not taken). n, the word at r + 280, is
   atom 33, a chunk of the block region sn_RN; its value is bx_n bs (sn_n_byte). The overflow trap (bltu) is refuted
   from the block lying below the allocator's ceiling. The tail call is sn_tail, the one place that uses the snprintf
   contract. *)
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASNPRINTF : absnprintf_realizes SEGS B (SIGMA BB___interceptor_trampoline_snprintf).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
Definition SBsn : Z := 0x7fff8000.
Definition CBsn : sv := SOff 32 0.
Definition Bspan_sn : Z * Z := (SBsn, SBsn + 2 ^ 44 - 1).
Definition sn_RN : YP09.region := YP09.mkRegion (Some 10%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition sn_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF SBsn SBsn 0);
(33%nat, mkAF 0 5 0)] [] [].
Definition sn_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32; sn_RN].
Definition ss_sn : sstate := mkSS AF_reac_boxreg_set_name sr_atoms sn_regions None sn_facts.
Definition sn_SH : list shent := [mkSHE 10 0 288].
Definition Esn (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs [Z_to_bv 64 SBsn; Z_to_bv 64 n]).
Lemma sn_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hc.
Qed.
Lemma sn_swrap : forall z, 0 <= z < 2 ^ 32 -> 0 <= bv_swrap 32 z -> bv_swrap 32 z = z.
Proof.
intros z Hz Hs. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. cbn [Z.of_N] in *.
change (2 ^ 32) with 4294967296 in *. change (4294967296 / 2) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
(* The bytes of n: bx_n bs is the signed 32-bit word at 280 .. 283 of bs, here 0 .. 5. *)
Lemma sn_n_byte : forall bs : list byte, length bs = 288%nat -> 0 <= Boxreg.bx_n bs -> forall k, (k < 4)%nat ->
nth (280 + k) bs (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr (Boxreg.bx_n bs mod 2 ^ (8 * Z.of_nat 4)) (8 * Z.of_nat k) mod 256).
Proof.
intros bs Hlen Hn k Hk.
assert (Hnth : nth (280 + k) bs (Z_to_bv 8 0) = nth k (skipn 280 bs) (Z_to_bv 8 0)).
{ rewrite <- (firstn_skipn 280 bs) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. f_equal. lia. }
rewrite Hnth. clear Hnth.
unfold Boxreg.bx_n, Boxreg.rd4, Boxreg.bsub in *.
change (Z.to_nat 280) with 280%nat in *. change (Z.to_nat 4) with 4%nat in *.
assert (Hsk : length (skipn 280 bs) = 8%nat) by (rewrite length_skipn; lia).
revert Hn Hsk. destruct (skipn 280 bs) as [|b0 [|b1 [|b2 [|b3 t]]]]; cbn [length]; intros Hn Hsk; try lia.
cbn [firstn] in *.
lazymatch goal with |- context [bv_swrap 32 ?t] => set (v := t) in * end.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
assert (Hv : v = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
{ clear Hn. subst v. rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
  change (firstn 0 t) with (@nil byte).
  cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val]. ring. }
clearbody v.
assert (Hv0 : 0 <= v < 2 ^ 32) by (clear Hn; lia).
assert (Hsw : bv_swrap 32 v = v) by (apply sn_swrap; [exact Hv0 | exact Hn]).
clear Hn.
rewrite Hsw. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small v) by lia.
rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth]; apply bv_eq; rewrite Z_to_bv_unsigned;
unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; rewrite Hv.
- change (2 ^ (8 * Z.of_nat 0)) with 1. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 2)) with 65536. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.
Lemma sn_nth_upd : forall (cs l : list byte) k i d, (k + length l <= length cs)%nat -> (i < length cs)%nat ->
nth i (Lib.Mem.upd_bytes cs k l) d =
if (Nat.leb k i && Nat.ltb i (k + length l))%bool then nth (i - k) l d else nth i cs d.
Proof.
intros cs l k i d H1 H2.
pose proof (Lib.Mem.upd_bytes_nth cs k l i H1 H2) as E.
rewrite (nth_error_nth' _ d) in E by (rewrite Lib.Mem.upd_bytes_length; lia).
destruct (Nat.leb k i && Nat.ltb i (k + length l))%bool eqn:C.
- apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
  rewrite (nth_error_nth' _ d) in E by lia. injection E as E. exact E.
- rewrite (nth_error_nth' _ d) in E by lia. injection E as E. exact E.
Qed.
Lemma sn_nth_lt : forall (l : list Z) j, Forall (fun c => 0 <= c < 256) l -> 0 <= nth j l 0 < 256.
Proof.
induction l as [|c l IH]; intros j H; destruct j as [|j]; cbn [nth]; try lia; inversion H; subst; [lia | apply IH; assumption].
Qed.
Lemma sn_forall_firstn : forall n (l : list Z) (P : Z -> Prop), Forall P l -> Forall P (firstn n l).
Proof.
induction n as [|n IH]; intros l P H; [constructor|]. destruct l as [|c l]; cbn [firstn]; [constructor|].
inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.
Lemma sn_hi : forall x i, 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof. intros x i Hx Hi. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.
Lemma sn_lxor : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
assert (L : Z.ldiff x (Z.ones 64) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. cbn [negb]. apply andb_false_r.
  - rewrite (sn_hi x i Hx) by lia. reflexivity. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x L).
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (sn_hi x i Hx) by lia. reflexivity.
Qed.
(* The values the walk meets: ~r (not a2,a0), 56 * idx (slli/slli/sub), the destination r + 56 * idx + 24. *)
Lemma sn_U_not : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite sn_lxor by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.
Lemma sn_U_mul : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 4 -> U E (SMd M_MUL (SOff n 0) (SLit 56)) = 56 * v.
Proof.
intros E n v Hn Hv. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n v Hn) by lia. rewrite U_SLit.
change (zcanon 56) with 56. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma sn_U_dst : forall E r idx, ew E 10 = Z_to_bv 64 r -> ew E 11 = Z_to_bv 64 idx -> 0 <= r < 2 ^ 48 -> 0 <= idx <= 4 ->
U E (SAlu ALU_ADD (SOff 10 24) (SMd M_MUL (SOff 11 0) (SLit 56))) = r + 56 * idx + 24.
Proof.
intros E r idx H10 H11 Hr Hi. rewrite U_SAlu. cbn [zalu_raw]. rewrite (sn_U_mul E 11 idx H11 Hi), U_SOff, H10.
rewrite unsigned_lit_small by lia. rewrite (zcanon_id (r + 24)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma sn_br_lt0 : forall E n v, ew E n = Z_to_bv 64 v -> -2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. cbn [branch_taken].
apply Boxreg.lts_lit; lia.
Qed.
Lemma sn_br_ge : forall E n m v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
-2 ^ 63 <= v < 2 ^ 63 -> -2 ^ 63 <= w < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = negb (v <? w).
Proof.
intros E n m v w Hn Hm Hv Hw. cbn [sv_denot]. rewrite Hn, Hm, !Z.add_0_r, !Z_to_bv_bv_unsigned. cbn [branch_taken].
rewrite Boxreg.lts_lit by lia. reflexivity.
Qed.
Lemma sn_rom_kept : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> absn_rom_kept SEGS B W mem.
Proof.
intros W mem HRO a Ha Ho He. unfold arodata_okP in HRO.
apply HRO; [unfold in_roP; left; exact Ha | exact Ho | exact He].
Qed.
(* A byte the image carries reads as Some in every state: aview falls back to the image byte where memory holds
   none (lib/Reusable/YP09.v mbyte), and the image's bytes are never hidden (YA0o.v seg_rom_hidden). So the tail of
   the empty string's NUL word is readable whether or not it is a runtime-owned static. *)
Lemma sn_aview_rom : forall (W : world SEGS) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None ->
  aview SEGS (w_H W) mem a <> None.
Proof.
intros W mem a Hr. unfold aview, mbyte, mrestrict. cbv beta.
destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
- exfalso. apply Hr. eapply seg_rom_hidden; [exact (w_Hoff W) | exact EH].
- destruct (mem (Z_to_bv 64 a)) as [b|]; [cbv beta iota delta [option_map]; discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; [cbv beta iota delta [option_map]; discriminate | exfalso; exact (Hr eq_refl)].
Qed.
(* The shadow entry of the block: its 288 bytes are addressable and lie apart from the shadow band. *)
Lemma sn_shent : forall ly S (W : world SEGS) mem md Ex (q b sz lo hi : Z) (n : nat),
AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
U Ex CBsn = SHADOW_OFF -> U Ex (SOff n 0) = q ->
b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
shent_ok SEGS CBsn Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md Ex q b sz lo hi n HAR Hin HB Hq Hlo Hlh Hhi.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
rewrite <- (aview_rd_of SEGS). split.
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
- intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
  revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.
Lemma sn_entry : forall ly S W (regs : bvmap 5 word) mem md ch r (bs : list byte),
afn_pre SEGS B REAC_BOXREG_SET_NAME_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
st_ok_pi SEGS VAL (Esn regs (Boxreg.bx_n bs)) ss_sn
  (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_reac_boxreg_set_nameP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBsn sn_SH (Esn regs (Boxreg.bx_n bs)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r bs HPRE H10 Hin Hlen HBS HB1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STKB = 8192) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *. assert (Hsz : REG_SIZEB = 288) by reflexivity.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Hrimg. change (req_size REG_SIZEB) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'.
rewrite restrict_mkst_fx.
set (E := Esn regs (Boxreg.bx_n bs)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)]) n)
  by (intros n Hn; subst E; unfold Esn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBsn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold Esn; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold Esn; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_sn, AB_reac_boxreg_set_nameP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sn_regions, stack_region, got_regionP, bcell_regionP, sn_RN.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBsn SBsn);
      [cbn [sv_denot CBsn]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBsn; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (Boxreg.bx_n bs));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      intros k Hk. change (N.to_nat 4) with 4%nat in Hk.
      pose proof (HBS (280 + Z.of_nat k) ltac:(lia)) as Hb.
      replace (r + (280 + Z.of_nat k)) with (r + 280 + Z.of_nat k) in Hb by lia.
      unfold aview in Hb. cbv beta in Hb.
      destruct (mbyte SEGS (mrestrict (w_H W) mem) (r + 280 + Z.of_nat k)) as [b|] eqn:Hm; [|discriminate Hb].
      cbn [option_map] in Hb. injection Hb as Hb.
      assert (Hbe : b = nth (Z.to_nat (280 + Z.of_nat k)) bs (Z_to_bv 8 0)) by (apply bv_eq; exact Hb).
      rewrite Hbe. replace (Z.to_nat (280 + Z.of_nat k)) with (280 + k)%nat by lia.
      f_equal. exact (sn_n_byte bs Hlen ltac:(lia) k Hk).
  + apply pairwise_disjoint_of_extents.
    unfold sn_regions, stack_region, got_regionP, bcell_regionP, sn_RN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hrceil Hr4096 Hrimg. clear. intros.
    repeat split; lia.
  + split; [|split; exact I].
    cbn [sn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SBsn; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil HB1'.
    clear. unfold SBsn. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, sn_SH. apply Forall_cons; [|apply Forall_nil].
  apply (sn_shent ly S W mem md E r r REG_SIZEB 0 288 10 HAR Hin).
  + unfold CBsn. rewrite (U_atom E 32 SBsn E32) by (unfold SBsn; lia). reflexivity.
  + apply (U_atom E 10 r E10). lia.
  + lia.
  + lia.
  + change (req_size REG_SIZEB) with 288. lia.
Qed.
(* The tail call: at 0x82330 the frame is popped (sp is the entry sp, ra the caller's) and the registers hold the
   destination r + 56 * idx + 24, the size 32, "%s" and the string x; the snprintf contract's post, at the caller's
   return address, is the function's post. The image's "%s" is read through absn_rom_kept (arodata_okP at entry and
   the frame lying outside the image) and its shadow through globs_marked / img_shadow_vis in the state at the call;
   the string's facts at entry carry over the frame's writes. *)
Lemma sn_tail : forall ly S W (regs : bvmap 5 word) mem md ch (r idx x : Z) (bs : list byte) (s : list Z)
  (G : list (Z * Z)) (regsT : bvmap 5 word) memT mdT,
afn_pre SEGS B REAC_BOXREG_SET_NAME_STKB ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
ajournal SEGS B REAC_BOXREG_SET_NAME_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W memT mdT 0 ->
getr regsT 10 = w64 (r + 56 * idx + 24) -> getr regsT 11 = w64 32 -> getr regsT 12 = w64 (VAL (A_OBJ 10)) ->
getr regsT 13 = w64 x -> getr regsT 1 = getr regs 1 -> spZ regsT = spZ regs ->
getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 -> aregs_preserved regs regsT ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a) ->
In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
0 <= idx < Boxreg.bx_n bs -> Boxreg.boxreg_B1 bs ->
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 -> 0 < x ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) mem (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
(forall a, x + Z.of_nat (length s) < a < absn_word_end x (Z.of_nat (length s)) -> aview SEGS (w_H W) mem a <> None) ->
amem_range x (Z.of_nat (length s) + 8) ->
(forall a, x <= a < absn_word_end x (Z.of_nat (length s)) -> ~ (spZ regs - REAC_BOXREG_SET_NAME_STKB <= a < spZ regs)) ->
(absn_word_end x (Z.of_nat (length s)) <= r \/ r + REG_SIZEB <= x) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x (Z.of_nat (length s) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) x (Z.of_nat (length s) + 1) ->
img_shadow_vis SEGS B -> globs_marked SEGS B G ->
absn_rom_bytes SEGS B (VAL (A_OBJ 10)) ABSN_FMT -> In (VAL (A_OBJ 10), 3) G ->
IMG_LO + 64 <= VAL (A_OBJ 10) -> VAL (A_OBJ 10) + 3 + 64 <= IMG_HI ->
(* R2: the format below image B's GOT canary slot (the contract's P2), from the spec's premise *)
VAL (A_OBJ 10) + 3 <= 0x99f60 ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
(tbreac_boxreg_set_name_post regs ly S W mem md r idx bs s).
Proof.
intros ly S W regs mem md ch r idx x bs s G regsT memT mdT HPRE HRO HJ R10 R11 R12 R13 R1 Rsp R3 R4 HPR KEEP Hin Hlen
  HBS Hidx HB1 Hsc Hsl Hx0 Hx Hxw Hxm Hxwin Hxd Hxra Hxhv HISV HGM HFS HFG HFlo HFhi HFcan HFRM.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STKB = 8192) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Hrimg. change (req_size REG_SIZEB) with 288 in Hrimg.
assert (Hsz : REG_SIZEB = 288) by reflexivity.
pose proof HJ as (HART & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
unfold IMG_HI in HFhi.
assert (HWE : x + Z.of_nat (length s) < absn_word_end x (Z.of_nat (length s)) <= x + Z.of_nat (length s) + 8)
  by (unfold absn_word_end; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)); lia).
assert (Hxm' : x + Z.of_nat (length s) + 1 <= 2 ^ 47) by (unfold amem_range in Hxm; lia).
(* What the frame's writes leave: the read-only image, the string. *)
assert (HROT : absn_rom_kept SEGS B W memT).
{ intros a Ha Ho He. pose proof Ha as (sg & Hsg & _ & Hab).
  assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | lia]).
  pose proof (pa_img_range a Himg) as Hia.
  rewrite KEEP by lia. exact (sn_rom_kept W mem HRO a Ha Ho He). }
assert (KX : forall a, x <= a < absn_word_end x (Z.of_nat (length s)) ->
  aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP; [lia|]. intros Hw. apply (Hxwin a Ha). lia. }
(* "%s": its bytes through absn_rom_kept, its shadow from the registered global in the state at the call. *)
assert (HFB : forall i, 0 <= i < 3 -> aview SEGS (w_H W) memT (VAL (A_OBJ 10) + i) = Some (nth (Z.to_nat i) ABSN_FMT 0)).
{ intros i Hi. destruct (HFS i ltac:(unfold ABSN_FMT; cbn; lia)) as (Hr & Ho & He & Hv).
  rewrite (HROT _ Hr Ho He). exact Hv. }
destruct (ro_read_ok_glob SEGS B G ly S W memT mdT (VAL (A_OBJ 10)) 3 (VAL (A_OBJ 10)) 3 HGM HFG HISV HART
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HFra HFhv].
change (SRr SEGS W (cfg_at SEGS (SIGMA BB___interceptor_trampoline_snprintf) regsT memT mdT)
  (tbreac_boxreg_set_name_post regs ly S W mem md r idx bs s)).
eapply SRr_mono.
{ apply (ASNPRINTF ly S W regsT memT mdT (r + 56 * idx + 24) 32 (VAL (A_OBJ 10)) x s r REG_SIZEB).
  - eapply ecall_pre_at with (STK := REAC_BOXREG_SET_NAME_STKB) (sp0 := spZ regs) (FP := [(r, r + REG_SIZEB)])
      (ly := ly) (S := S) (W0 := W) (mem := mem) (md := md) (own := []) (k := 0) (o := 0);
    first [exact HJ | (rewrite Rsp; lia) | reflexivity | lia | (rewrite R1; exact Hra) | (rewrite R3; exact Hgp)
          | (rewrite R4; exact Htp) | exact LAWS | exact pa_segs_low].
  - rewrite Rsp. lia.
  - intros a Ha. apply HpresJ. rewrite Rsp in Ha. lia.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - lia.
  - exact Hin.
  - lia.
  - lia.
  - intros a Ha Hw. rewrite Rsp in Hw. lia.
  - exact HFB.
  - lia.
  - unfold amem_range. left. lia.
  - lia.
  - exact HFcan.
  - intros a Ha Hw. rewrite Rsp in Hw. lia.
  - destruct Hrimg as [Hl | Hl]; [right | left]; lia.
  - exact HFra.
  - exact HFhv.
  - exact Hsc.
  - exact Hsl.
  - exact Hx0.
  - intros i Hi. rewrite (KX (x + i)) by lia. exact (Hx i Hi).
  - intros a Ha. rewrite (KX a) by lia. exact (Hxw a Ha).
  - exact Hxm.
  - intros a Ha. rewrite Rsp. exact (Hxwin a Ha).
  - destruct Hxd as [Hl | Hl]; [left | right]; lia.
  - eapply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 16) (spZ regs));
    [exact KEEP | lia | lia | lia | exact Hxra].
  - eapply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 16) (spZ regs));
    [exact KEEP | lia | lia | lia | lia | exact Hxhv].
  - exact HROT.
  - exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & -> & HFR & HFC & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
assert (HAO : absn_out 32 s = firstn 31 s ++ [0]) by reflexivity.
rewrite HAO in Heff, Hfr.
assert (HL31 : (length (firstn 31 s) <= 31)%nat) by (rewrite length_firstn; lia).
assert (HLl : Z.of_nat (length (firstn 31 s ++ [0])) = Z.of_nat (length (firstn 31 s)) + 1)
  by (rewrite length_app; cbn [length]; lia).
rewrite HLl in Heff, Hfr.
unfold tbreac_boxreg_set_name_post, apost_baseF.
exists fx2, ly, S, regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite R1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HFR|]. split; [right; exact HFC|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low REAC_BOXREG_SET_NAME_STKB (spZ regs) [(r, r + REG_SIZEB)]
    ly S W mem md [] ly S W memT mdT 0 mem2 md2
    (fun a => (r + 56 * idx + 24 <= a < r + 56 * idx + 24 + (Z.of_nat (length (firstn 31 s)) + 1))
      \/ (spZ regs - 2 * ESTACK <= a < spZ regs)) S [] HJ).
  - intros a Ha Hna. rewrite Rsp in Hfr. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left.
    + right; left; split.
      * exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; lia].
      * exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia].
    + left. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
split; [exact (aregs_preserved_trans _ _ _ HPR HP)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
intros i Hi. rewrite Hsz in Hi.
unfold tbreac_boxreg_set_name_bytes.
replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with false
  by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
assert (HLp : length (printf_facts_c.pf_bytes (firstn 31 s ++ [0])) = (length (firstn 31 s) + 1)%nat)
  by (unfold printf_facts_c.pf_bytes; rewrite length_map, length_app; reflexivity).
rewrite sn_nth_upd by (rewrite ?HLp; lia).
rewrite HLp.
lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:Hc end.
- apply andb_prop in Hc as [Hc1 Hc2]. apply Nat.leb_le in Hc1. apply Nat.ltb_lt in Hc2.
  unfold printf_facts_c.pf_bytes. rewrite (map_nth (Z_to_bv 8) (firstn 31 s ++ [0]) 0).
  replace (r + i) with (r + 56 * idx + 24 + (i - (56 * idx + 24))) by lia.
  rewrite (Heff (i - (56 * idx + 24))) by lia.
  replace (Z.to_nat (i - (56 * idx + 24))) with (Z.to_nat i - Z.to_nat (56 * idx + 24))%nat by lia.
  rewrite sn_u8; [reflexivity|].
  apply sn_nth_lt. apply Forall_app. split.
  + apply sn_forall_firstn. eapply Forall_impl; [|exact Hsc]. cbn beta. intros c Hc. lia.
  + constructor; [lia | constructor].
- apply andb_false_iff in Hc.
  assert (Hout : ~ (r + 56 * idx + 24 <= r + i < r + 56 * idx + 24 + (Z.of_nat (length (firstn 31 s)) + 1))).
  { destruct Hc as [Hc | Hc]; [apply Nat.leb_gt in Hc | apply Nat.ltb_ge in Hc]; lia. }
  rewrite (Hfr (r + i)); [| lia | exact Hout | rewrite Rsp; lia].
  rewrite (KEEP (r + i)) by lia. apply HBS. rewrite Hsz. exact Hi.
Qed.
Local Ltac sn_keep KP regs W mem0 Usp :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H W) ?m0) (mrestrict (w_H W) ?m1) |- _ =>
    let KP2 := fresh "KP" in
    assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
                  aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw; transitivity (aview SEGS (w_H W) m0 a); [| exact (KP a Ha Hw)];
      apply (kept_of_frame Ex rs (w_H W) m0 m1 (fun x => spZ regs - 16 <= x < spZ regs) HFr); [| exact Ha | exact Hw];
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
      let Hwin := fresh "Hwin" in let Hr := fresh "Hr" in
      intros bb wlo whi aa Hwin Hr; vm_compute in Hwin;
      destruct Hwin as [Hwin | [Hwin | [Hwin | [Hwin | []]]]]; injection Hwin as <- <- <-; cbn [base_val] in Hr;
      rewrite ?Usp in Hr; lia
    | clear KP HFr; rename KP2 into KP ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Local Ltac sn_reg HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh Ex ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
Theorem pbb_reac_boxreg_set_name : tbreac_boxreg_set_name_spec.
Proof.
unfold tbreac_boxreg_set_name_spec.
intros ly S W regs mem md ch r idx q bs s G HPRE HRO H10 H11 H12 Hidx Hin Hlen HBS HB1 HNM HISV HGM
  HFS HFG HFlo HFhi HFcan HES HEG HElo HEhi HFRM.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (sn_entry ly S W regs mem md ch r bs HPRE H10 Hin Hlen HBS HB1) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_SET_NAME_STKB [(r, r + REG_SIZEB)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STKB = 8192) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria. assert (Hsz : REG_SIZEB = 288) by reflexivity.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Hrimg. change (req_size REG_SIZEB) with 288 in Hrimg.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'.
unfold IMG_HI in HFhi, HEhi.
assert (Hq : 0 <= q < 2 ^ 47).
{ destruct HNM as [(-> & _) | (Hq0 & _ & _ & _ & _ & Hqm & _)]; [lia|]. unfold amem_range in Hqm. lia. }
remember (Esn regs (Boxreg.bx_n bs)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)]) n)
  by (intros n Hn; subst E; unfold Esn; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 idx)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E251 : ew E 251%nat = Z_to_bv 64 (VAL (A_OBJ 10)))
  by (change 251%nat with (A_OBJ 10); subst E; unfold Esn; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E 252%nat = Z_to_bv 64 (VAL (A_OBJ 11)))
  by (change 252%nat with (A_OBJ 11); subst E; unfold Esn; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
unfold cfg_at.
change (w64 AB_reac_boxreg_set_nameP) with (Z_to_bv 64 AB_reac_boxreg_set_nameP).
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
(* The frame, the save of ra, up to bltz idx. *)
paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
sn_keep KP regs W mem Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_sn.
- (* idx < 0: the reload of ra, the release of the frame and the return *)
  rewrite (sn_br_lt0 E 11 idx E11 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. rename Hc into Hneg.
  paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
  sn_keep KP regs W mem Usp.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) RR1;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold tbreac_boxreg_set_name_post, apost_baseF;
    exists fx, ly, S, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite RR1, E1, Hra; reflexivity|];
    split; [intros; reflexivity|]; split; [left; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)] HS);
            [exact HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
    intros i Hi; rewrite (KP (r + i)) by lia; rewrite HBS by exact Hi;
    unfold tbreac_boxreg_set_name_bytes;
    replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with true
      by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; lia);
    reflexivity
  end.
- (* idx >= 0 *)
  rewrite (sn_br_lt0 E 11 idx E11 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc. rename Hc into Hnn.
  assert (HF11 : afact_ok E 11 (mkAF 0 (2 ^ 31 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E11, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
  apply (st_ok_pi_add_fact E _ _ 11 _ HS) in HF11. clear HS. rename HF11 into HS.
  (* the UBSan checks of r, the shadow check and load of n, up to bge idx, n *)
  paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
  sn_keep KP regs W mem Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_sn.
  + (* n <= idx: the return *)
    rewrite (sn_br_ge E 11 33 idx (Boxreg.bx_n bs) E11 E33 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hge.
    paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
    sn_keep KP regs W mem Usp.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      prreg HS (1%bv : bv 5) RR1;
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros mat';
      unfold tbreac_boxreg_set_name_post, apost_baseF;
      exists fx, ly, S, (ms_regs msc), (ms_mem msc); eexists;
      split; [cbn [ms_regs]; rewrite RR1, E1, Hra; reflexivity|];
      split; [intros; reflexivity|]; split; [left; reflexivity|];
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)] HS);
              [exact HAE | vm_compute; reflexivity]|];
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
      intros i Hi; rewrite (KP (r + i)) by lia; rewrite HBS by exact Hi;
      unfold tbreac_boxreg_set_name_bytes;
      replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with true
        by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia);
      reflexivity
    end.
  + (* idx < n <= 5 *)
    rewrite (sn_br_ge E 11 33 idx (Boxreg.bx_n bs) E11 E33 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt.
    assert (HF11 : afact_ok E 11 (mkAF 0 4 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E11, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
    apply (st_ok_pi_add_fact E _ _ 11 _ HS) in HF11. clear HS. rename HF11 into HS.
    (* bgeu idx, 5 is decided; up to the overflow check bltu ~r, 56 * idx *)
    paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
    sn_keep KP regs W mem Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan_sn.
    * (* the overflow trap: ~r < 56 * idx is false *)
      exfalso. rewrite branch_ltu_U in Hc.
      rewrite (sn_U_not E 10 r E10), (sn_U_mul E 11 idx E11) in Hc by lia.
      apply Z.ltb_lt in Hc. lia.
    * (* the destination, up to bnez name *)
      clear Hc. paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
      sn_keep KP regs W mem Usp.
      psrr_branch_tok RUN BR HS SHOK Bspan_sn.
      -- (* name <> NULL: a3 = name *)
         rewrite branch_ne_U, U_SLit, (U_atom E 12 q E12) in Hc by lia. change (zcanon 0) with 0 in Hc.
         apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hqn.
         destruct HNM as [(Hq0 & _) | (Hqp & Hsc & Hsl & Hx & Hxw & Hxm & Hxwin & Hxd & Hxra & Hxhv)]; [lia|].
         paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
         sn_keep KP regs W mem Usp.
         pmkst HS.
         sn_reg HS (10%bv : bv 5) RR10. rewrite denot_lit_U, (sn_U_dst E r idx E10 E11) in RR10 by lia.
         sn_reg HS (11%bv : bv 5) RR11. cbn [sv_denot] in RR11.
         sn_reg HS (12%bv : bv 5) RR12. cbn [sv_denot] in RR12. rewrite E251, Z.add_0_r, Z_to_bv_bv_unsigned in RR12.
         sn_reg HS (13%bv : bv 5) RR13. cbn [sv_denot] in RR13. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned in RR13.
         sn_reg HS (1%bv : bv 5) RR1. cbn [sv_denot] in RR1. rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned in RR1.
         sn_reg HS (2%bv : bv 5) RR2. cbn [sv_denot] in RR2. rewrite E2, Z.add_0_r, Z_to_bv_bv_unsigned in RR2.
         sn_reg HS (3%bv : bv 5) RR3. cbn [sv_denot] in RR3. rewrite E3, Z.add_0_r, Z_to_bv_bv_unsigned in RR3.
         sn_reg HS (4%bv : bv 5) RR4. cbn [sv_denot] in RR4. rewrite E4, Z.add_0_r, Z_to_bv_bv_unsigned in RR4.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
         assert (HPR : aregs_preserved regs (ms_regs msX));
         [ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)] HS);
           [exact HAE | vm_compute; reflexivity]
         | exact (sn_tail ly S W regs mem md ch r idx q bs s G (ms_regs msX) (ms_mem msX) _ HPRE HRO HJ RR10 RR11 RR12
             RR13 RR1 ltac:(unfold spZ at 1; rewrite RR2; reflexivity) RR3 RR4 HPR KP Hin Hlen HBS ltac:(lia) HB1 Hsc Hsl
             Hqp Hx Hxw Hxm Hxwin Hxd Hxra Hxhv HISV HGM HFS HFG HFlo ltac:(unfold IMG_HI; lia) HFcan HFRM) ]
         end.
      -- (* name = NULL: a3 = "" (A_OBJ 11) *)
         rewrite branch_ne_U, U_SLit, (U_atom E 12 q E12) in Hc by lia. change (zcanon 0) with 0 in Hc.
         apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hq0.
         destruct HNM as [(_ & ->) | (Hqp & _)]; [|lia].
         (* "": its byte through absn_rom_kept, the rest of its word through the image (sn_aview_rom), its shadow
            from the registered global *)
         pose proof (sn_rom_kept W mem HRO) as HRK.
         destruct HES as [HEb HEw].
         assert (HXe : forall i, 0 <= i <= Z.of_nat (length (@nil Z)) ->
           aview SEGS (w_H W) mem (VAL (A_OBJ 11) + i) = Some (nth (Z.to_nat i) ([] ++ [0]) 0)).
         { intros i Hi. destruct (HEb i ltac:(cbn in Hi |- *; lia)) as (Hr & Ho & He & Hv).
           rewrite (HRK _ Hr Ho He). exact Hv. }
         assert (HXw : forall a, VAL (A_OBJ 11) + Z.of_nat (length (@nil Z)) < a <
           absn_word_end (VAL (A_OBJ 11)) (Z.of_nat (length (@nil Z))) -> aview SEGS (w_H W) mem a <> None).
         { intros a Ha. destruct (HEw a Ha) as (_ & Hv). exact (sn_aview_rom W mem a Hv). }
         assert (HWE : absn_word_end (VAL (A_OBJ 11)) 0 <= VAL (A_OBJ 11) + 8)
           by (unfold absn_word_end; pose proof (Z.mod_pos_bound (VAL (A_OBJ 11) + 0) 8 ltac:(lia)); lia).
         destruct (ro_read_ok_glob SEGS B G ly S W mem md (VAL (A_OBJ 11)) 1 (VAL (A_OBJ 11)) 1 HGM HEG HISV HAR
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HXra HXhv].
         paj_run_tok RUN HS HJ SHOK Bspan_sn; [awr_ok_tac; exact Usp |].
         sn_keep KP regs W mem Usp.
         pmkst HS.
         sn_reg HS (10%bv : bv 5) RR10. rewrite denot_lit_U, (sn_U_dst E r idx E10 E11) in RR10 by lia.
         sn_reg HS (11%bv : bv 5) RR11. cbn [sv_denot] in RR11.
         sn_reg HS (12%bv : bv 5) RR12. cbn [sv_denot] in RR12. rewrite E251, Z.add_0_r, Z_to_bv_bv_unsigned in RR12.
         sn_reg HS (13%bv : bv 5) RR13. cbn [sv_denot] in RR13. rewrite E252, Z.add_0_r, Z_to_bv_bv_unsigned in RR13.
         sn_reg HS (1%bv : bv 5) RR1. cbn [sv_denot] in RR1. rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned in RR1.
         sn_reg HS (2%bv : bv 5) RR2. cbn [sv_denot] in RR2. rewrite E2, Z.add_0_r, Z_to_bv_bv_unsigned in RR2.
         sn_reg HS (3%bv : bv 5) RR3. cbn [sv_denot] in RR3. rewrite E3, Z.add_0_r, Z_to_bv_bv_unsigned in RR3.
         sn_reg HS (4%bv : bv 5) RR4. cbn [sv_denot] in RR4. rewrite E4, Z.add_0_r, Z_to_bv_bv_unsigned in RR4.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
         assert (HPR : aregs_preserved regs (ms_regs msX));
         [ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SBsn; Z_to_bv 64 (Boxreg.bx_n bs)] HS);
           [exact HAE | vm_compute; reflexivity]
         | refine (sn_tail ly S W regs mem md ch r idx (VAL (A_OBJ 11)) bs [] G (ms_regs msX) (ms_mem msX) _ HPRE HRO HJ
             RR10 RR11 RR12 RR13 RR1 ltac:(unfold spZ at 1; rewrite RR2; reflexivity) RR3 RR4 HPR KP Hin Hlen HBS
             ltac:(lia) HB1 (Forall_nil _) ltac:(cbn; lia) ltac:(lia) HXe HXw _ _ _ HXra HXhv HISV HGM HFS HFG HFlo
             ltac:(unfold IMG_HI; lia) HFcan HFRM);
           [ unfold amem_range; left; change (Z.of_nat (length (@nil Z))) with 0; lia
           | intros a Ha Hw; change (Z.of_nat (length (@nil Z))) with 0 in Ha; lia
           | change (Z.of_nat (length (@nil Z))) with 0; destruct Hrimg as [Hl | Hl]; [right | left]; lia ] ]
         end.
Qed.
End h.
End f.
End d.
