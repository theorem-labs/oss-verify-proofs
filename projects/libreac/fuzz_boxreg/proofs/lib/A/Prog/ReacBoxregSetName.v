(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 586 of its 641 lines of code are new or changed and 314 lines of the source are left out. *)
(* reac_boxreg_set_name (fuzz_boxreg.asan 0x81ea4, 36 instructions): the contract of the ASan build's code.
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; sd ra,8(sp)), returns at once when idx < 0
   (bltz a1), loads n, the 4-byte word at r + 280, after checking that word's shadow byte (the report path,
   __asan_report_load4, is refuted by the block's shadow, which AR's shadow law gives for the 288-byte block r), and
   returns when idx >= n (bge, signed). Otherwise it sets a0 = r + 56 * idx + 24 (the name field of row idx), a1 = 32,
   a2 = "%s" (A_OBJ 10, 0x20d40), a3 = name or, when name is NULL, "" (A_OBJ 11, 0x20d60), restores ra, pops its frame
   and TAIL-calls snprintf (`j 0x41430`, __interceptor_trampoline_snprintf; the listing's PTail
   BS___interceptor_trampoline_snprintf).
   The tail call: at the call its own frame is gone (sp is the entry sp, ra the caller's), so the stack it needs is the
   snprintf wrapper's 2 * ESTACK (lib/A/Rt/SnprintfDef.v asnprintf_realizes, taken at
   pa_sigma BS___interceptor_trampoline_snprintf; its own 16-byte frame lies inside that window), and its post is the
   snprintf post at the caller's return address: the struct's name field holds firstn 31 name ++ [0], every other byte
   of the struct and every byte outside the window are kept, callee-saved registers are kept, and the FP state is the
   wrapper's fx' (apost_baseF: f registers equal except f10, fcsr the entry's or rounding mode 0; the two early
   returns never reach the wrapper and take fx' := fx). a0 is not stated: the function returns void.
   Hazards: the registry struct is 288 bytes (rows 0..280, n at +280, fabric at +284); the name field
   r + 56 * idx + 24 .. + 56 lies inside it only for idx <= 4, which comes from idx < n and Pau's boxreg_B1
   (0 <= n <= 5); the name string must be NUL-terminated, with the rest of its NUL's 8-byte word readable (musl's memchr
   word loop under strnlen), outside the struct and the window, and its shadow addressable (the wrapper's printf_common
   check). The function makes no call before the tail call and writes only its own frame, so the name premises,
   stated at entry, hold at the call; a caller re-derives them at its own call (for a heap name: the block's bytes,
   which journals keep, AR's shadow law, and asn_blk_tail_vis of lib/A/Rt/SnprintfDef.v).
   The image's "%s" (A_OBJ 10, 0x20d40) and "" (A_OBJ 11, 0x20d60) and the read-only image the wrapper reads
   (asn_rom_kept, lib/A/Rt/SnprintfDef.v) are stated by facts that hold in every state, so that a caller has them at
   its call after any earlier call (an ajournal keeps no shadow byte of the image, lib/Reusable/YCbq.v:358, and keeps
   an image byte only when it is neither an owned static nor an errno byte, :362):
   - asn_rom_kept: arodata_okP on the read-only segments; arodata_okP is carried by every journal
     (lib/A/Prog/BoxBase.v arodata_ok_journalP);
   - their bytes: asn_rom_bytes / asn_rom_str (state-free: read-only image bytes that are no owned static and no errno
     byte, read through asn_rom_kept; the rest of "" 's 8-byte word may be owned and is read through aview's image
     fallback, `seg_rom ... <> None`);
   - their shadow: globs_marked G with In (q, sz) G (range_addressable) and img_shadow_vis with the 64-byte margins
     (shadow_hull_vis), lib/A/Prog/BoxRo.v ro_read_ok_glob; both hold in every AR state;
   - 0 < q, amem_range, apart from the window and from the destination: from the margins, alloc_ceiling below the
     stack, and AR_client_img_law (a heap byte is no image byte);
   - R2 (asnprintf_realizes P1 0x10000 <= f, P2 f + 3 <= 0x99b40, P3 amem_range x (|s| + 8)): P1 from the margin
     IMG_LO + 64 <= VAL (A_OBJ 10), P2 the spec's own premise, P3 name_ok's conjunct or, for "", the margins.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReacBoxregSetName.v) adds UBSan traps (unimp) for r NULL,
   r misaligned, idx >= 5 and the pointer overflow of r + 56 * idx, refuted by the block law and boxreg_B1.
   The memory model is Pau's plain one, used as it is: lib/Prog/Boxreg.v (bx_n, boxreg_B1) and the post of
   lib/Prog/reac_boxreg_set_name_c.v (pf_bytes (firstn 31 s ++ [0]) at r + 56 * idx + 24 when 0 <= idx < bx_n bs,
   nothing otherwise), written into the struct's bytes with lib/Lib/Mem.v upd_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The struct's 288 bytes after the call (REG_SIZE: lib/A/Prog/ReacBoxregInit.v): unchanged when idx < 0 or
   idx >= n, else the name field of row idx holds Pau's pf_bytes (firstn 31 s ++ [0]). *)
Definition treac_boxreg_set_name_bytes (bs : list byte) (idx : Z) (s : list Z) : list byte :=
if (idx <? 0) || (Boxreg.bx_n bs <=? idx) then bs
else Lib.Mem.upd_bytes bs (Z.to_nat (56 * idx + 24)) (printf_facts_c.pf_bytes (firstn 31 s ++ [0])).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: the snprintf wrapper's 2 * ESTACK, taken at the entry
   sp because the tail call is made after the function pops its 16-byte frame. *)
Definition A_reac_boxreg_set_nameP : Z := BASE + AF_reac_boxreg_set_name.
Definition REAC_BOXREG_SET_NAME_STK : Z := 2 * ESTACK.
(* The name argument q: NULL (the call prints ""), or the NUL-terminated string s at q, with the rest of its NUL's
   8-byte word readable, outside the window below sp and outside the struct r, its shadow addressable (Pau's name_ok,
   lib/Prog/reac_boxreg_set_name_c.v, over the ASan view). *)
Definition treac_boxreg_set_name_name_ok (W : world SEGS) (mem : word -> option byte) (sp r q : Z) (s : list Z)
  : Prop :=
(q = 0 /\ s = []) \/
(0 < q /\ Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
 (forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) mem (q + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
 (forall a, q + Z.of_nat (length s) < a < asn_word_end q (Z.of_nat (length s)) -> aview SEGS (w_H W) mem a <> None) /\
 amem_range q (Z.of_nat (length s) + 8) /\
 (forall a, q <= a < asn_word_end q (Z.of_nat (length s)) -> ~ (sp - REAC_BOXREG_SET_NAME_STK <= a < sp)) /\
 (asn_word_end q (Z.of_nat (length s)) <= r \/ r + REG_SIZE <= q) /\
 range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q (Z.of_nat (length s) + 1) /\
 shadow_hull_vis (aview SEGS (w_H W) mem) q (Z.of_nat (length s) + 1)).
Section h.
Variable B : asyms.
Definition treac_boxreg_set_name_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r idx : Z) (bs : list byte)
  (s : list Z) : world SEGS -> config -> Prop :=
apost_baseF SEGS B REAC_BOXREG_SET_NAME_STK [(r, r + REG_SIZE)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W') mem' (r + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (treac_boxreg_set_name_bytes bs idx s) (Z_to_bv 8 0))))).
Definition treac_boxreg_set_name_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r idx q : Z) (bs : list byte) (s : list Z) (G : list (Z * Z)),
afn_pre SEGS B REAC_BOXREG_SET_NAME_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 idx -> getr regs 12 = w64 q -> -2 ^ 31 <= idx < 2 ^ 31 ->
(* the registry struct: a heap block holding bs *)
In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
(* the name *)
treac_boxreg_set_name_name_ok W mem (spZ regs) r q s ->
(* facts of the image and of the runtime's symbols, true in every state *)
img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the image's "%s" (A_OBJ 10) and "" (A_OBJ 11): bytes of the read-only image, registered globals *)
asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT -> In (VAL (A_OBJ 10), 3) G ->
IMG_LO + 64 <= VAL (A_OBJ 10) -> VAL (A_OBJ 10) + 3 + 64 <= IMG_HI ->
(* R2 (a Theorem Labs lane 15:05Z): the format below the image's GOT canary slot, which the snprintf contract now asks (P2) *)
VAL (A_OBJ 10) + 3 <= 0x99b40 ->
asn_rom_str SEGS B (VAL (A_OBJ 11)) [] -> In (VAL (A_OBJ 11), 1) G ->
IMG_LO + 64 <= VAL (A_OBJ 11) -> VAL (A_OBJ 11) + 1 + 64 <= IMG_HI ->
(* the rounding mode at entry, which this function hands to the snprintf wrapper (SnprintfDef.v) *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (cfg_at SEGS A_reac_boxreg_set_nameP regs mem md)
(treac_boxreg_set_name_post regs ly S W mem md r idx bs s).
(* The walk. Model facts first: the struct's byte i as a number, n's 4 bytes as the word the code loads, and the
   bytes the call leaves in the struct. *)
Definition snb (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Lemma snb_range : forall bs i, 0 <= snb bs i < 256.
Proof.
intros bs i. unfold snb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.
Definition sn_nu (bs : list byte) : Z := snb bs 280 + 256 * (snb bs 281 + 256 * (snb bs 282 + 256 * snb bs 283)).
Lemma sn_nu_range : forall bs, 0 <= sn_nu bs < 2 ^ 32.
Proof.
intros bs. unfold sn_nu. pose proof (snb_range bs 280). pose proof (snb_range bs 281).
pose proof (snb_range bs 282). pose proof (snb_range bs 283). lia.
Qed.
Lemma sn_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros A l. induction l as [|x l IH]; intros k d Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma sn_bsub_280 : forall bs : list byte, length bs = 288%nat ->
  Boxreg.bsub bs 280 4 = [nth 280 bs (Z_to_bv 8 0); nth 281 bs (Z_to_bv 8 0); nth 282 bs (Z_to_bv 8 0); nth 283 bs (Z_to_bv 8 0)].
Proof.
intros bs Hl. unfold Boxreg.bsub. change (Z.to_nat 280) with 280%nat. change (Z.to_nat 4) with 4%nat.
rewrite (sn_skipn_cons bs 280 (Z_to_bv 8 0)) by lia. rewrite (sn_skipn_cons bs 281 (Z_to_bv 8 0)) by lia.
rewrite (sn_skipn_cons bs 282 (Z_to_bv 8 0)) by lia. rewrite (sn_skipn_cons bs 283 (Z_to_bv 8 0)) by lia.
reflexivity.
Qed.
Lemma sn_bx_n : forall bs, length bs = 288%nat -> Boxreg.boxreg_B1 bs -> Boxreg.bx_n bs = sn_nu bs.
Proof.
intros bs Hl HB. pose proof (sn_nu_range bs) as Hr. unfold Boxreg.boxreg_B1, Boxreg.bx_n, Boxreg.rd4 in *.
rewrite (sn_bsub_280 bs Hl) in *.
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val in *.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val] in *.
unfold sn_nu, snb in *. change (Z.to_nat 280) with 280%nat in *. change (Z.to_nat 281) with 281%nat in *.
change (Z.to_nat 282) with 282%nat in *. change (Z.to_nat 283) with 283%nat in *.
set (b0 := bv_unsigned (nth 280 bs (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 281 bs (Z_to_bv 8 0))) in *.
set (b2 := bv_unsigned (nth 282 bs (Z_to_bv 8 0))) in *. set (b3 := bv_unsigned (nth 283 bs (Z_to_bv 8 0))) in *.
replace (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) with (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) in * by lia.
set (x := b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) in *. clearbody x.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma sn_nu_byte : forall bs k, (k < 4)%nat -> (sn_nu bs / 2 ^ (8 * Z.of_nat k)) mod 256 = snb bs (280 + Z.of_nat k).
Proof.
intros bs k Hk. unfold sn_nu.
pose proof (snb_range bs 280) as R0. pose proof (snb_range bs 281) as R1.
pose proof (snb_range bs 282) as R2. pose proof (snb_range bs 283) as R3.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (280 + Z.of_nat 0) with 280. change (2 ^ (8 * Z.of_nat 0)) with 1. Z.div_mod_to_equations. lia.
- change (280 + Z.of_nat 1) with 281. change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. lia.
- change (280 + Z.of_nat 2) with 282. change (2 ^ (8 * Z.of_nat 2)) with 65536. Z.div_mod_to_equations. lia.
- change (280 + Z.of_nat 3) with 283. change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.
Lemma sn_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Lemma sn_out_range : forall s, Forall (fun c => 0 < c < 256) s -> forall j, 0 <= nth j (asn_out 32 s) 0 < 256.
Proof.
intros s Hs j. destruct (Nat.lt_ge_cases j (length (asn_out 32 s))) as [Hj|Hj].
- pose proof (nth_In (asn_out 32 s) 0 Hj) as Hi. remember (nth j (asn_out 32 s) 0) as c eqn:Hc. clear Hc.
  unfold asn_out in Hi. apply in_app_or in Hi as [Hi|[Hi|[]]].
  + apply sn_in_firstn in Hi. rewrite Forall_forall in Hs. specialize (Hs _ Hi). lia.
  + subst c. lia.
- rewrite nth_overflow by exact Hj. lia.
Qed.
Lemma sn_out_len : forall s, (1 <= length (asn_out 32 s) <= 32)%nat.
Proof.
intros s. unfold asn_out. rewrite length_app, length_firstn. cbn [length]. change (Z.to_nat (32 - 1)) with 31%nat. lia.
Qed.
Lemma sn_upd_nth : forall (bs : list byte) (idx : Z) (s : list Z) (i : Z),
  length bs = 288%nat -> 0 <= idx <= 4 -> Forall (fun c => 0 < c < 256) s -> 0 <= i < 288 ->
  bv_unsigned (nth (Z.to_nat i) (Lib.Mem.upd_bytes bs (Z.to_nat (56 * idx + 24))
    (printf_facts_c.pf_bytes (firstn 31 s ++ [0]))) (Z_to_bv 8 0)) =
  if (56 * idx + 24 <=? i) && (i <? 56 * idx + 24 + Z.of_nat (length (asn_out 32 s)))
  then nth (Z.to_nat (i - (56 * idx + 24))) (asn_out 32 s) 0
  else bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
intros bs idx s i Hl Hidx Hs Hi.
change (firstn 31 s ++ [0]) with (asn_out 32 s).
pose proof (sn_out_len s) as HL.
assert (HLp : length (printf_facts_c.pf_bytes (asn_out 32 s)) = length (asn_out 32 s))
  by (unfold printf_facts_c.pf_bytes; apply length_map).
pose proof (Lib.Mem.upd_bytes_nth bs (Z.to_nat (56 * idx + 24)) (printf_facts_c.pf_bytes (asn_out 32 s)) (Z.to_nat i)
  ltac:(rewrite HLp; lia) ltac:(lia)) as Hn.
rewrite HLp in Hn.
destruct (Z.leb_spec (56 * idx + 24) i) as [H1|H1]; destruct (Z.ltb_spec i (56 * idx + 24 + Z.of_nat (length (asn_out 32 s)))) as [H2|H2];
destruct (Nat.leb_spec (Z.to_nat (56 * idx + 24)) (Z.to_nat i)) as [N1|N1];
destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (56 * idx + 24) + length (asn_out 32 s))) as [N2|N2];
cbn [andb] in Hn |- *; try (exfalso; lia).
- assert (Hj : (Z.to_nat i - Z.to_nat (56 * idx + 24) < length (asn_out 32 s))%nat) by lia.
  unfold printf_facts_c.pf_bytes in Hn. rewrite nth_error_map, (nth_error_nth' _ 0 Hj) in Hn. cbn [option_map] in Hn.
  rewrite (nth_error_nth _ _ _ Hn). replace (Z.to_nat (i - (56 * idx + 24))) with (Z.to_nat i - Z.to_nat (56 * idx + 24))%nat by lia.
  pose proof (sn_out_range s Hs (Z.to_nat i - Z.to_nat (56 * idx + 24))) as Hr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
- rewrite (nth_error_nth' bs (Z_to_bv 8 0)) in Hn by lia. rewrite (nth_error_nth _ _ _ Hn). reflexivity.
- rewrite (nth_error_nth' bs (Z_to_bv 8 0)) in Hn by lia. rewrite (nth_error_nth _ _ _ Hn). reflexivity.
Qed.
Lemma sn_bytes_in : forall bs idx s i, length bs = 288%nat -> 0 <= idx < Boxreg.bx_n bs -> Boxreg.boxreg_B1 bs ->
  Forall (fun c => 0 < c < 256) s -> 0 <= i < 288 ->
  bv_unsigned (nth (Z.to_nat i) (treac_boxreg_set_name_bytes bs idx s) (Z_to_bv 8 0)) =
  if (56 * idx + 24 <=? i) && (i <? 56 * idx + 24 + Z.of_nat (length (asn_out 32 s)))
  then nth (Z.to_nat (i - (56 * idx + 24))) (asn_out 32 s) 0
  else bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
intros bs idx s i Hl Hidx HB Hs Hi. unfold Boxreg.boxreg_B1 in HB. unfold treac_boxreg_set_name_bytes.
replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with false
  by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
apply sn_upd_nth; [exact Hl | lia | exact Hs | exact Hi].
Qed.
Lemma sn_bytes_out : forall bs idx s, (idx <? 0) || (Boxreg.bx_n bs <=? idx) = true -> treac_boxreg_set_name_bytes bs idx s = bs.
Proof. intros bs idx s H. unfold treac_boxreg_set_name_bytes. rewrite H. reflexivity. Qed.
Lemma sn_val_mem : forall H (mem : word -> option byte) r bs,
  (forall i, 0 <= i < REG_SIZE -> aview SEGS H mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  val_mem SEGS (mrestrict H mem) (r + 280) (N.to_nat 4) (sn_nu bs).
Proof.
intros H mem r bs Hbs. unfold val_mem. intros k Hk. change (N.to_nat 4) with 4%nat in Hk |- *.
rewrite le_byte_small by (pose proof (sn_nu_range bs); first [lia | (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)]).
destruct (aview_byte SEGS H mem (r + (280 + Z.of_nat k)) _ (Hbs (280 + Z.of_nat k) ltac:(unfold REG_SIZE; lia)))
  as (b & Hb & Hv & _).
replace (r + 280 + Z.of_nat k) with (r + (280 + Z.of_nat k)) by lia. rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite (sn_nu_byte bs k Hk). unfold snb. symmetry. exact Hv.
Qed.
(* The symbolic start state: the 16-byte frame, the shadow GOT word and cell (PALib), and n at r + 280; the struct's
   288 bytes are one shadow entry (the block law makes them addressable). *)
Definition SN_SB : Z := 0x7fff8000.
Definition sn_Bx : sv := SOff 32 0.
Definition sn_span : Z * Z := (SN_SB, SN_SB + 2 ^ 44 - 1).
Definition sn_RN : YP09.region := YP09.mkRegion (Some 10%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition sn_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF SN_SB SN_SB 0);
           (33%nat, mkAF 0 5 0)] [] [].
Definition ss_sn : sstate :=
  mkSS AF_reac_boxreg_set_name sr_atoms [stack_region 16; got_regionP; bcell_regionP 32; sn_RN] None sn_facts.
Definition sn_SH : list shent := [mkSHE 10 0 288].
Definition sn_extra (bs : list byte) : list word := map (Z_to_bv 64) [SN_SB; sn_nu bs].
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib (PI := PI) B.
Hypothesis ASNP : asnprintf_realizes SEGS B (SIGMA BS___interceptor_trampoline_snprintf).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
Lemma sn_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r : Z) (bs : list byte),
  afn_pre SEGS B REAC_BOXREG_SET_NAME_STK ly S W regs mem md ch ->
  getr regs 10 = w64 r -> In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (sn_extra bs))) ss_sn
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_boxreg_set_name)) mem (seg_rom SEGS))) /\
  sh_ok SEGS sn_Bx sn_SH (Eimg (Ereg regs (sn_extra bs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r bs HPRE H10 Hin Hlen Hbs HB1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STK = 8192) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in *.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Hrimg. change (req_size REG_SIZE) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (sn_bx_n bs Hlen HB1) as Hnu. pose proof (sn_nu_range bs) as Hnur.
unfold Boxreg.boxreg_B1 in HB1. rewrite Hnu in HB1.
set (E := Eimg (Ereg regs (sn_extra bs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (sn_extra bs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SN_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (sn_nu bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_sn. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, sn_RN.
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
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SN_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SN_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (sn_nu bs));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (sn_val_mem (w_H W) mem r bs Hbs).
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, sn_RN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hrimg Hrceil Hr4096. clear. intros.
    repeat split; lia.
  + split; [|split; exact I].
    cbn [sn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SN_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil HB1. clear. unfold SN_SB. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, sn_SH. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (HUB : U E sn_Bx = SHADOW_OFF) by (unfold sn_Bx; rewrite (U_atom E 32 SN_SB E32) by (unfold SN_SB; lia); reflexivity).
  rewrite HUB, (U_atom E 10 r E10) by lia.
  rewrite <- (aview_rd_of SEGS). split.
  + eapply (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZE (r + 0) (288 - 0) HAR Hin);
    change (req_size REG_SIZE) with 288; lia.
  + intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hria Hr4096 Hrceil C1 C3 C5. clear. intros. lia.
Qed.
(* The registers' values at the stops, and the three branch conditions. *)
Lemma sn_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma sn_den_reg : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma sn_br_ltz : forall E n a, ew E n = Z_to_bv 64 a -> -2 ^ 63 <= a < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (a <? 0).
Proof. intros E n a H Ha. rewrite (sn_den_atom E n a H). cbn [branch_taken sv_denot]. apply Boxreg.lts_lit; lia. Qed.
Lemma sn_br_ge : forall E n m a b, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b ->
  -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = negb (a <? b).
Proof.
intros E n m a b Hn Hm Ha Hb. rewrite (sn_den_atom E n a Hn), (sn_den_atom E m b Hm). cbn [branch_taken].
rewrite Boxreg.lts_lit by lia. reflexivity.
Qed.
Lemma sn_den_row : forall E r idx, ew E 10 = Z_to_bv 64 r -> ew E 11 = Z_to_bv 64 idx ->
  0 <= r -> 0 <= idx <= 4 -> r + 56 * idx + 24 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 10 24) (SMd M_MUL (SOff 11 0) (SLit 56))) = Z_to_bv 64 (r + 56 * idx + 24).
Proof.
intros E r idx H10 H11 Hr Hi Hlt. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 11 idx H11) by lia. rewrite U_SOff, H10, U_SLit.
rewrite unsigned_lit_small by lia.
rewrite (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id (r + 24)) by (unfold M64; lia).
rewrite (zcanon_id (idx * 56)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* The two returns (idx < 0, idx >= n): nothing written, the struct read back from the entry memory. *)
Lemma sn_ret_post : forall ly S W (regs : bvmap 5 word) mem md (r idx : Z) (bs : list byte) (s : list Z) regsF memF mdF,
  ajournal SEGS B REAC_BOXREG_SET_NAME_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memF mdF 0 ->
  aregs_preserved regs regsF ->
  (idx <? 0) || (Boxreg.bx_n bs <=? idx) = true ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) memF (r + i) = aview SEGS (w_H W) mem (r + i)) ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  treac_boxreg_set_name_post regs ly S W mem md r idx bs s W (mkCfg (mkst regsF (getr regs 1) memF (seg_rom SEGS)) mdF).
Proof.
intros ly S W regs mem md r idx bs s regsF memF mdF HJ HP Hc Hk Hbs.
unfold treac_boxreg_set_name_post, apost_baseF. exists fx, ly, S, regsF, memF, mdF.
split; [reflexivity|]. split; [intros; reflexivity|]. split; [left; reflexivity|].
split; [exact HJ|]. split; [exact HP|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
intros i Hi. rewrite (Hk i Hi), (Hbs i Hi), (sn_bytes_out bs idx s Hc). reflexivity.
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
(* The tail call: the snprintf wrapper's contract taken at its trampoline with the entry sp and the caller's ra,
   and its post turned into the function's post. The one place that reads the snprintf contract. *)
Lemma sn_tail : forall ly S W (regs : bvmap 5 word) mem md ch (r idx q : Z) (bs : list byte) (s : list Z)
  (G : list (Z * Z)) (regsT : bvmap 5 word) memT mdT (x : Z),
  afn_pre SEGS B REAC_BOXREG_SET_NAME_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> 0 <= idx < Boxreg.bx_n bs ->
  treac_boxreg_set_name_name_ok W mem (spZ regs) r q s ->
  (q = 0 /\ x = VAL (A_OBJ 11) \/ q <> 0 /\ x = q) ->
  img_shadow_vis SEGS B -> globs_marked SEGS B G ->
  asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT -> In (VAL (A_OBJ 10), 3) G ->
  IMG_LO + 64 <= VAL (A_OBJ 10) -> VAL (A_OBJ 10) + 3 + 64 <= IMG_HI -> VAL (A_OBJ 10) + 3 <= 0x99b40 ->
  asn_rom_str SEGS B (VAL (A_OBJ 11)) [] -> In (VAL (A_OBJ 11), 1) G ->
  IMG_LO + 64 <= VAL (A_OBJ 11) -> VAL (A_OBJ 11) + 1 + 64 <= IMG_HI ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  ajournal SEGS B REAC_BOXREG_SET_NAME_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsT ->
  getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
  getr regsT 10 = Z_to_bv 64 (r + 56 * idx + 24) -> getr regsT 11 = Z_to_bv 64 32 ->
  getr regsT 12 = Z_to_bv 64 (VAL (A_OBJ 10)) -> getr regsT 13 = Z_to_bv 64 x ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
    (treac_boxreg_set_name_post regs ly S W mem md r idx bs s).
Proof.
intros ly S W regs mem md ch r idx q bs s G regsT memT mdT x HPRE HRO Hin Hlen Hbs HB1 Hidx HNAME Hx HISV HGM
  HFB HFG HF1 HF2 HF3 HSB HSG HS1 HS2 HFRM HJ KEEP HP T1 T2 T3 T4 T10 T11 T12 T13.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STK = 8192) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Hrimg. change (req_size REG_SIZE) with 288 in Hrimg.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'.
unfold IMG_HI in HF2, HS2.
assert (Hsp : spZ regsT = spZ regs) by (unfold spZ; rewrite T2; reflexivity).
pose proof HJ as (HART & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT & _ & _ & _).
(* the read-only image at the call: the entry's arodata_okP, kept because the function wrote only its frame *)
assert (ROMK : asn_rom_kept SEGS B W memT).
{ intros a Hrom Hown Herr.
  assert (Ha : 0 <= a < kLowMemEnd).
  { destruct Hrom as (sg & Hsg & _ & Hr). apply pa_segs_low. exists sg. split; [exact Hsg | exact Hr]. }
  rewrite (KEEP a) by lia. apply HRO; [left; exact Hrom | exact Hown | exact Herr]. }
(* the format "%s": its bytes through ROMK, its shadow from globs_marked / img_shadow_vis in the call's AR state *)
assert (HFMT : forall i, 0 <= i < 3 -> aview SEGS (w_H W) memT (VAL (A_OBJ 10) + i) = Some (nth (Z.to_nat i) ASN_FMT 0)).
{ intros i Hi. destruct (HFB i ltac:(change (Z.of_nat (length ASN_FMT)) with 3; lia)) as (Hrom & Hown & Herr & Hb).
  rewrite (ROMK _ Hrom Hown Herr). exact Hb. }
destruct (ro_read_ok_glob SEGS B G ly S W memT mdT (VAL (A_OBJ 10)) 3 (VAL (A_OBJ 10)) 3 HGM HFG HISV HART
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HFRA HFHV].
(* the string argument: q's string (name_ok, kept) or the image's "" *)
assert (STR : Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\ 0 < x /\
  (forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) memT (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
  (forall a, x + Z.of_nat (length s) < a < asn_word_end x (Z.of_nat (length s)) -> aview SEGS (w_H W) memT a <> None) /\
  amem_range x (Z.of_nat (length s) + 8) /\
  (forall a, x <= a < asn_word_end x (Z.of_nat (length s)) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  (asn_word_end x (Z.of_nat (length s)) <= r + 56 * idx + 24 \/ r + 56 * idx + 24 + 32 <= x) /\
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) memT) x (Z.of_nat (length s) + 1)).
{ rewrite Hsp. destruct Hx as [[Hq0 ->] | [Hq0 ->]].
  - destruct HNAME as [[_ ->] | (Hq & _)]; [|lia].
    destruct HSB as [HSB1 HSB2].
    destruct (ro_read_ok_glob SEGS B G ly S W memT mdT (VAL (A_OBJ 11)) 1 (VAL (A_OBJ 11)) 1 HGM HSG HISV HART
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HERA HEHV].
    pose proof (Z.mod_pos_bound (VAL (A_OBJ 11) + Z.of_nat (length (@nil Z))) 8 ltac:(lia)) as Hm8.
    split; [constructor|]. split; [cbn; lia|]. split; [lia|].
    split.
    { intros i Hi. destruct (HSB1 i ltac:(cbn in Hi |- *; lia)) as (Hrom & Hown & Herr & Hb).
      rewrite (ROMK _ Hrom Hown Herr). exact Hb. }
    split.
    { intros a Ha. destruct (HSB2 a Ha) as (_ & Hn). exact (sn_aview_rom W memT a Hn). }
    split; [unfold amem_range; cbn [length Z.of_nat]; lia|].
    split; [intros a Ha; unfold asn_word_end in Ha; cbn [length Z.of_nat] in *; lia|].
    split; [unfold asn_word_end; cbn [length Z.of_nat] in *; lia|].
    split; [exact HERA | exact HEHV].
  - destruct HNAME as [[Hq' _] | (Hq & HFs & Hls & Hby & Hrest & Hamr & Hwin & Hdisj & Hra' & Hhv)]; [lia|].
    assert (Hqb : 0 <= q /\ q + Z.of_nat (length s) + 8 <= 2 ^ 47) by (unfold amem_range in Hamr; lia).
    pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)) as Hm8.
    assert (Hwe : q + Z.of_nat (length s) < asn_word_end q (Z.of_nat (length s))) by (unfold asn_word_end; lia).
    split; [exact HFs|]. split; [exact Hls|]. split; [exact Hq|].
    split.
    { intros i Hi. rewrite KEEP; [apply Hby; exact Hi | lia |].
      intros Hw. apply (Hwin (q + i)); [lia | unfold REAC_BOXREG_SET_NAME_STK; lia]. }
    split.
    { intros a Ha. assert (Hw' : ~ (spZ regs - REAC_BOXREG_SET_NAME_STK <= a < spZ regs)) by (apply Hwin; lia).
      rewrite KEEP; [apply Hrest; exact Ha | unfold asn_word_end in Ha; lia | unfold REAC_BOXREG_SET_NAME_STK in Hw'; lia]. }
    split; [exact Hamr|].
    split; [exact Hwin|].
    split; [destruct Hdisj as [Hd|Hd]; [left | right]; unfold REG_SIZE in *; lia|].
    split.
    + eapply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 16) (spZ regs) q (Z.of_nat (length s) + 1));
      [intros s0 Hs0 Hns0; apply KEEP; [exact Hs0 | exact Hns0] | lia | lia | lia | exact Hra'].
    + eapply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 16) (spZ regs) q (Z.of_nat (length s) + 1));
      [intros s0 Hs0 Hns0; apply KEEP; [exact Hs0 | exact Hns0] | lia | lia | lia | lia | exact Hhv]. }
destruct STR as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
assert (HPRE' : ecall_pre SEGS B ly S W regsT memT mdT).
{ eapply (ecall_pre_at SEGS B REAC_BOXREG_SET_NAME_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0
    regsT 0 HJ); [lia | reflexivity | lia | lia | rewrite T1; exact Hra | rewrite T3; exact Hgp | rewrite T4; exact Htp]. }
assert (Hlo2 : ly_stk_lo ly + 2 * ESTACK <= spZ regsT) by (rewrite Hsp; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply HpresT; rewrite Hsp in Ha; lia).
assert (HDW : forall a, r + 56 * idx + 24 <= a < r + 56 * idx + 24 + 32 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT))
  by (intros a Ha; rewrite Hsp; lia).
assert (HFW : forall a, VAL (A_OBJ 10) <= a < VAL (A_OBJ 10) + 3 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT))
  by (intros a Ha; rewrite Hsp; lia).
eapply SRr_mono.
{ exact (ASNP ly S W regsT memT mdT (r + 56 * idx + 24) 32 (VAL (A_OBJ 10)) x s r REG_SIZE
    HPRE' Hlo2 Hpres2E T10 T11 T12 T13 ltac:(lia) Hin ltac:(lia) ltac:(unfold REG_SIZE; lia) HDW
    HFMT ltac:(lia) ltac:(unfold amem_range; lia) ltac:(lia) HF3 HFW ltac:(lia) HFRA HFHV
    S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 ROMK HFRM). }
cbv beta. intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & -> & HFR & HFC & HAR2 & HP2 & Hsame & Ha0 & Hw & Hkeep & Hpres2).
unfold treac_boxreg_set_name_post, apost_baseF.
exists fx2, ly, S, regs2, mem2, md2.
split.
{ change (@cfg_at fx2 SEGS (raZ regsT) regs2 mem2 md2) with
    (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (bv_unsigned (getr regsT 1))) mem2 (seg_rom SEGS)) md2).
  rewrite Z_to_bv_bv_unsigned, T1. reflexivity. }
split; [exact HFR|]. split; [right; exact HFC|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low REAC_BOXREG_SET_NAME_STK (spZ regs) [(r, r + REG_SIZE)]
    ly S W mem md [] ly S W memT mdT 0 mem2 md2
    (fun a => (r + 56 * idx + 24 <= a < r + 56 * idx + 24 + Z.of_nat (length (asn_out 32 s))) \/
              (spZ regs - 2 * ESTACK <= a < spZ regs)) S [] HJ).
  - intros a Ha Hna. apply Hkeep; [exact Ha | intros H'; apply Hna; left; exact H' |].
    rewrite Hsp. intros H'; apply Hna; right; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left.
    + right; left. pose proof (sn_out_len s) as HL. split.
      * exists (r, r + REG_SIZE). split; [left; reflexivity|]. cbn [fst snd]. unfold REG_SIZE. lia.
      * exists r, REG_SIZE. split; [exact Hin|]. change (req_size REG_SIZE) with 288. lia.
    + left. unfold REAC_BOXREG_SET_NAME_STK. exact Ha.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
split; [exact (aregs_preserved_trans _ _ _ HP HP2)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
intros i Hi.
rewrite (sn_bytes_in bs idx s i Hlen Hidx HB1 S1 Hi).
destruct ((56 * idx + 24 <=? i) && (i <? 56 * idx + 24 + Z.of_nat (length (asn_out 32 s)))) eqn:Hc.
- apply andb_true_iff in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
  replace (r + i) with (r + 56 * idx + 24 + (i - (56 * idx + 24))) by lia.
  rewrite (Hw (i - (56 * idx + 24)) ltac:(lia)). reflexivity.
- apply andb_false_iff in Hc. unfold REG_SIZE in Hi.
  rewrite Hkeep.
  + rewrite KEEP by lia. exact (Hbs i Hi).
  + lia.
  + destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia.
  + rewrite Hsp. lia.
Qed.
(* Walk tactics: one run to the next stop; the entry memory read back outside the 16-byte frame; a register's value
   at a call stop; the two returns. *)
Ltac sn_run HS HJ SHOK Usp :=
  paj_run_tok RUN HS HJ SHOK sn_span; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
Ltac sn_keep KEEP Usp regs mem :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
    let K := fresh "KEEPn" in
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS Hh m1 a = aview SEGS Hh mem a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw; transitivity (aview SEGS Hh m0 a); [| exact (KEEP a Ha Hw)];
      apply (kept_of_frame Ex rs Hh m0 m1 (fun x => spZ regs - 16 <= x < spZ regs) HFr); [| exact Ha | exact Hw];
      let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros bb wl wh aa Hin Hr; cbv beta; vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [ injection Hin as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite Usp in Hr; lia] | ]);
      try contradiction
    | clear KEEP; rename K into KEEP;
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end ]
  end.
Ltac sn_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); pf)
  end.
Ltac sn_ret HS HJ KEEP E HAE E1 Hra regs bs cond :=
  let R1 := fresh "R1" in
  prreg HS (1%bv : bv 5) R1;
  eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat; cbn [ms_regs ms_mem];
  rewrite R1, E1, Hra;
  eapply sn_ret_post;
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (sn_extra bs) HS); [exact HAE | vm_compute; reflexivity]
  | cond
  | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply KEEP; unfold REG_SIZE in Hi; lia
  | eassumption ].
Ltac sn_tailcall HS HJ KEEP E HAE E1 E2 E3 E4 E10 E11 E251 regs bs r idx v13 Ex13 :=
  pmkst HS;
  let T10 := fresh "T10" in let T11 := fresh "T11" in let T12 := fresh "T12" in let T13 := fresh "T13" in
  let T1 := fresh "T1" in let T2 := fresh "T2" in let T3 := fresh "T3" in let T4 := fresh "T4" in
  sn_reg HS (10%bv : bv 5) (Z_to_bv 64 (r + 56 * idx + 24)) ltac:(apply sn_den_row; [exact E10 | exact E11 | lia | lia | lia]) T10;
  sn_reg HS (11%bv : bv 5) (Z_to_bv 64 32) ltac:(reflexivity) T11;
  sn_reg HS (12%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 10))) ltac:(exact (sn_den_atom E 251 _ E251)) T12;
  sn_reg HS (13%bv : bv 5) (Z_to_bv 64 v13) ltac:(exact (sn_den_atom E _ _ Ex13)) T13;
  sn_reg HS (1%bv : bv 5) (getr regs 1) ltac:(exact (sn_den_reg E 1 _ E1)) T1;
  sn_reg HS (2%bv : bv 5) (getr regs 2) ltac:(exact (sn_den_reg E 2 _ E2)) T2;
  sn_reg HS (3%bv : bv 5) (getr regs 3) ltac:(exact (sn_den_reg E 3 _ E3)) T3;
  sn_reg HS (4%bv : bv 5) (getr regs 4) ltac:(exact (sn_den_reg E 4 _ E4)) T4;
  eapply sn_tail;
  [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | lia | eassumption
  | | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
  | eassumption | eassumption | eassumption | eassumption | exact HJ | exact KEEP
  | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (sn_extra bs) HS); [exact HAE | vm_compute; reflexivity]
  | exact T1 | exact T2 | exact T3 | exact T4 | exact T10 | exact T11 | exact T12 | exact T13 ].
Theorem pb_reac_boxreg_set_name : treac_boxreg_set_name_spec.
Proof.
unfold treac_boxreg_set_name_spec.
intros ly S W regs mem md ch r idx q bs s G HPRE HRO H10 H11 H12 Hidx Hin Hlen Hbs HB1 HNAME HISV HGM HFB HFG HF1 HF2
  HF3 HSB HSG HS1 HS2 HFRM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (sn_entry ly S W regs mem md ch r bs HPRE H10 Hin Hlen Hbs HB1) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_SET_NAME_STK [(r, r + REG_SIZE)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_SET_NAME_STK = 8192) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof (sn_bx_n bs Hlen HB1) as Hnu. pose proof (sn_nu_range bs) as Hnur.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'. rewrite Hnu in HB1'.
assert (Hq : 0 <= q < 2 ^ 64).
{ destruct HNAME as [[-> _] | (Hq0 & _ & _ & _ & _ & Hqa & _)]; [lia|]. unfold amem_range in Hqa. lia. }
remember (Eimg (Ereg regs (sn_extra bs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (sn_extra bs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
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
assert (E33 : ew E 33 = Z_to_bv 64 (sn_nu bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E251 : ew E 251 = Z_to_bv 64 (VAL (A_OBJ 10)))
  by (change 251%nat with (A_OBJ 10); subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E 252 = Z_to_bv 64 (VAL (A_OBJ 11)))
  by (change 252%nat with (A_OBJ 11); subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs (sn_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
unfold cfg_at, A_reac_boxreg_set_nameP.
change (w64 (BASE + AF_reac_boxreg_set_name)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_set_name)).
(* the frame, the save of ra, up to `bltz idx` *)
sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
psrr_branch_tok RUN BR HS SHOK sn_span.
- (* idx < 0: the frame is popped and the function returns *)
  rewrite (sn_br_ltz E 11 idx E11) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hneg.
  sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
  sn_ret HS HJ KEEP E HAE E1 Hra regs bs ltac:(apply orb_true_iff; left; apply Z.ltb_lt; exact Hneg).
- rewrite (sn_br_ltz E 11 idx E11) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hnn.
  (* the shadow base through the GOT, the checked load of n (the check is decided by the block's shadow entry),
     up to `bge idx, n` *)
  sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
  psrr_branch_tok RUN BR HS SHOK sn_span.
  + (* idx >= n: return *)
    rewrite (sn_br_ge E 11 33 idx (sn_nu bs) E11 E33) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
    rename Hc into Hge.
    sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
    sn_ret HS HJ KEEP E HAE E1 Hra regs bs ltac:(apply orb_true_iff; right; apply Z.leb_le; lia).
  + rewrite (sn_br_ge E 11 33 idx (sn_nu bs) E11 E33) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
    rename Hc into Hlt.
    (* the row address, up to `bnez name` *)
    sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
    psrr_branch_tok RUN BR HS SHOK sn_span.
    * (* name != NULL: a3 = name, then the arguments, the pop of the frame and the tail jump *)
      rewrite branch_ne_U, (U_atom E 12 q E12 Hq), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
      rename Hc into Hqnz.
      sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
      sn_tailcall HS HJ KEEP E HAE E1 E2 E3 E4 E10 E11 E251 regs bs r idx q E12.
      right. split; [exact Hqnz | reflexivity].
    * (* name == NULL: a3 = "" *)
      rewrite branch_ne_U, (U_atom E 12 q E12 Hq), U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
      rename Hc into Hq0.
      sn_run HS HJ SHOK Usp. sn_keep KEEP Usp regs mem.
      sn_tailcall HS HJ KEEP E HAE E1 E2 E3 E4 E10 E11 E251 regs bs r idx (VAL (A_OBJ 11)) E252.
      left. split; [exact Hq0 | reflexivity].
Qed.
End h.
End f.
End d.
