(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Def.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0); the real frame's cell R+0xf8 -> R+0x118; hm_sh's sixth scope flag (x) out of scope. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the two inner cut states of
   ent_build's case 0 head and the statements of its four blocks. Statement text only: no function is proved here.

   THE CODE (pod.h:224-249, ent_headamp_key up to the end of the channel text ch). The piece runs from the jump
   table's case-0 target D = 0x81860, or from D0E = 0x818cc when no input byte is left, to G = 0x81a34, where the
   parts loop begins (lib/A/HPgSeg.v hs_cut_D, hs_cut_D0E, hs_cut_G).
     0x81860-0x8188c  t[96] in scope: 12 shadow bytes of F+0x20 := 0
     0x81890          beqz s9: no input byte left for c
     0x81894-0x818ac  c = fuzz_u8: the shadow check of the cursor, then `lbu`
     0x818b0-0x818bc  s8 = cursor + 2; bne of in.n with 2: no byte left for p
     0x818c0-0x818c8  in.n := 0 and p := 0, two bytes consumed
     0x82088-0x82098  p = fuzz_u8: the shadow check, then `lbu`
     0x8209c-0x820a8  s8 = cursor + 3; in.n := in.n - 3
     0x818cc-0x81910  no byte at all: t in scope, c = p = 0, in.n := 0
     0x820ac-0x820b4 / 0x81914-0x8191c  ch[24] in scope: 3 shadow bytes of F+0xa0 := 0
     0x820b8-0x820c4  bltu of c with 0xc7 picks the two arms below
     0x81920-0x81a30  DIG, c < 200: the digits of c mod 64 into r[4] (shadow 0x04), reversed into ch, its NUL,
                      r out of scope again
     0x820c8-0x82128  ODD, c >= 200: odd_ch[c mod 14] (the pointer table in .data.rel.ro), strlen, memcpy into ch
   So the piece is four blocks: D0 (0x81860 -> 0x81920 / 0x820c8), D0E (0x818cc -> 0x81920), DIG and ODD (both to
   0x81a34). Each `lb <shadow>; bnez; andi/blt` is one obligation of the token engine (lib/Reusable/YCbn.v), paid
   from the frame's shadow row (r, ch) or from the input block's addressable range (the two cursor reads). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the two inner pcs ===================================== *)
Definition R7_DIG : Z := 0x81920.   (* the digits of c mod 64, c < 200 *)
Definition R7_ODD : Z := 0x820c8.   (* odd_ch[c mod 14], c >= 200 *)

(* The instruction table of the piece: the two straight ranges and the four slow blocks its checks branch to
   (`andi u,x,7; blt u,t,<report>`), which the token engine must decode. *)
Definition r7_tbl : ctable :=
  build_table rsegs 0x81860 117
  (build_table rsegs 0x82088 44
  (build_table rsegs 0x82664 3
  (build_table rsegs 0x826b4 3
  (build_table rsegs 0x826d0 3
  (build_table rsegs 0x82784 3 TEmpty))))).
Lemma r7_tbl_ok : table_ok rsegs r7_tbl.
Proof.
unfold r7_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.

(* The shadow base the token engine matches (atom 32 holds the runtime's shadow offset) and the band it watches. *)
Definition R7Bx : sv := SOff 32 0.
Definition R7span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* The frame's shadow row at the pcs of the piece, in HPgMem's words (e is in scope from the pod loop's
   `sb zero` 0x817a4-0x817d4 and closes only after the join). *)
Lemma r7_PJ_sh : hs_PJ = hm_sh false false false true false false.
Proof. vm_compute. reflexivity. Qed.
Lemma r7_PG_sh : hs_PG = hm_sh true true false true false false.
Proof. vm_compute. reflexivity. Qed.
(* inside the digits and the reverse loop r is in scope as well (shadow byte 0x04, 0x8192c) *)
Definition r7_PR : list Z := hm_sh true true true true false false.
(* after the t stores and before the ch stores *)
Definition r7_PT : list Z := hm_sh true false false true false false.

(* The token engine's shadow entries, in app_entries' degenerate form (she_lo = the write window's end,
   she_hi = its start): they carry only "this window is application memory, not shadow", which is what
   cells_safe_b asks of a writable region inside the band. The atoms are the registers that hold the bases:
   22 = s6 = F + 0xe0 (r) and 20 = s4 = F + 0xa0 (ch). *)
Definition r7_SH_r : list shent := [mkSHE 22 4 0].
Definition r7_SH_ch : list shent := [mkSHE 20 24 0].
Definition r7_SH_rch : list shent := [mkSHE 22 4 0; mkSHE 20 24 0].

(* What case 0 reads of the turn's input before the two arms: the kind byte, then c and p (pod.h:234); on an
   empty input fuzz_u8 gives 0 and does not move the cursor (fuzz.h:37-43). HPgSeg.hs_g_of is this with the
   channel text of c in place of c. *)
Definition r7_cp_of (rr : list byte) : Z * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(c, pb, r3).
Lemma r7_g_of_cp : forall rr c pb r3,
(c, pb, r3) = r7_cp_of rr ->
hs_g_of rr = (if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Proof.
intros rr c pb r3 H. unfold hs_g_of, r7_cp_of in *.
destruct (Cursor.fuzz_u8 rr) as [kd r1]. destruct (Cursor.fuzz_u8 r1) as [c' r2].
destruct (Cursor.fuzz_u8 r2) as [pb' r3']. injection H as <- <- <-. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the locations both inner cuts carry =====================
   HPgSeg.hs_L_Dc0 and the four values case 0 holds at both arms: s4 = &ch, s11 = the key's second input
   byte, the cursor and what is left of the input. *)
Definition r7_L_arm (cx : hs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (pb : Z) : list (hd_loc * Z) :=
hs_L_Dc0 segs cx sh np ps cnt es
++ [(LCell XR 0x118, Z.of_nat (length r));
    (LReg 20, e_F (x_e segs cx) + 0xa0); (LReg 27, pb)].

(* ---------------- DIG = 0x81920: the digits arm, c < 200 ----------------
   t and ch are in scope and r is not yet (its granule opens at 0x8192c), so the frame's shadow row is
   HPgSeg.hs_PG, the row G also has. a0 = c, a7 = 10 and t0 = 9 are the digit loop's three values
   (0x8181c / 0x81900, 0x818a4 / 0x81904), and s9 is the cursor after c and p. *)
Definition r7_cut_DIG (cx : hs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
(r7_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 25, hs_cur segs cx rest r); (LReg 10, c); (LReg 17, 10); (LReg 5, 9)]) /\
hs_fsh_at segs cx W2 mem2 hs_PG /\
hs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + 0xf0) (hd_zbytes (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = r7_cp_of rr /\
0 <= c < 200 /\ 0 <= pb < 256.

(* ---------------- ODD = 0x820c8: the table arm, c >= 200 ----------------
   The same row; s8 (not s9) holds the cursor here, and the block copies it into s9 at 0x82124. *)
Definition r7_cut_ODD (cx : hs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
(r7_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 24, hs_cur segs cx rest r); (LReg 10, c)]) /\
hs_fsh_at segs cx W2 mem2 hs_PG /\
hs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + 0xf0) (hd_zbytes (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = r7_cp_of rr /\
200 <= c < 256 /\ 0 <= pb < 256.

(* ===================== the continuations of the two inner cuts ===================== *)
Section f.
Variable cx : hs_scx segs.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.
Definition r7_from_DIG (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
r7_cut_DIG cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs R7_DIG regs2 mem2 md2) POST.
Definition r7_from_ODD (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
r7_cut_ODD cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs R7_ODD regs2 mem2 md2) POST.
End f.

(* ===================== the three block statements of the piece =====================
   Together they give HPgSeg.hs_piece_W7a_stmt (lib/A/HPgEnt0.v). *)
(* the digits arm: from DIG to G, with the channel text dec64 (c mod 64) in ch *)
Definition r7_dig_stmt : Prop :=
forall cx POST rest i k,
hs_start_M01 segs B cx rest -> hs_from_G segs B MT cx POST rest i k ->
r7_from_DIG cx POST rest i k.
(* the table arm: from ODD to G, with odd_ch[c mod 14] in ch (the strlen wrapper and __asan_memcpy) *)
Definition r7_odd_stmt : Prop :=
forall cx POST rest i k,
hs_start_M01 segs B cx rest -> hs_from_G segs B MT cx POST rest i k ->
r7_from_ODD cx POST rest i k.
(* the head: both entries of case 0 to the two arms *)
Definition r7_head_stmt : Prop :=
forall cx POST rest i k kd,
hs_start_M01 segs B cx rest -> kd mod 10 = 0 ->
r7_from_DIG cx POST rest i k -> r7_from_ODD cx POST rest i k ->
hs_from_D segs B MT cx POST rest i k kd /\ hs_from_D0E segs B MT cx POST rest i k.

End d.
End c.
End b.
