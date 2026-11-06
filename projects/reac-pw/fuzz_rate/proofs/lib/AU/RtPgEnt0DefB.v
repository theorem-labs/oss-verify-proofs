(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Def.v at 27540f54413f for reac-pw/fuzz_rate's image A; rate's pcs (the head's two out-of-line blocks 0x81b38 and 0x81b58, the arms DIG 0x813f8 and ODD 0x81b6c), registers (in.n in s10, &ch in s6, the `v / 10` multiplier in t2) and code table; the frame's shadow rows in RtPgMem's seven-flag words; the piece lemma rt7_piece from the three block statements. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Def.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): image B's pcs (the arms DIG 0x8152c and ODD 0x81de0, the out-of-line range 0x81d58 .. 0x81e54 and the slow blocks 0x82270 / 0x82314), registers (what is left in t1, &ch in s2, p in s9, the cursor in the cell R+0x128, c in a3, the digit loop's 4 / 10 / 9 in t0 / t2 / t3, the `v / 10` multiplier in s5) and code table; the frame's shadow rows in lib/AU/RtPgMemB.v's words; the statements over lib/AU/RtPgSegB.v's cuts; names rt7_ -> rt7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the two inner cut states of
   ent_build's case-0 head, the statements of its three blocks and the piece lemma of lane W7a from them. Proves no
   function (kind: statement text).

   THE CODE (pod.h:224-249, ent_headamp_key up to the end of the channel text ch). The piece runs from the jump
   table's case-0 target D0 = 0x81460, or from D0E = 0x814d0 when no input byte is left (`beqz s9` 0x813e8), to
   G = 0x8160c, where the parts begin (lib/AU/RtPgSegB.v rsb_cut_D, rsb_cut_D0E, rsb_cut_G). At D0, s10 is the kind
   byte's address, s2 the cursor after it, s6 what is left after it, t1 what was left before it and a6 = 1 the left
   side of the trap tests; s3 = shadow_addr F, s4 the shadow offset.
     0x81460-0x8148c  t[96] in scope: 12 shadow bytes of F+0x20 := 0
     0x81490          beqz s6 -> 0x81d58: no input byte left for c (s10 := s2, j 0x81500)
     0x81494-0x8149c  the trap test of c's read (`addi a0,s2,1; bltu a6,a0`, trap 0x81498)
     0x814a0-0x814b0  c = fuzz_u8: the shadow check of the cursor (slow block 0x82270), a3 := c (`lbu` 0x814b0)
     0x814b4-0x814bc  a0 := s10 + 2; bne t1, 2 -> 0x81d90: a byte is left for p
     0x814c0-0x814cc  no byte for p: R+0x128 := s10 + 2, t1 := 0, s9 := 0, j 0x81dbc
     0x81d90-0x81db8  p = fuzz_u8: the trap test (0x81d94), the shadow check (slow block 0x82314), s9 := p,
                      s10 := s10 + 3, t1 := t1 - 3, R+0x128 := s10
     0x81dbc-0x81ddc  ch[24] in scope: 3 shadow bytes of F+0xa0 := 0; s2 := [R+0xe0] = &ch, t0 := 4, t2 := 10,
                      t3 := 9; bgeu 199, a3 -> DIG (c < 200), else ODD
     0x814d0-0x814fc  D0E: t in scope, then
     0x81500-0x81528  (also from 0x81d58) t1 := 0, s9 := 0, a3 := 0, ch in scope, R+0x128 := s10, s2 := [R+0xe0],
                      t0 := 4, t2 := 10, t3 := 9; falls into DIG
     0x8152c-0x81608  DIG, c < 200: the digits of c mod 64 into r[4] (r into scope 0x81534 with shadow byte 0x04;
                      the bound trap 0x81540; the store's check takes its slow block 0x8159c inline), reversed into
                      ch (the read's check, slow block 0x815e0 inline), the NUL's trap 0x815f8 and its store, r out
                      of scope again (0x81608)
     0x81de0-0x81e50  ODD, c >= 200: odd_ch[c mod 14] (the pointer table ent_headamp_key.odd_ch 0x9be40 in
                      .data.rel.ro; the trap 0x81e0c; its 8-byte load is checked by `lbu; beqz +8; j` 0x81e20-0x81e28),
                      the strlen wrapper (0x421ec), __asan_memcpy (0x518b8) into ch, t1 back from s8, j G
   So the piece is three blocks: the head (D0 -> DIG / ODD, D0E -> DIG), DIG (-> G) and ODD (-> G). On every arm
   t1 = what is left of the input, s2 = &ch, s9 = p and R+0x128 the cursor, which G also carries. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ===================================== the two inner pcs ===================================== *)
Definition RT7B_DIG : Z := 0x8152c.   (* the digits of c mod 64, c < 200 (`li a2,0`) *)
Definition RT7B_ODD : Z := 0x81de0.   (* odd_ch[c mod 14], c >= 200 (`auipc a1`) *)

(* The instruction table of the piece: the straight range D0 .. G (107 words, the digit and reverse loops' slow
   blocks 0x8159c and 0x815e0 among them), the head's and ODD's out-of-line range 0x81d58 .. 0x81e54 (63 words;
   0x81d60 .. 0x81d8c is case 8's, never reached from here) and the two out-of-line slow blocks the head's checks
   branch to (`andi u,x,7; blt u,t,<back>; j <report>`): c's read 0x82270, p's read 0x82314. The token engine must
   decode them. *)
Definition rt7b_tbl : ctable :=
  build_table rsegs 0x81460 107
  (build_table rsegs 0x81d58 63
  (build_table rsegs 0x82270 3
  (build_table rsegs 0x82314 3 TEmpty))).
Lemma rt7b_tbl_ok : table_ok rsegs rt7b_tbl.
Proof.
unfold rt7b_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.

(* The frame's shadow rows at the pcs of the piece, in RtPgMemB's words (the flags t ch r e e42 e62 hz; e62 is in
   scope from the pod loop's stores 0x813a4 .. 0x813d4 and closes only after J). RtPgSegB.rsb_PJ (at D0 / D0E) and
   rsb_PG (at DIG / ODD / G) are these words by definition. *)
(* after the t stores and before the ch stores *)
Definition rt7b_PT : list Z := rtmb_sh true false false false false true false.
(* inside the digit and the reverse loops r is in scope as well (shadow byte 0x04, 0x81534) *)
Definition rt7b_PR : list Z := rtmb_sh true true true false false true false.

(* What case 0 reads of the turn's input before the two arms: the kind byte, then c and p (pod.h:234); on an
   empty input fuzz_u8 gives 0 and does not move the cursor (fuzz.h:37-43). RtPgSegB.rsb_g_of is this with the
   channel text of c in place of c. *)
Definition rt7b_cp_of (rr : list byte) : Z * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(c, pb, r3).
Lemma rt7b_g_of_cp : forall rr c pb r3,
(c, pb, r3) = rt7b_cp_of rr ->
rsb_g_of rr = (if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Proof.
intros rr c pb r3 H. unfold rsb_g_of, rt7b_cp_of in *.
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
   RtPgSegB.rsb_L_Dc (rsb_L_Dc0 and s8 = -8, the byte DIG's 0x81608 stores to close r) and the four values case 0
   holds at both arms and at G: t1 = what is left of the input, s2 = &ch, s9 = the key's second input byte p, and
   the cursor in the cell R+0x128. *)
Definition rt7b_L_arm (cx : rsb_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (pb : Z) : list (rt_loc * Z) :=
rsb_L_Dc segs cx sh np ps cnt es
++ [(LReg 6, Z.of_nat (length r)); (LReg 18, q_F (x_e segs cx) + 0xa0); (LReg 25, pb);
    (LCell XR 0x128, rsb_cur segs cx rest r)].

(* ---------------- DIG = 0x8152c: the digits arm, c < 200 ----------------
   t and ch are in scope and r is not yet (its granule opens at 0x81534), so the frame's shadow row is
   RtPgSegB.rsb_PG, the row G also has. a3 = c, t0 = 4, t2 = 10 and t3 = 9 are the digit loop's four values
   (0x814b0 / 0x81508, 0x81dcc / 0x81520, 0x81dd0 / 0x81524, 0x81dd4 / 0x81528); the `v / 10` multiplier is s5
   (rsb_Rc0). *)
Definition rt7b_cut_DIG (cx : rsb_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx segs cx W2 mem2 regs2
(rt7b_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 13, c); (LReg 5, 4); (LReg 7, 10); (LReg 28, 9)]) /\
rsb_fsh_at segs cx W2 mem2 rsb_PG /\
rsb_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e segs cx) + 0x210) (rsb_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = rt7b_cp_of rr /\
0 <= c < 200 /\ 0 <= pb < 256.

(* ---------------- ODD = 0x81de0: the table arm, c >= 200 ----------------
   The same row and the same four values; a3 = c. *)
Definition rt7b_cut_ODD (cx : rsb_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx segs cx W2 mem2 regs2
(rt7b_L_arm cx sh np ps cnt es rest r pb ++ [(LReg 13, c)]) /\
rsb_fsh_at segs cx W2 mem2 rsb_PG /\
rsb_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e segs cx) + 0x210) (rsb_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = rt7b_cp_of rr /\
200 <= c < 256 /\ 0 <= pb < 256.

(* ===================== the continuations of the two inner cuts ===================== *)
Section f.
Variable cx : rsb_scx segs.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.
Definition rt7b_from_DIG (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
rt7b_cut_DIG cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RT7B_DIG regs2 mem2 md2) POST.
Definition rt7b_from_ODD (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
rt7b_cut_ODD cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RT7B_ODD regs2 mem2 md2) POST.
End f.

(* ===================== the three block statements of the piece ===================== *)
(* the digits arm: from DIG to G, with the channel text dec64 (c mod 64) in ch *)
Definition rt7b_dig_stmt : Prop :=
forall cx POST rest i k,
rsb_start_M01 segs B cx rest -> rsb_from_G segs B MT cx POST rest i k ->
rt7b_from_DIG cx POST rest i k.
(* the table arm: from ODD to G, with odd_ch[c mod 14] in ch (the strlen wrapper and __asan_memcpy) *)
Definition rt7b_odd_stmt : Prop :=
forall cx POST rest i k,
rsb_start_M01 segs B cx rest -> rsb_from_G segs B MT cx POST rest i k ->
rt7b_from_ODD cx POST rest i k.
(* the head: both entries of case 0 to the two arms *)
Definition rt7b_head_stmt : Prop :=
forall cx POST rest i k kd,
rsb_start_M01 segs B cx rest -> kd mod 10 = 0 ->
rt7b_from_DIG cx POST rest i k -> rt7b_from_ODD cx POST rest i k ->
rsb_from_D segs B MT cx POST rest i k kd /\ rsb_from_D0E segs B MT cx POST rest i k.

(* ===================== the piece: RtPgSegB.rsb_piece_W7a_stmt from the three blocks ===================== *)
Lemma rt7b_piece : rt7b_head_stmt -> rt7b_dig_stmt -> rt7b_odd_stmt -> rsb_piece_W7a_stmt segs B MT.
Proof.
intros HH HD HO cx POST rest i k kd Hst Hkd HG.
exact (HH cx POST rest i k kd Hst Hkd (HD cx POST rest i k Hst HG) (HO cx POST rest i k Hst HG)).
Qed.

End d.
End c.
End b.

Print Assumptions rt7b_tbl_ok.
Print Assumptions rt7b_g_of_cp.
Print Assumptions rt7b_piece.
