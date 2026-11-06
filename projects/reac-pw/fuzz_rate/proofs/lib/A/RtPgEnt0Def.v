(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Def.v at 27540f54413f for reac-pw/fuzz_rate's image A; rate's pcs (the head's two out-of-line blocks 0x81b38 and 0x81b58, the arms DIG 0x813f8 and ODD 0x81b6c), registers (in.n in s10, &ch in s6, the `v / 10` multiplier in t2) and code table; the frame's shadow rows in RtPgMem's seven-flag words; the piece lemma rt7_piece from the three block statements. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the two inner cut states of
   ent_build's case-0 head, the statements of its three blocks and the piece lemma W7a from them. Proves no
   function (kind: statement text).

   THE CODE (pod.h:224-249, ent_headamp_key up to the end of the channel text ch). The piece runs from the jump
   table's case-0 target D0 = 0x81334, or from D0E = 0x813a0 when no input byte is left, to G = 0x8150c, where the
   parts begin (lib/A/RtPgSeg.v rs_cut_D, rs_cut_D0E, rs_cut_G). At D0, s9 is the cursor after the kind byte, a4 the
   kind byte's address, s8 what is left after it and a5 = s8 + 1; s4 = shadow_addr F, s2 the shadow offset.
     0x81334-0x81360  t[96] in scope: 12 shadow bytes of F+0x20 := 0
     0x81364          beqz s8 -> 0x81bcc: no input byte left for c (s6 := [R+0x98], j 0x813d8)
     0x81368-0x81380  c = fuzz_u8: the shadow check of the cursor (slow block 0x82148), s6 := [R+0x98] = &ch,
                      t0 := 9, t2 := [R+0x90] (the `v / 10` multiplier)
     0x81384-0x81390  a0 := c, s9 := a4 + 2; bne a5, 2 -> 0x81b38: a byte is left for p
     0x81394-0x8139c  no byte for p: s10 := 0, s11 := 0, j 0x81b58
     0x81b38-0x81b54  p = fuzz_u8: s10 := a5, the shadow check (slow block 0x821fc), s11 := p, s9 := a4 + 3,
                      s10 := a5 - 3
     0x81b58-0x81b68  ch[24] in scope: 3 shadow bytes of F+0xa0 := 0; bgeu 0xc7, c -> DIG (c < 200), else ODD
     0x813a0-0x813d4  D0E: t in scope, s6 := [R+0x98], a7 := 10, then
     0x813d8-0x813f4  (also from 0x81bcc) t0 := 9, t2 := [R+0x90], s10 := 0, s11 := 0, a0 := 0, ch in scope
     0x813f8-0x81508  DIG, c < 200: the digits of c mod 64 into r[4] (shadow 0x04 at 0x81404), reversed into ch
                      (slow blocks 0x81460, 0x814cc, 0x814d8 inline), its NUL (slow block 0x8212c), r out of scope
                      again (0x81508)
     0x81b6c-0x81bc8  ODD, c >= 200: odd_ch[c mod 14] (the pointer table ent_headamp_key.odd_ch 0x9bb40 in
                      .data.rel.ro; its 8-byte load is checked by `lbu; beqz +8; j` 0x81ba0-0x81ba8), the strlen
                      wrapper (0x42194), __asan_memcpy (0x51860) into ch, j G
   So the piece is three blocks: the head (D0 -> DIG / ODD, D0E -> DIG), DIG (-> G) and ODD (-> G). On every arm
   s10 = what is left of the input, s9 the cursor, s11 = p and s6 = &ch, which G also carries. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ===================================== the two inner pcs ===================================== *)
Definition RT7_DIG : Z := 0x813f8.   (* the digits of c mod 64, c < 200 *)
Definition RT7_ODD : Z := 0x81b6c.   (* odd_ch[c mod 14], c >= 200 *)

(* The instruction table of the piece: the straight range D0 .. G, the head's and ODD's out-of-line range
   0x81b38 .. 0x81bd0, and the three out-of-line slow blocks its checks branch to (`andi u,x,7; blt u,t,<back>;
   j <report>`): the NUL store 0x8212c, c's read 0x82148, p's read 0x821fc. The token engine must decode them. *)
Definition rt7_tbl : ctable :=
  build_table rsegs 0x81334 118
  (build_table rsegs 0x81b38 39
  (build_table rsegs 0x8212c 3
  (build_table rsegs 0x82148 3
  (build_table rsegs 0x821fc 3 TEmpty)))).
Lemma rt7_tbl_ok : table_ok rsegs rt7_tbl.
Proof.
unfold rt7_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.

(* The frame's shadow row at the pcs of the piece, in RtPgMem's words (the flags t ch r e hz asked[0] asked[1];
   e is in scope from the pod loop's stores 0x81280 .. 0x812b0 and closes only after J). *)
Lemma rt7_PJ_sh : rs_PJ = rtm_sh false false false true false false false.
Proof. vm_compute. reflexivity. Qed.
Lemma rt7_PG_sh : rs_PG = rtm_sh true true false true false false false.
Proof. vm_compute. reflexivity. Qed.
(* inside the digits and the reverse loop r is in scope as well (shadow byte 0x04, 0x81404) *)
Definition rt7_PR : list Z := rtm_sh true true true true false false false.
(* after the t stores and before the ch stores *)
Definition rt7_PT : list Z := rtm_sh true false false true false false false.

(* What case 0 reads of the turn's input before the two arms: the kind byte, then c and p (pod.h:234); on an
   empty input fuzz_u8 gives 0 and does not move the cursor (fuzz.h:37-43). RtPgSeg.rs_g_of is this with the
   channel text of c in place of c. *)
Definition rt7_cp_of (rr : list byte) : Z * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(c, pb, r3).
Lemma rt7_g_of_cp : forall rr c pb r3,
(c, pb, r3) = rt7_cp_of rr ->
rs_g_of rr = (if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Proof.
intros rr c pb r3 H. unfold rs_g_of, rt7_cp_of in *.
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
   RtPgSeg.rs_L_Dc0 and the four values case 0 holds at both arms and at G: s10 = what is left of the input,
   s6 = &ch, s11 = the key's second input byte p, s9 = the cursor. *)
Definition rt7_L_arm (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (pb : Z) : list (rt_loc * Z) :=
rs_L_Dc0 segs cx sh np ps cnt es
++ [(LReg 26, Z.of_nat (length r)); (LReg 22, q_F (x_e segs cx) + 0xa0); (LReg 27, pb);
    (LReg 25, rs_cur segs cx rest r)].

(* ---------------- DIG = 0x813f8: the digits arm, c < 200 ----------------
   t and ch are in scope and r is not yet (its granule opens at 0x81404), so the frame's shadow row is
   RtPgSeg.rs_PG, the row G also has. a0 = c, a7 = 10, t0 = 9 and t2 = the `v / 10` multiplier are the digit
   loop's four values (0x81384 / 0x813e8, 0x812f0 / 0x813d4, 0x81378 / 0x813d8, 0x8137c / 0x813dc). *)
Definition rt7_cut_DIG (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx segs cx W2 mem2 regs2
(rt7_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 10, c); (LReg 17, 10); (LReg 5, 9); (LReg 7, RS_MULT10)]) /\
rs_fsh_at segs cx W2 mem2 rs_PG /\
rs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e segs cx) + 0xf0) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = rt7_cp_of rr /\
0 <= c < 200 /\ 0 <= pb < 256.

(* ---------------- ODD = 0x81b6c: the table arm, c >= 200 ----------------
   The same row and the same four values; a0 = c. *)
Definition rt7_cut_ODD (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx segs cx W2 mem2 regs2
(rt7_L_arm cx sh np ps cnt es rest r pb ++ [(LReg 10, c)]) /\
rs_fsh_at segs cx W2 mem2 rs_PG /\
rs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e segs cx) + 0xf0) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = rt7_cp_of rr /\
200 <= c < 256 /\ 0 <= pb < 256.

(* ===================== the continuations of the two inner cuts ===================== *)
Section f.
Variable cx : rs_scx segs.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.
Definition rt7_from_DIG (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
rt7_cut_DIG cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RT7_DIG regs2 mem2 md2) POST.
Definition rt7_from_ODD (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
rt7_cut_ODD cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RT7_ODD regs2 mem2 md2) POST.
End f.

(* ===================== the three block statements of the piece ===================== *)
(* the digits arm: from DIG to G, with the channel text dec64 (c mod 64) in ch *)
Definition rt7_dig_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 segs B cx rest -> rs_from_G segs B MT cx POST rest i k ->
rt7_from_DIG cx POST rest i k.
(* the table arm: from ODD to G, with odd_ch[c mod 14] in ch (the strlen wrapper and __asan_memcpy) *)
Definition rt7_odd_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 segs B cx rest -> rs_from_G segs B MT cx POST rest i k ->
rt7_from_ODD cx POST rest i k.
(* the head: both entries of case 0 to the two arms *)
Definition rt7_head_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 segs B cx rest -> kd mod 10 = 0 ->
rt7_from_DIG cx POST rest i k -> rt7_from_ODD cx POST rest i k ->
rs_from_D segs B MT cx POST rest i k kd /\ rs_from_D0E segs B MT cx POST rest i k.

(* ===================== the piece: RtPgSeg.rs_piece_W7a_stmt from the three blocks ===================== *)
Lemma rt7_piece : rt7_head_stmt -> rt7_dig_stmt -> rt7_odd_stmt -> rs_piece_W7a_stmt segs B MT.
Proof.
intros HH HD HO cx POST rest i k kd Hst Hkd HG.
exact (HH cx POST rest i k kd Hst Hkd (HD cx POST rest i k Hst HG) (HO cx POST rest i k Hst HG)).
Qed.

End d.
End c.
End b.

Print Assumptions rt7_tbl_ok.
Print Assumptions rt7_PG_sh.
Print Assumptions rt7_g_of_cp.
Print Assumptions rt7_piece.
