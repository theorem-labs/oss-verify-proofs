(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its numbers changed; 208 of its 242 lines of code are new or changed and 232 lines of the source are left out. *)
(* Segment RD9 (SCRIBBLE) of the image-A walk of LLVMFuzzerTestOneInput: seg_rd_run 9 of
   lib/A/Prog/codec_amain_inv.v, from the reader cut at 0x80dc8 to RUN 0x820d0. k.a = fuzz_u32, then
   k.bytes[0 .. 8) = fuzz_u8 each (fuzz_codec.c: case SCRIBBLE).
   The code: 0x80dc8 ld in.n; beqz -> 0x812cc (no byte); 0x80dd0 .. 0x80df8 byte 0 (check slow path behind
   `j 0x82b8c`); 0x80dfc beqz in.n - 1 -> 0x81424; 0x80e00 .. 0x80e24 byte 1 (slow path 0x82cac), j 0x81428;
   0x81428 ld in.n, beqz -> 0x81490; 0x81430 .. 0x81458 byte 2 (slow path 0x82cd0); 0x8145c beqz in.n - 3 -> 0x81494;
   0x81460 .. 0x81484 byte 3 (slow path 0x82ee0); 0x81498 .. 0x814b0 the bytes composed, sw k.a; a1 = 8,
   a3 = &k.bytes (spill 88(sp1)); the loop 0x814bc .. 0x814fc: beqz in.n - j -> 0x814ec (a missing byte reads 0),
   else byte j (check inline, slow path 0x81504), sb, a1 - 1, a3 + 1, bnez a1; j RUN.
   The state is codec_amain_rdlib.v's rd_ss with the k window [24, 48) (k.a and the first 8 bytes); b, c and delta
   lie inside the window and are not written, so the window starts with their HEAD zeros as chunks (rd9_cs) and the
   end reads them back. The twelve bytes are the atoms 37 .. 48 (input bytes c .. c + 11). Each byte's check leaves
   one obligation, paid by the input block (codec_amain_rdin.v rd_obl); each byte's load reads the 1-byte region
   rd_in_add puts at the cursor after its in.n test; the engine records each in.n test's condition, so once the
   bytes ran out every later test is decided: thirteen paths by the bytes taken. The walk keeps one bound
   c + j <= e_n g in place of the tests' disequalities. The cut needs only 0 <= k.a < 2^32 of the stored word. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st CPgTokJ codec_amain_rdlib codec_amain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rd10.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition rd9_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
 (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
 (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0)].
(* b (k + 28), c (k + 32) and delta (k + 36), inside the window, as HEAD left them *)
Definition rd9_cs : list YP09.chunk :=
[YP09.mkChunk 204 (CVal 4 (SLit 0)); YP09.mkChunk 208 (CVal 4 (SLit 0)); YP09.mkChunk 212 (CVal 4 (SLit 0))].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* RUN: k.a is the word stored at 24 (its u32 value), the bytes the eight 1-byte values stored at 40 .. 48; b, c and
   delta read back from their chunks *)
Ltac rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in
  let Cy := fresh "Cy" in let Cc := fresh "Cc" in let Cd := fresh "Cd" in
  let Y0 := fresh "Y0" in let Y1 := fresh "Y1" in let Y2 := fresh "Y2" in let Y3 := fresh "Y3" in
  let Y4 := fresh "Y4" in let Y5 := fresh "Y5" in let Y6 := fresh "Y6" in let Y7 := fresh "Y7" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb; rd_chunk HS 33%nat 200 Cx;
  rd_chunk HS 33%nat 204 Cy; rd_chunk HS 33%nat 208 Cc; rd_chunk HS 33%nat 212 Cd;
  rd_chunk HS 33%nat 216 Y0; rd_chunk HS 33%nat 217 Y1; rd_chunk HS 33%nat 218 Y2; rd_chunk HS 33%nat 219 Y3;
  rd_chunk HS 33%nat 220 Y4; rd_chunk HS 33%nat 221 Y5; rd_chunk HS 33%nat 222 Y6; rd_chunk HS 33%nat 223 Y7;
  rewrite ?ew_ewset_other in Cx, Cy, Cc, Cd, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7 by lia;
  rewrite B33 in Cx, Cy, Cc, Cd, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 200 (CVal 4 ?va)) =>
  lazymatch type of Y0 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 216 (CVal 1 ?y0)) =>
  lazymatch type of Y1 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 217 (CVal 1 ?y1)) =>
  lazymatch type of Y2 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 218 (CVal 1 ?y2)) =>
  lazymatch type of Y3 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 219 (CVal 1 ?y3)) =>
  lazymatch type of Y4 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 220 (CVal 1 ?y4)) =>
  lazymatch type of Y5 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 221 (CVal 1 ?y5)) =>
  lazymatch type of Y6 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 222 (CVal 1 ?y6)) =>
  lazymatch type of Y7 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 223 (CVal 1 ?y7)) =>
  eapply (rd_endk B MT K XM_LIB LAWS g pos sp1 ops 24 48 c ys ly2 S2 W2 regs2 mem2 md2 k 9 pv dv od Ef ssf msf _ j
    (bv_unsigned (sv_denot Ef va) mod 2 ^ 32) 0 0 0
    (map (fun x => x mod 256) [bv_unsigned (sv_denot Ef y0); bv_unsigned (sv_denot Ef y1); bv_unsigned (sv_denot Ef y2);
       bv_unsigned (sv_denot Ef y3); bv_unsigned (sv_denot Ef y4); bv_unsigned (sv_denot Ef y5);
       bv_unsigned (sv_denot Ef y6); bv_unsigned (sv_denot Ef y7)] ++ repeat 0 16)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ unfold codec_owe.reader_ok;
    split; [apply rd_u32_range|]; split; [lia|]; split; [lia|]; split; [lia|];
    split; [reflexivity|];
    split; [apply Forall_app; split;
            [ cbn [map]; repeat (apply Forall_cons; [apply Z.mod_pos_bound; lia|]); apply Forall_nil
            | apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia ]|];
    split; [lia|]; split; [intros; discriminate|]; split; intros; discriminate
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 24) 4 _ => replace (F + 176 + 24) with (F + 200) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cx)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 28) 4 _ => replace (F + 176 + 28) with (F + 204) by lia end;
    exact (rd_chunk_lit0 _ _ _ _ 4 Cy)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 32) 4 _ => replace (F + 176 + 32) with (F + 208) by lia end;
    exact (rd_chunk_lit0 _ _ _ _ 4 Cc)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 36) 4 _ => replace (F + 176 + 36) with (F + 212) by lia end;
    exact (rd_chunk_lit0 _ _ _ _ 4 Cd)
  | apply (rd_bytes8 g pos sp1 24 48 W2 mem2 _ 9 pv dv _ _ _ _ _ _ _ _ Hkat KE); [lia | lia | lia | lia | lia
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y0) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y1)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y2) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y3)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y4) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y5)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y6) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y7) ] ]
  end end end end end end end end end
end.

Theorem seg_rd9_holds : seg_rd_run B MT K XM_LIB 9.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R23 & Hkat).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold AM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C152 & C160).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
set (ys := [rd_ib g c; rd_ib g (c + 1); rd_ib g (c + 2); rd_ib g (c + 3); rd_ib g (c + 4); rd_ib g (c + 5);
  rd_ib g (c + 6); rd_ib g (c + 7); rd_ib g (c + 8); rd_ib g (c + 9); rd_ib g (c + 10); rd_ib g (c + 11)]).
assert (HAF : atoms_ok (am_env g pos c regs2 ys) rd9_AF).
{ unfold rd9_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (am_ew_y g pos c regs2 ys 0) as Y0. pose proof (am_ew_y g pos c regs2 ys 1) as Y1.
  pose proof (am_ew_y g pos c regs2 ys 2) as Y2. pose proof (am_ew_y g pos c regs2 ys 3) as Y3.
  pose proof (am_ew_y g pos c regs2 ys 4) as Y4. pose proof (am_ew_y g pos c regs2 ys 5) as Y5.
  pose proof (am_ew_y g pos c regs2 ys 6) as Y6. pose proof (am_ew_y g pos c regs2 ys 7) as Y7.
  pose proof (am_ew_y g pos c regs2 ys 8) as Y8. pose proof (am_ew_y g pos c regs2 ys 9) as Y9.
  pose proof (am_ew_y g pos c regs2 ys 10) as Y10. pose proof (am_ew_y g pos c regs2 ys 11) as Y11.
  unfold AM_X0 in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11.
  cbn [Nat.add] in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11.
  rewrite Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)).
  pose proof (rd_ib_range g (c + 2)). pose proof (rd_ib_range g (c + 3)).
  pose proof (rd_ib_range g (c + 4)). pose proof (rd_ib_range g (c + 5)).
  pose proof (rd_ib_range g (c + 6)). pose proof (rd_ib_range g (c + 7)).
  pose proof (rd_ib_range g (c + 8)). pose proof (rd_ib_range g (c + 9)).
  pose proof (rd_ib_range g (c + 10)). pose proof (rd_ib_range g (c + 11)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
assert (HCS : Forall (YP09.chunk_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) rd9_cs).
{ pose proof Hkat as ((_ & _ & _ & _ & Vb & Vc & Vd & _) & _). cbn [kz_b kz_c kz_delta k_rdZ] in Vb, Vc, Vd.
  unfold rd9_cs. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 204 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact Vb.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 208 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 208) with (FA g pos + 176 + 32) by lia. exact Vc.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 212 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 212) with (FA g pos + 176 + 36) by lia. exact Vd. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd9_AF (rd_pc 9) 24 48 rd9_cs
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) HCS eq_refl HAF) as [HS SHOK].
clear HCS.
assert (HAE : env_agree 41 (am_env g pos c regs2 ys) (am_env g pos c regs2 ys)) by apply env_agree_refl.
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (subst E; rewrite (am_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (am_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (am_ew_SB g pos c regs2 ys)).
assert (EY0 : ew E 37 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 0))) by (subst E; rewrite Z.add_0_r; exact (am_ew_y g pos c regs2 ys 0)).
assert (EY1 : ew E 38 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 1))) by (subst E; exact (am_ew_y g pos c regs2 ys 1)).
assert (EY2 : ew E 39 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 2))) by (subst E; exact (am_ew_y g pos c regs2 ys 2)).
assert (EY3 : ew E 40 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 3))) by (subst E; exact (am_ew_y g pos c regs2 ys 3)).
assert (EY4 : ew E 41 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 4))) by (subst E; exact (am_ew_y g pos c regs2 ys 4)).
assert (EY5 : ew E 42 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 5))) by (subst E; exact (am_ew_y g pos c regs2 ys 5)).
assert (EY6 : ew E 43 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 6))) by (subst E; exact (am_ew_y g pos c regs2 ys 6)).
assert (EY7 : ew E 44 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 7))) by (subst E; exact (am_ew_y g pos c regs2 ys 7)).
assert (EY8 : ew E 45 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 8))) by (subst E; exact (am_ew_y g pos c regs2 ys 8)).
assert (EY9 : ew E 46 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 9))) by (subst E; exact (am_ew_y g pos c regs2 ys 9)).
assert (EY10 : ew E 47 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 10))) by (subst E; exact (am_ew_y g pos c regs2 ys 10)).
assert (EY11 : ew E 48 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 11))) by (subst E; exact (am_ew_y g pos c regs2 ys 11)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 48 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 360 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hcm : c + 0 <= e_n g) by lia.
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 9)) with (Z_to_bv 64 0x80dc8). change (rd_pc 9) with 0x80dc8 in HS.
(* 0x80dc8 ld a3, in.n; to the test at 0x80dcc *)
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
(* in.n = 0: no byte (0x812cc, 0x81490), k.a = 0, the eight bytes 0 (every later test decided) *)
cw_branch Hb0; rd10_brn Hb0 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 0
  | ].
(* byte 0: 0x80dd0 .. 0x80df8, to the test of in.n - 1 at 0x80dfc *)
rd_bump Hb0 Hcm. rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd10_brn Hb1 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 1
  | ].
(* byte 1: 0x80e00 .. 0x80e24, j 0x81428, to the test of in.n - 2 at 0x8142c *)
rd_bump Hb1 Hcm. rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb2; rd10_brn Hb2 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 2
  | ].
(* byte 2: 0x81430 .. 0x81458, to the test of in.n - 3 at 0x8145c *)
rd_bump Hb2 Hcm. rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb3; rd10_brn Hb3 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 3
  | ].
(* byte 3: 0x81460 .. 0x81484, sw k.a, to the loop test of in.n - 4 at 0x814bc *)
rd_bump Hb3 Hcm. rd_in_add LAWS HJ0 Hfr HC c 3%nat E35 EY3 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb4; rd10_brn Hb4 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 4
  | ].
(* byte 4 (k.bytes[0]): the loop body, to the test of in.n - 5 *)
rd_bump Hb4 Hcm. rd_in_add LAWS HJ0 Hfr HC c 4%nat E35 EY4 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb5; rd10_brn Hb5 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 5
  | ].
(* byte 5 (k.bytes[1]) *)
rd_bump Hb5 Hcm. rd_in_add LAWS HJ0 Hfr HC c 5%nat E35 EY5 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb6; rd10_brn Hb6 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 6
  | ].
(* byte 6 (k.bytes[2]) *)
rd_bump Hb6 Hcm. rd_in_add LAWS HJ0 Hfr HC c 6%nat E35 EY6 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb7; rd10_brn Hb7 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 7
  | ].
(* byte 7 (k.bytes[3]) *)
rd_bump Hb7 Hcm. rd_in_add LAWS HJ0 Hfr HC c 7%nat E35 EY7 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb8; rd10_brn Hb8 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 8
  | ].
(* byte 8 (k.bytes[4]) *)
rd_bump Hb8 Hcm. rd_in_add LAWS HJ0 Hfr HC c 8%nat E35 EY8 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb9; rd10_brn Hb9 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 9
  | ].
(* byte 9 (k.bytes[5]) *)
rd_bump Hb9 Hcm. rd_in_add LAWS HJ0 Hfr HC c 9%nat E35 EY9 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb10; rd10_brn Hb10 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 10
  | ].
(* byte 10 (k.bytes[6]) *)
rd_bump Hb10 Hcm. rd_in_add LAWS HJ0 Hfr HC c 10%nat E35 EY10 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb11; rd10_brn Hb11 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 11
  | ].
(* byte 11 (k.bytes[7]), the loop's last pass, j RUN *)
rd_bump Hb11 Hcm. rd_in_add LAWS HJ0 Hfr HC c 11%nat E35 EY11 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
rd9_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 12.
Qed.

End b.
End a.
