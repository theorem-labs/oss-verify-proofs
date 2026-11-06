(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v; 142 of its 173 lines of code are new or changed and 235 lines of the source are left out. *)
(* Segment RD6 (METER) of the image-A walk of LLVMFuzzerTestOneInput: seg_rd_run 6 of
   lib/A/Prog/codec_amain_inv.v, from the reader cut at 0x8109c to RUN 0x820d0. k.a, k.c, k.b = fuzz_u32 in this
   order (fuzz_codec.c: case METER), stored at 24(s6) (0x81e9c), 32(s6) (0x81f88) and 28(s6) (0x820cc).
   The code: 0x8109c ld in.n; beqz -> 0x81318 (no byte); 0x810a4 .. 0x810cc byte 0 (check slow path behind
   `j 0x82be0`); 0x810d0 beqz in.n - 1 -> 0x81e14; 0x810d4 .. 0x810f8 byte 1, j 0x81e18; 0x81e18 ld in.n, beqz ->
   0x81e80; 0x81e20 .. 0x81e48 byte 2; 0x81e4c beqz in.n - 3 -> 0x81e84; 0x81e50 .. 0x81e74 byte 3; 0x81e88 ..
   0x81e9c k.a composed and stored; 0x81e8c ld in.n, 0x81ea0 beqz -> 0x81efc; 0x81ea4 .. 0x81ec8 byte 4 (check
   inline); 0x81ecc beqz in.n - 5 -> 0x81f04; 0x81ed0 .. 0x81ef0 byte 5; 0x81f08 ld in.n, beqz -> 0x81f6c;
   0x81f10 .. 0x81f34 byte 6; 0x81f38 beqz in.n - 7 -> 0x81f70; 0x81f3c .. 0x81f60 byte 7; 0x81f74 .. 0x81f88 k.c
   composed and stored; 0x81f78 ld in.n, 0x81f8c beqz -> 0x81fe8; 0x81f90 .. 0x81fb4 byte 8; 0x81fb8 beqz in.n - 9
   -> 0x81ff8; 0x81fbc .. 0x81fdc byte 9; 0x81ffc ld in.n, beqz -> 0x81fec; 0x82004 .. 0x82028 byte 10; 0x8202c
   beqz in.n - 11 -> 0x81ff0; 0x82030 .. 0x820b4 byte 11 (check inline, 0x82048 .. 0x82054); 0x820bc .. 0x820cc
   k.b composed and stored; RUN.
   The state is codec_amain_rdlib.v's rd_ss with the k window [24, 36); the twelve bytes are the atoms 37 .. 48
   (input bytes c .. c + 11). Each byte's check leaves one obligation, paid by the input block (codec_amain_rdin.v
   rd_obl); each byte's load reads the 1-byte region rd_in_add puts at the cursor after its in.n test; the engine
   records each branch's condition, so an in.n test repeated after the bytes ran out is decided, and the branch
   tree is a comb of 13 leaves (0 .. 12 bytes taken). After a test with in.n - j <> 0 the walk keeps the linear
   fact 0 < in.n - j instead, so lia never splits a disequality. The cut needs only 0 <= k.a, k.b, k.c < 2^32 of
   the stored words. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition rd6_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
 (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
 (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0)].

(* the run to the next stop (an undecided branch or RUN 0x820d0), its input-byte obligation closed *)
Ltac rd6_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 532688; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z; the case in.n - j <> 0 as 0 < in.n - j *)
Ltac rd6_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [ apply Z.eqb_eq in Hb
      | apply Z.eqb_neq in Hb;
        lazymatch type of Hb with ?x <> 0 => let H := fresh "Hlt" in assert (H : 0 < x) by lia; clear Hb end ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* RUN: k.a / k.b / k.c are the words stored at 24 / 28 / 32 (their u32 values), delta / bytes still HEAD's zeros *)
Ltac rd6_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in let Cy := fresh "Cy" in let Cz := fresh "Cz" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb;
  rd_chunk HS 33%nat 200 Cx; rd_chunk HS 33%nat 204 Cy; rd_chunk HS 33%nat 208 Cz;
  rewrite ?ew_ewset_other in Cx, Cy, Cz by lia; rewrite B33 in Cx, Cy, Cz;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 200 (CVal 4 ?va)) =>
  lazymatch type of Cy with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 204 (CVal 4 ?vb)) =>
  lazymatch type of Cz with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 208 (CVal 4 ?vc)) =>
  eapply (rd_endk B MT K XM_LIB LAWS g pos sp1 ops 24 36 c ys ly2 S2 W2 regs2 mem2 md2 k 6 pv dv od Ef ssf msf _ j
    (bv_unsigned (sv_denot Ef va) mod 2 ^ 32) (bv_unsigned (sv_denot Ef vb) mod 2 ^ 32)
    (bv_unsigned (sv_denot Ef vc) mod 2 ^ 32) 0 (repeat 0 24)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ unfold codec_owe.reader_ok; rewrite repeat_length;
    split; [apply rd_u32_range|]; split; [apply rd_u32_range|]; split; [apply rd_u32_range|]; split; [lia|];
    split; [reflexivity|]; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|];
    split; [lia|]; split; [intros; discriminate|]; split; intros; discriminate
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 24) 4 _ => replace (F + 176 + 24) with (F + 200) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cx)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 28) 4 _ => replace (F + 176 + 28) with (F + 204) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cy)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 32) 4 _ => replace (F + 176 + 32) with (F + 208) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cz)
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 6 pv dv 24 36 36 Hkat); first [exact KE | lia]
  | destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _); cbn [kz_bytes k_rdZ] in Vy;
    apply (rd_garr8_kept_k g pos sp1 24 36 W2 mem2 _ 40 (repeat 0 24) KE); [lia | lia | lia | lia | rewrite repeat_length; cbn; lia
      | rewrite repeat_length; cbn; lia | exact Vy] ]
  end end end
end.
(* a leaf: the run to RUN (the in.n tests left are decided) and the end *)
Ltac rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
rd6_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j.

Theorem seg_rd6_holds : seg_rd_run B MT K XM_LIB 6.
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
set (ys := [rd_ib g c; rd_ib g (c + 1); rd_ib g (c + 2); rd_ib g (c + 3); rd_ib g (c + 4); rd_ib g (c + 5); rd_ib g (c + 6); rd_ib g (c + 7); rd_ib g (c + 8); rd_ib g (c + 9); rd_ib g (c + 10); rd_ib g (c + 11)]).
assert (HAF : atoms_ok (am_env g pos c regs2 ys) rd6_AF).
{ unfold rd6_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (am_ew_y g pos c regs2 ys 0) as Y0. pose proof (am_ew_y g pos c regs2 ys 1) as Y1. pose proof (am_ew_y g pos c regs2 ys 2) as Y2. pose proof (am_ew_y g pos c regs2 ys 3) as Y3. pose proof (am_ew_y g pos c regs2 ys 4) as Y4. pose proof (am_ew_y g pos c regs2 ys 5) as Y5. pose proof (am_ew_y g pos c regs2 ys 6) as Y6. pose proof (am_ew_y g pos c regs2 ys 7) as Y7. pose proof (am_ew_y g pos c regs2 ys 8) as Y8. pose proof (am_ew_y g pos c regs2 ys 9) as Y9. pose proof (am_ew_y g pos c regs2 ys 10) as Y10. pose proof (am_ew_y g pos c regs2 ys 11) as Y11.
  unfold AM_X0 in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11. cbn [Nat.add] in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11.
  rewrite Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)). pose proof (rd_ib_range g (c + 2)). pose proof (rd_ib_range g (c + 3)). pose proof (rd_ib_range g (c + 4)). pose proof (rd_ib_range g (c + 5)). pose proof (rd_ib_range g (c + 6)). pose proof (rd_ib_range g (c + 7)). pose proof (rd_ib_range g (c + 8)). pose proof (rd_ib_range g (c + 9)). pose proof (rd_ib_range g (c + 10)). pose proof (rd_ib_range g (c + 11)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd6_AF (rd_pc 6) 24 36 []
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl HAF) as [HS SHOK].
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
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 36 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 360 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 6)) with (Z_to_bv 64 0x8109c). change (rd_pc 6) with 0x8109c in HS.
(* 0x8109c ld a3, in.n; to the test at 0x810a0 *)
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
(* each test of in.n - j: the first goal is in.n = j (a leaf: no more bytes), the second takes byte j *)
cw_branch Hb0; rd6_brn Hb0 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 0 | ].
(* byte 0: 0x810a4 .. 0x810cc *)
rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd6_brn Hb1 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 1 | ].
(* byte 1: 0x810d4 .. 0x810f8, j 0x81e18 *)
rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb2; rd6_brn Hb2 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 2 | ].
(* byte 2: 0x81e20 .. 0x81e48 *)
rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb3; rd6_brn Hb3 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 3 | ].
(* byte 3: 0x81e50 .. 0x81e74, k.a stored *)
rd_in_add LAWS HJ0 Hfr HC c 3%nat E35 EY3 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb4; rd6_brn Hb4 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 4 | ].
(* byte 4: 0x81ea4 .. 0x81ec8 *)
rd_in_add LAWS HJ0 Hfr HC c 4%nat E35 EY4 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb5; rd6_brn Hb5 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 5 | ].
(* byte 5: 0x81ed0 .. 0x81ef0 *)
rd_in_add LAWS HJ0 Hfr HC c 5%nat E35 EY5 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb6; rd6_brn Hb6 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 6 | ].
(* byte 6: 0x81f10 .. 0x81f34 *)
rd_in_add LAWS HJ0 Hfr HC c 6%nat E35 EY6 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb7; rd6_brn Hb7 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 7 | ].
(* byte 7: 0x81f3c .. 0x81f60, k.c stored *)
rd_in_add LAWS HJ0 Hfr HC c 7%nat E35 EY7 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb8; rd6_brn Hb8 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 8 | ].
(* byte 8: 0x81f90 .. 0x81fb4 *)
rd_in_add LAWS HJ0 Hfr HC c 8%nat E35 EY8 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb9; rd6_brn Hb9 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 9 | ].
(* byte 9: 0x81fbc .. 0x81fdc *)
rd_in_add LAWS HJ0 Hfr HC c 9%nat E35 EY9 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb10; rd6_brn Hb10 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 10 | ].
(* byte 10: 0x82004 .. 0x82028 *)
rd_in_add LAWS HJ0 Hfr HC c 10%nat E35 EY10 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb11; rd6_brn Hb11 E36; [ rd6_leaf LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E35 E32 EFA g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 11 | ].
(* byte 11: 0x82030 .. 0x820b4 *)
rd_in_add LAWS HJ0 Hfr HC c 11%nat E35 EY11 HSEP.
rd6_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
(* k.b composed and stored, RUN *)
rd6_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 12.
Qed.

End b.
End a.
