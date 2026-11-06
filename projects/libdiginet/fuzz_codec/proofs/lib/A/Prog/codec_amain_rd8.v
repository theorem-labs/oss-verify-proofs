(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v; 112 of its 143 lines of code are new or changed and 235 lines of the source are left out. *)
(* Segment RD8 (COUNTER_LEDS) of the image-A walk of LLVMFuzzerTestOneInput: seg_rd_run 8 of
   lib/A/Prog/codec_amain_inv.v, from the reader cut at 0x811a0 to RUN 0x820d0. k.b = fuzz_u32 (fuzz_codec.c: case
   COUNTER_LEDS), stored at 28(s6).
   The code: 0x811a0 ld in.n; beqz -> 0x81fe8 (no byte); 0x811a8 .. 0x811d0 byte 0 (check slow path behind
   `j 0x82bf8`); 0x811d4 beqz in.n - 1 -> 0x8205c; 0x811d8 .. 0x811fc byte 1 (slow path 0x82d30), j 0x82060;
   0x82060 ld in.n, beqz -> 0x81fec; 0x82068 .. 0x8208c byte 2 (check inline, slow path 0x82e5c); 0x82090 beqz
   in.n - 3 -> 0x81ff0; 0x82094 .. 0x820b4 byte 3 (slow path 0x82f70); 0x820bc .. 0x820cc the bytes composed,
   sw k.b; RUN.
   The state is codec_amain_rdlib.v's rd_ss with the k window [28, 32); the four bytes are the atoms 37 .. 40
   (input bytes c .. c + 3). Each byte's check leaves one obligation, paid by the input block (codec_amain_rdin.v
   rd_obl); each byte's load reads the 1-byte region rd_in_add puts at the cursor after its in.n test; the engine
   records each branch's condition, so a repeated in.n test is decided. The cut needs only 0 <= k.b < 2^32 of the
   stored word. *)
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

Definition rd8_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0)].

(* the run to the next stop (an undecided branch or RUN 0x820d0), its input-byte obligation closed *)
Ltac rd8_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 532688; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z *)
Ltac rd8_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* RUN: k.b is the word stored at 28 (its u32 value), a / c / delta / bytes still HEAD's zeros *)
Ltac rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cd := fresh "Cd" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb; rd_chunk HS 33%nat 204 Cd;
  rewrite ?ew_ewset_other in Cd by lia; rewrite B33 in Cd;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Cd with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 204 (CVal 4 ?v)) =>
  eapply (rd_endk B MT K XM_LIB LAWS g pos sp1 ops 28 32 c ys ly2 S2 W2 regs2 mem2 md2 k 8 pv dv od Ef ssf msf _ j
    0 (bv_unsigned (sv_denot Ef v) mod 2 ^ 32) 0 0 (repeat 0 24)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ unfold codec_owe.reader_ok; rewrite repeat_length;
    split; [lia|]; split; [apply rd_u32_range|]; split; [lia|]; split; [lia|];
    split; [reflexivity|]; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|];
    split; [lia|]; split; [intros; discriminate|]; split; intros; discriminate
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 8 pv dv 28 32 24 Hkat); first [exact KE | lia]
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 28) 4 _ => replace (F + 176 + 28) with (F + 204) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cd)
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 8 pv dv 28 32 32 Hkat); first [exact KE | lia]
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 8 pv dv 28 32 36 Hkat); first [exact KE | lia]
  | destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _); cbn [kz_bytes k_rdZ] in Vy;
    apply (rd_garr8_kept_k g pos sp1 28 32 W2 mem2 _ 40 (repeat 0 24) KE); [lia | lia | lia | lia | rewrite repeat_length; cbn; lia
      | rewrite repeat_length; cbn; lia | exact Vy] ]
  end
end.

Theorem seg_rd8_holds : seg_rd_run B MT K XM_LIB 8.
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
set (ys := [rd_ib g c; rd_ib g (c + 1); rd_ib g (c + 2); rd_ib g (c + 3)]).
assert (HAF : atoms_ok (am_env g pos c regs2 ys) rd8_AF).
{ unfold rd8_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (am_ew_y g pos c regs2 ys 0) as Y0. pose proof (am_ew_y g pos c regs2 ys 1) as Y1.
  pose proof (am_ew_y g pos c regs2 ys 2) as Y2. pose proof (am_ew_y g pos c regs2 ys 3) as Y3.
  unfold AM_X0 in Y0, Y1, Y2, Y3. cbn [Nat.add] in Y0, Y1, Y2, Y3. rewrite Y0, Y1, Y2, Y3.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)).
  pose proof (rd_ib_range g (c + 2)). pose proof (rd_ib_range g (c + 3)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd8_AF (rd_pc 8) 28 32 []
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
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 28 32 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 360 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 8)) with (Z_to_bv 64 0x811a0). change (rd_pc 8) with 0x811a0 in HS.
(* 0x811a0 ld a3, in.n; to the test at 0x811a4 *)
rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd8_brn Hb1 E36.
- (* in.n = 0: no byte (0x81fe8), k.b = 0 *)
  rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 0.
- (* byte 0: 0x811a8 .. 0x811d0, to the test of in.n - 1 at 0x811d4 *)
  rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  cw_branch Hb2; rd8_brn Hb2 E36.
  + (* in.n = 1: 0x8205c, 0x82060 (the test at 0x82064 decided from the recorded in.n - 1 = 0), 0x81fec *)
    rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 1.
  + (* byte 1: 0x811d8 .. 0x811fc, j 0x82060, to the test of in.n - 2 at 0x82064 *)
    rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    cw_branch Hb3; rd8_brn Hb3 E36.
    * rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 2.
    * (* byte 2: 0x82068 .. 0x8208c, to the test of in.n - 3 at 0x82090 *)
      rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
      rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      cw_branch Hb4; rd8_brn Hb4 E36.
      -- rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
         rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 3.
      -- (* byte 3: 0x82094 .. 0x820b4, the composition, sw k.b *)
         rd_in_add LAWS HJ0 Hfr HC c 3%nat E35 EY3 HSEP.
         rd8_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
         rd8_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 4.
Qed.

End b.
End a.
