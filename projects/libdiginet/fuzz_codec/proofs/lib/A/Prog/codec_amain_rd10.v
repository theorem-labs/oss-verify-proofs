(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v; 141 of its 172 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd5.v, with its addresses and numbers changed; 186 of its 284 lines of code are new or changed and 74 lines of the source are left out. *)
(* Segment RD10 (COUNTER) of the image-A walk of LLVMFuzzerTestOneInput: seg_rd_run 10 of
   lib/A/Prog/codec_amain_inv.v, from the reader cut at 0x81104 to RUN 0x820d0. k.b = fuzz_u8, then
   k.bytes[0 .. 8) = fuzz_u8 each (fuzz_codec.c: case COUNTER, SPEC_DIGITS = 8).
   The code: 0x81104 ld in.n; beqz -> 0x81138 (no byte: k.b is the in.n just tested, 0); 0x8110c .. 0x81134 byte 0
   (check slow path behind `j 0x82bec`); 0x81138 .. 0x81148 sw k.b, a1 = 8, a2 = &k.bytes (spill 88(sp1)); the
   loop 0x8114c .. 0x8118c: beqz in.n - j -> 0x8117c (a missing byte reads 0), else byte j (check inline, slow path
   0x81194), sb, a1 - 1, a2 + 1, bnez a1; j RUN.
   The state is codec_amain_rdlib.v's rd_ss with the k window [28, 48) (k.b and the first 8 bytes); c and delta lie
   inside the window and are not written, so the window starts with their HEAD zeros as chunks (rd10_cs) and the
   end reads them back. The nine bytes are the atoms 37 .. 45 (input bytes c .. c + 8). Each byte's check leaves one
   obligation, paid by the input block (codec_amain_rdin.v rd_obl); each byte's load reads the 1-byte region
   rd_in_add puts at the cursor after its in.n test; the engine records each in.n test's condition, so once the
   bytes ran out every later test is decided: ten paths by the bytes taken. The walk keeps one bound
   c + j <= e_n g in place of the tests' disequalities. The cut needs k.b < 256: the engine's range of the stored
   value (the byte's atom fact), or in.n = 0 on the path with no byte. *)
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

Definition rd10_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
 (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
 (45%nat, mkAF 0 255 0)].
(* c (k + 32) and delta (k + 36), inside the window, as HEAD left them *)
Definition rd10_cs : list YP09.chunk := [YP09.mkChunk 208 (CVal 4 (SLit 0)); YP09.mkChunk 212 (CVal 4 (SLit 0))].

(* the run to the next stop (an undecided branch or RUN 0x820d0), its input-byte obligation closed *)
Ltac rd10_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 532688; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z *)
Ltac rd10_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb].
(* in.n - m <> 0 with the bound c + m <= n: the bound c + (m + 1) <= n replaces both *)
Ltac rd_bump Hb Hcm :=
lazymatch type of Hcm with ?c + ?m <= ?n =>
  let m' := eval cbv in (m + 1) in
  let H := fresh "Hcm" in assert (H : c + m' <= n) by lia; clear Hb Hcm; rename H into Hcm end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.

(* a literal-0 value chunk, as the field's value 0 *)
Lemma rd_chunk_lit0 : forall E (m : word -> option byte) base off (w : N),
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w (SLit 0))) -> val_mem tfibsegs m (base + off) (N.to_nat w) 0.
Proof.
intros E m base off w H. pose proof (rd_val_of_chunk E m base off w (SLit 0) H) as V.
cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. exact V.
Qed.

(* k.bytes at the end of a reader that writes its first 8 bytes (k + 40 .. k + 48, the frame's F + 216 .. F + 224):
   each written byte as its 1-byte value, the other 16 kept from the cut's zeros *)
Lemma rd_bytes8 : forall g pos sp1 lo hi (W2 : world tfibsegs) mem2 mem3 kind pv dv x0 x1 x2 x3 x4 x5 x6 x7,
k_at g pos (k_rdZ kind pv dv) W2 mem2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
4096 <= FA g pos -> FA g pos + 512 <= sp1 -> sp1 <= 2 ^ 47 -> 0 <= lo -> hi <= 48 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 216) 1 x0 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 217) 1 x1 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 218) 1 x2 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 219) 1 x3 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 220) 1 x4 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 221) 1 x5 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 222) 1 x6 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 223) 1 x7 ->
garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 40)
  (map (fun x => x mod 256) [x0; x1; x2; x3; x4; x5; x6; x7] ++ repeat 0 16).
Proof.
intros g pos sp1 lo hi W2 mem2 mem3 kind pv dv x0 x1 x2 x3 x4 x5 x6 x7 ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _)
  KE HF HFs H47 Hlo Hhi V0 V1 V2 V3 V4 V5 V6 V7.
cbn [kz_bytes k_rdZ] in Vy.
assert (VB : forall x a, val_mem tfibsegs (mrestrict (w_H W2) mem3) a 1 x ->
  val_mem tfibsegs (mrestrict (w_H W2) mem3) a 1 (x mod 256) /\ 0 <= x mod 256 < 256).
{ intros x a Hv. split; [|apply Z.mod_pos_bound; lia].
  apply (rd_val_congr _ a 1 x); [|exact Hv]. change (8 * Z.of_nat 1) with 8. rewrite Z.mod_mod by lia. reflexivity. }
intros j Hj. simpl in Hj.
destruct (Nat.lt_ge_cases j 8) as [H8|H8].
- destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; cbn [map app nth].
  + replace (FA g pos + 176 + 40 + Z.of_nat 0) with (FA g pos + 216) by lia. exact (VB _ _ V0).
  + replace (FA g pos + 176 + 40 + Z.of_nat 1) with (FA g pos + 217) by lia. exact (VB _ _ V1).
  + replace (FA g pos + 176 + 40 + Z.of_nat 2) with (FA g pos + 218) by lia. exact (VB _ _ V2).
  + replace (FA g pos + 176 + 40 + Z.of_nat 3) with (FA g pos + 219) by lia. exact (VB _ _ V3).
  + replace (FA g pos + 176 + 40 + Z.of_nat 4) with (FA g pos + 220) by lia. exact (VB _ _ V4).
  + replace (FA g pos + 176 + 40 + Z.of_nat 5) with (FA g pos + 221) by lia. exact (VB _ _ V5).
  + replace (FA g pos + 176 + 40 + Z.of_nat 6) with (FA g pos + 222) by lia. exact (VB _ _ V6).
  + replace (FA g pos + 176 + 40 + Z.of_nat 7) with (FA g pos + 223) by lia. exact (VB _ _ V7).
- assert (Hn : nth j (map (fun x => x mod 256) [x0; x1; x2; x3; x4; x5; x6; x7] ++ repeat 0 16) 0 = 0).
  { rewrite app_nth2 by (cbn [length map]; lia). apply nth_repeat. }
  rewrite Hn. split; [|lia].
  destruct (Vy j ltac:(rewrite repeat_length; lia)) as [Vj _]. rewrite nth_repeat in Vj.
  apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Vj].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KE; [lia | unfold rd_zone; lia].
Qed.

Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* k.b < 256: the engine's range of the stored value, or the in.n tested 0 *)
Ltac rd10_blt Ef vb Hvb E36 :=
first
[ rewrite Z.mod_small by lia; lia
| lazymatch vb with SOff 36 ?o =>
    lazymatch type of E36 with ew _ 36 = Z_to_bv 64 ?x =>
    change (bv_unsigned (sv_denot Ef vb)) with (U Ef vb);
    rewrite (cw_U_offx Ef 36 x o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia));
    replace (x + o) with 0 by lia; rewrite !Z.mod_0_l by lia; lia end end ].

(* RUN: k.b is the word stored at 28 (its u32 value), the bytes the eight 1-byte values stored at 40 .. 48; a kept,
   c and delta read back from their chunks *)
Ltac rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in
  let Cc := fresh "Cc" in let Cd := fresh "Cd" in
  let Y0 := fresh "Y0" in let Y1 := fresh "Y1" in let Y2 := fresh "Y2" in let Y3 := fresh "Y3" in
  let Y4 := fresh "Y4" in let Y5 := fresh "Y5" in let Y6 := fresh "Y6" in let Y7 := fresh "Y7" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb; rd_chunk HS 33%nat 204 Cx;
  rd_chunk HS 33%nat 208 Cc; rd_chunk HS 33%nat 212 Cd;
  rd_chunk HS 33%nat 216 Y0; rd_chunk HS 33%nat 217 Y1; rd_chunk HS 33%nat 218 Y2; rd_chunk HS 33%nat 219 Y3;
  rd_chunk HS 33%nat 220 Y4; rd_chunk HS 33%nat 221 Y5; rd_chunk HS 33%nat 222 Y6; rd_chunk HS 33%nat 223 Y7;
  rewrite ?ew_ewset_other in Cx, Cc, Cd, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7 by lia;
  rewrite B33 in Cx, Cc, Cd, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 204 (CVal 4 ?vb)) =>
  lazymatch type of Y0 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 216 (CVal 1 ?y0)) =>
  lazymatch type of Y1 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 217 (CVal 1 ?y1)) =>
  lazymatch type of Y2 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 218 (CVal 1 ?y2)) =>
  lazymatch type of Y3 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 219 (CVal 1 ?y3)) =>
  lazymatch type of Y4 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 220 (CVal 1 ?y4)) =>
  lazymatch type of Y5 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 221 (CVal 1 ?y5)) =>
  lazymatch type of Y6 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 222 (CVal 1 ?y6)) =>
  lazymatch type of Y7 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 223 (CVal 1 ?y7)) =>
  let Hvb := fresh "Hvb" in
  let r := eval vm_compute in (sv_urange (ss_facts ssf) vb) in
  lazymatch r with Some (?lo, ?hi) =>
    pose proof (sv_urange_sound Ef (ss_facts ssf) vb lo hi (st_ok_facts_ok tfibsegs Ef ssf _ HS)
      ltac:(vm_compute; reflexivity)) as Hvb; unfold U in Hvb end;
  eapply (rd_endk B MT K XM_LIB LAWS g pos sp1 ops 28 48 c ys ly2 S2 W2 regs2 mem2 md2 k 10 pv dv od Ef ssf msf _ j
    0 (bv_unsigned (sv_denot Ef vb) mod 2 ^ 32) 0 0
    (map (fun x => x mod 256) [bv_unsigned (sv_denot Ef y0); bv_unsigned (sv_denot Ef y1); bv_unsigned (sv_denot Ef y2);
       bv_unsigned (sv_denot Ef y3); bv_unsigned (sv_denot Ef y4); bv_unsigned (sv_denot Ef y5);
       bv_unsigned (sv_denot Ef y6); bv_unsigned (sv_denot Ef y7)] ++ repeat 0 16)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ unfold codec_owe.reader_ok;
    split; [lia|]; split; [apply rd_u32_range|]; split; [lia|]; split; [lia|];
    split; [reflexivity|];
    split; [apply Forall_app; split;
            [ cbn [map]; repeat (apply Forall_cons; [apply Z.mod_pos_bound; lia|]); apply Forall_nil
            | apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia ]|];
    split; [lia|]; split; [intros; discriminate|]; split; [intros _; rd10_blt Ef vb Hvb E36 | intros; discriminate]
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 10 pv dv 28 48 24 Hkat); first [exact KE | lia]
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 28) 4 _ => replace (F + 176 + 28) with (F + 204) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cx)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 32) 4 _ => replace (F + 176 + 32) with (F + 208) by lia end;
    exact (rd_chunk_lit0 _ _ _ _ 4 Cc)
  | lazymatch goal with |- val_mem _ _ (?F + 176 + 36) 4 _ => replace (F + 176 + 36) with (F + 212) by lia end;
    exact (rd_chunk_lit0 _ _ _ _ 4 Cd)
  | apply (rd_bytes8 g pos sp1 28 48 W2 mem2 _ 10 pv dv _ _ _ _ _ _ _ _ Hkat KE); [lia | lia | lia | lia | lia
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y0) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y1)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y2) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y3)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y4) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y5)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y6) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y7) ] ]
  end end end end end end end end end
end.

Theorem seg_rd10_holds : seg_rd_run B MT K XM_LIB 10.
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
  rd_ib g (c + 6); rd_ib g (c + 7); rd_ib g (c + 8)]).
assert (HAF : atoms_ok (am_env g pos c regs2 ys) rd10_AF).
{ unfold rd10_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (am_ew_y g pos c regs2 ys 0) as Y0. pose proof (am_ew_y g pos c regs2 ys 1) as Y1.
  pose proof (am_ew_y g pos c regs2 ys 2) as Y2. pose proof (am_ew_y g pos c regs2 ys 3) as Y3.
  pose proof (am_ew_y g pos c regs2 ys 4) as Y4. pose proof (am_ew_y g pos c regs2 ys 5) as Y5.
  pose proof (am_ew_y g pos c regs2 ys 6) as Y6. pose proof (am_ew_y g pos c regs2 ys 7) as Y7.
  pose proof (am_ew_y g pos c regs2 ys 8) as Y8.
  unfold AM_X0 in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8. cbn [Nat.add] in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8.
  rewrite Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)).
  pose proof (rd_ib_range g (c + 2)). pose proof (rd_ib_range g (c + 3)).
  pose proof (rd_ib_range g (c + 4)). pose proof (rd_ib_range g (c + 5)).
  pose proof (rd_ib_range g (c + 6)). pose proof (rd_ib_range g (c + 7)). pose proof (rd_ib_range g (c + 8)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
assert (HCS : Forall (YP09.chunk_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) rd10_cs).
{ pose proof Hkat as ((_ & _ & _ & _ & _ & Vc & Vd & _) & _). cbn [kz_c kz_delta k_rdZ] in Vc, Vd.
  unfold rd10_cs. constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 208 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 208) with (FA g pos + 176 + 32) by lia. exact Vc.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 212 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 212) with (FA g pos + 176 + 36) by lia. exact Vd. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd10_AF (rd_pc 10) 28 48 rd10_cs
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
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 28 48 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 360 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hcm : c + 0 <= e_n g) by lia.
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 10)) with (Z_to_bv 64 0x81104). change (rd_pc 10) with 0x81104 in HS.
(* 0x81104 ld a1, in.n; to the test at 0x81108 *)
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
(* in.n = 0: no byte, k.b = in.n = 0, the eight bytes 0 (every loop test decided) *)
cw_branch Hb0; rd10_brn Hb0 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 0
  | ].
(* byte 0 (k.b): 0x8110c .. 0x81134, sw k.b, to the loop test of in.n - 1 at 0x8114c *)
rd_bump Hb0 Hcm. rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd10_brn Hb1 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 1
  | ].
(* byte 1 (k.bytes[0]): the loop body, to the test of in.n - 2 *)
rd_bump Hb1 Hcm. rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb2; rd10_brn Hb2 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 2
  | ].
(* byte 2 (k.bytes[1]) *)
rd_bump Hb2 Hcm. rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb3; rd10_brn Hb3 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 3
  | ].
(* byte 3 (k.bytes[2]) *)
rd_bump Hb3 Hcm. rd_in_add LAWS HJ0 Hfr HC c 3%nat E35 EY3 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb4; rd10_brn Hb4 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 4
  | ].
(* byte 4 (k.bytes[3]) *)
rd_bump Hb4 Hcm. rd_in_add LAWS HJ0 Hfr HC c 4%nat E35 EY4 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb5; rd10_brn Hb5 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 5
  | ].
(* byte 5 (k.bytes[4]) *)
rd_bump Hb5 Hcm. rd_in_add LAWS HJ0 Hfr HC c 5%nat E35 EY5 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb6; rd10_brn Hb6 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 6
  | ].
(* byte 6 (k.bytes[5]) *)
rd_bump Hb6 Hcm. rd_in_add LAWS HJ0 Hfr HC c 6%nat E35 EY6 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb7; rd10_brn Hb7 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 7
  | ].
(* byte 7 (k.bytes[6]) *)
rd_bump Hb7 Hcm. rd_in_add LAWS HJ0 Hfr HC c 7%nat E35 EY7 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb8; rd10_brn Hb8 E36;
  [ rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
    rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 8
  | ].
(* byte 8 (k.bytes[7]), the loop's last pass, j RUN *)
rd_bump Hb8 Hcm. rd_in_add LAWS HJ0 Hfr HC c 8%nat E35 EY8 HSEP.
rd10_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
rd10_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 9.
Qed.

End b.
End a.
