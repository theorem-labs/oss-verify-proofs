(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its module paths and module names changed; 143 of its 173 lines of code are new or changed and 236 lines of the source are left out. *)
(* Segment RD5 (RING) of the image-B walk of LLVMFuzzerTestOneInput: seg_rd_run 5 of
   lib/AU/Prog/codec_bmain_inv.v, from the reader cut at 0x81270 to RUN 0x826f4. k.a = fuzz_u32 then
   k.b = fuzz_u16 (fuzz_codec.c: case RING), stored at 24(s7) (0x81e38) and 28(s7) (0x826f0).
   The state is codec_bmain_rdlib.v's rd_ss with the k window [24, 32); the six bytes are the atoms 37 .. 42
   (input bytes c .. c + 5). Before each byte the code tests in.n, then advances the cursor with its UBSan check
   (decided by the engine). Each byte's instrumented check leaves one obligation, paid by the input block
   (codec_bmain_rdin.v rd_obl); each byte's load reads the 1-byte region rd_in_add puts at the cursor after its
   in.n test; the engine records each branch's condition, so an in.n test repeated after the bytes ran out is
   decided. The cut needs 0 <= k.a < 2^32 and 0 <= k.b < 2^16 of the stored words; the second comes from the
   engine's own range of the stored value (sv_urange_sound over the state's atom facts, the bytes in [0, 255]). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st CPgTokJU codec_bmain_rdlib codec_bmain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition rd5_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
 (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0)].

(* the run to the next stop (an undecided branch or RUN 0x820d0), its input-byte obligation closed *)
Ltac rd5_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 534260; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z *)
Ltac rd5_brn Hb E36 :=
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

(* RUN: k.a / k.b are the words stored at 24 / 28 (their u32 values; k.b below 2^16 by the engine's range of its
   value), c / delta / bytes still HEAD's zeros *)
Ltac rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od j :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in let Cy := fresh "Cy" in
  rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb; rd_chunk HS 33%nat 216 Cx; rd_chunk HS 33%nat 220 Cy;
  rewrite ?ew_ewset_other in Cx, Cy by lia; rewrite B33 in Cx, Cy;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 216 (CVal 4 ?va)) =>
  lazymatch type of Cy with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 220 (CVal 4 ?vb)) =>
  let Hvb := fresh "Hvb" in
  let r := eval vm_compute in (sv_urange (ss_facts ssf) vb) in
  lazymatch r with Some (?lo, ?hi) =>
    pose proof (sv_urange_sound Ef (ss_facts ssf) vb lo hi (st_ok_facts_ok tfibsegs Ef ssf _ HS)
      ltac:(vm_compute; reflexivity)) as Hvb; unfold U in Hvb end;
  eapply (rd_endk B MT K XM_LIB LAWS g pos sp1 ops 24 32 c ys ly2 S2 W2 regs2 mem2 md2 k 5 pv dv od Ef ssf msf _ j
    (bv_unsigned (sv_denot Ef va) mod 2 ^ 32) (bv_unsigned (sv_denot Ef vb) mod 2 ^ 32) 0 0 (repeat 0 24)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ unfold codec_owe.reader_ok; rewrite repeat_length;
    split; [apply rd_u32_range|]; split; [apply rd_u32_range|]; split; [lia|]; split; [lia|];
    split; [reflexivity|]; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|];
    split; [lia|]; split; [intros _; rewrite Z.mod_small by lia; lia|]; split; intros; discriminate
  | lazymatch goal with |- val_mem _ _ (?F + 192 + 24) 4 _ => replace (F + 192 + 24) with (F + 216) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cx)
  | lazymatch goal with |- val_mem _ _ (?F + 192 + 28) 4 _ => replace (F + 192 + 28) with (F + 220) by lia end;
    exact (rd_chunk_u32 _ _ _ _ _ Cy)
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 5 pv dv 24 32 32 Hkat); first [exact KE | lia]
  | apply (rd_kept4 g pos sp1 W2 mem2 _ 5 pv dv 24 32 36 Hkat); first [exact KE | lia]
  | destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _); cbn [kz_bytes k_rdZ] in Vy;
    apply (rd_garr8_kept_k g pos sp1 24 32 W2 mem2 _ 40 (repeat 0 24) KE); [lia | lia | lia | lia | rewrite repeat_length; cbn; lia
      | rewrite repeat_length; cbn; lia | exact Vy] ]
  end end
end.

Theorem seg_rd5_holds : seg_rd_run B MT K XM_LIB 5.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R22 & Hkat).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
set (ys := [rd_ib g c; rd_ib g (c + 1); rd_ib g (c + 2); rd_ib g (c + 3); rd_ib g (c + 4); rd_ib g (c + 5)]).
assert (HAF : atoms_ok (bm_env g pos c regs2 ys) rd5_AF).
{ unfold rd5_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (bm_ew_y g pos c regs2 ys 0) as Y0. pose proof (bm_ew_y g pos c regs2 ys 1) as Y1.
  pose proof (bm_ew_y g pos c regs2 ys 2) as Y2. pose proof (bm_ew_y g pos c regs2 ys 3) as Y3.
  pose proof (bm_ew_y g pos c regs2 ys 4) as Y4. pose proof (bm_ew_y g pos c regs2 ys 5) as Y5.
  unfold BM_X0 in Y0, Y1, Y2, Y3, Y4, Y5. cbn [Nat.add] in Y0, Y1, Y2, Y3, Y4, Y5.
  rewrite Y0, Y1, Y2, Y3, Y4, Y5.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)).
  pose proof (rd_ib_range g (c + 2)). pose proof (rd_ib_range g (c + 3)).
  pose proof (rd_ib_range g (c + 4)). pose proof (rd_ib_range g (c + 5)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd5_AF (rd_pc 5) 24 32 []
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl HAF) as [HS SHOK].
assert (HAE : env_agree 41 (bm_env g pos c regs2 ys) (bm_env g pos c regs2 ys)) by apply env_agree_refl.
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (subst E; rewrite (bm_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (bm_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (bm_ew_SB g pos c regs2 ys)).
assert (EY0 : ew E 37 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 0))) by (subst E; rewrite Z.add_0_r; exact (bm_ew_y g pos c regs2 ys 0)).
assert (EY1 : ew E 38 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 1))) by (subst E; exact (bm_ew_y g pos c regs2 ys 1)).
assert (EY2 : ew E 39 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 2))) by (subst E; exact (bm_ew_y g pos c regs2 ys 2)).
assert (EY3 : ew E 40 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 3))) by (subst E; exact (bm_ew_y g pos c regs2 ys 3)).
assert (EY4 : ew E 41 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 4))) by (subst E; exact (bm_ew_y g pos c regs2 ys 4)).
assert (EY5 : ew E 42 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 5))) by (subst E; exact (bm_ew_y g pos c regs2 ys 5)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 32 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 376 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 5)) with (Z_to_bv 64 0x81270). change (rd_pc 5) with 0x81270 in HS.
(* 0x81270 ld in.n; to its test *)
rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb0; rd5_brn Hb0 E36.
- (* in.n = 0: no more bytes; the remaining in.n tests are decided *)
  rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 0.
- (* byte 0 *)
  rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  cw_branch Hb1; rd5_brn Hb1 E36.
  + (* in.n = 1: no more bytes; the remaining in.n tests are decided *)
    rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 1.
  + (* byte 1 *)
    rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    cw_branch Hb2; rd5_brn Hb2 E36.
    * (* in.n = 2: no more bytes; the remaining in.n tests are decided *)
      rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 2.
    * (* byte 2 *)
      rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
      rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      cw_branch Hb3; rd5_brn Hb3 E36.
      -- (* in.n = 3: no more bytes; the remaining in.n tests are decided *)
        rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
        rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 3.
      -- (* byte 3 *)
        rd_in_add LAWS HJ0 Hfr HC c 3%nat E35 EY3 HSEP.
        rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
        cw_branch Hb4; rd5_brn Hb4 E36.
        ++ (* in.n = 4: no more bytes; the remaining in.n tests are decided *)
          rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
          rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 4.
        ++ (* byte 4 *)
          rd_in_add LAWS HJ0 Hfr HC c 4%nat E35 EY4 HSEP.
          rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
          cw_branch Hb5; rd5_brn Hb5 E36.
          ** (* in.n = 5: no more bytes; the remaining in.n tests are decided *)
            rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
            rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 5.
          ** (* byte 5 *)
            rd_in_add LAWS HJ0 Hfr HC c 5%nat E35 EY5 HSEP.
            rd5_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
            rd5_end_t LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE HEE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od 6.
Qed.

End b.
End a.
