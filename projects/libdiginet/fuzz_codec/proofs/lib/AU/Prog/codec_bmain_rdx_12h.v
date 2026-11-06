(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 197 of its 237 lines of code are new or changed and 183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_rdx_12t.v, with its module names, addresses and numbers changed; 92 of its 145 lines of code are new or changed and 184 lines of the source are left out. *)
(* Segment RD12 (SCRIBBLE_TEXT) of the image-B walk of LLVMFuzzerTestOneInput, first part: from the reader cut
   inv_rd .. 12 at 0x80fa4 to the inner cut rd12_Pa at 0x80fc0 (lib/AU/Prog/codec_bmain_rdx_l12.v).
     0x80fa4  bnez s6 (k.p, the s6 of the cut), taken to 0x80fc0 with k as the cut has it;
     0x80fa8  li a0,1; jal diginet_personality_of (0x8513c, run inline: it returns personalities[0] = CB_PERS for 1);
     0x80fb0  a1 = SPEC_C24; sd a0,8(s7); sd a1,16(s7): k.p / k.desk = the pair of Control|24.
   The state is codec_bmain_rdlib.v's rd_ss with the k window [8, 24) holding p and desk as the segment's atoms 37 / 38.
   It is the image-A part lib/A/Prog/codec_amain_rd12h.v at image B. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgTokJU codec_bmain_inv codec_bmain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdlib codec_bmain_rdin codec_bmain_rdx_l12.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* env_agree at a lower bound *)
Lemma r12h_ag : forall k k' E E', (k' <= k)%nat -> env_agree k E E' -> env_agree k' E E'.
Proof. intros k k' E E' Hk [HA HD]. split; [intros n Hn; apply HA; lia | exact HD]. Qed.

(* the run to 0x80fc0, and the cut there: its chunks (the cursor at 184 / 192 of atom 2, p and desk at 200 / 208 of
   atom 33), the env agreement with the base env, the stop's journal *)
Ltac rd12h_end B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k HJ0 Hfr Hk Hmo HC Hops HAE HEE B2 B33 EFA KE :=
  cwj_run_to ltac:(rdj_awr B2 B33 EFA) 0x80fc0; cw_keep ltac:(rdj_kwr B2 B33);
  lazymatch goal with
  | HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H _) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cp := fresh "Cp" in let Cd := fresh "Cd" in
    rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb; rd_chunk HS 33%nat 200 Cp; rd_chunk HS 33%nat 208 Cd;
    rewrite ?ew_ewset_other in Ca, Cb, Cp, Cd by lia; rewrite B2 in Ca, Cb; rewrite B33 in Cp, Cd;
    rewrite ?wvb_collapse in HJm;
    let HAf := fresh "HAf" in
    assert (HAf : env_agree 39 (bm_env g pos c regs2 ys) Ef) by (rewrite <- HEE; env_agree_chain HAE);
    apply (r12_exit B MT K XM_LIB LAWS g pos sp1 8 24 c ys ly2 S2 W2 regs2 mem2 md2 k Ef ssf msf _ 0x80fc0 _
      HJ0 Hfr Hk Hmo HC HJm (r12h_ag 39 35 _ _ ltac:(lia) HAf) HS ltac:(reflexivity) ltac:(reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) KE);
    split; [exact (r12_ops g pos c regs2 ys Ef ssf W2 msf ops (r12h_ag 39 35 _ _ ltac:(lia) HAf) HS
                     ltac:(reflexivity) Hops) |]
  end.

(* the cut's cursor and record at the stop, the record's p / desk as pv' / dv' *)
Ltac rd12h_fin g pos sp1 W2 mem2 pv dv c pv' dv' d' HP HV :=
  lazymatch goal with |- exists _ _ _ _, cur_at _ _ _ _ (ms_mem ?m) /\ _ =>
  lazymatch goal with
  | Ca : YP09.chunk_ok _ ?Ef _ _ (YP09.mkChunk 184 _), Cb : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 192 _),
    Cp : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 200 _), Cd : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 208 _),
    HAf : env_agree 39 _ ?Ef, KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _, Hkat : k_at _ _ _ _ _ |- _ =>
    let KK := fresh "KK" in let Vp := fresh "Vp" in let Vd := fresh "Vd" in let X := fresh "X" in
    assert (KK : forall x, FA g pos + 192 <= x < FA g pos + 376 -> ~ (FA g pos + 200 <= x < FA g pos + 216) ->
      aview tfibsegs (w_H W2) (ms_mem m) x = aview tfibsegs (w_H W2) mem2 x)
      by (intros x Hx1 Hx2; apply KE; [lia | unfold rd_zone; lia]);
    pose proof (rd_val_of_chunk _ _ _ _ _ _ Cp) as Vp; pose proof (rd_val_of_chunk _ _ _ _ _ _ Cd) as Vd;
    exists c, pv', dv', d'; split; [| split; [lia | split; [HP |]]];
    [ pose proof (rd_cur g sp1 c 0 W2 _ Ef Ca Cb
        ltac:(rewrite (rd_ag 39 _ _ 35 HAf ltac:(lia)); apply bm_ew_CP)
        ltac:(rewrite (rd_ag 39 _ _ 36 HAf ltac:(lia)); apply bm_ew_CN)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X;
      rewrite Z.add_0_r in X; exact X
    | change (k_rdZ 12 pv' dv') with (kz_set_pd (k_rdZ 12 pv dv) pv' dv');
      apply (r12_kat_pd g pos (k_rdZ 12 pv dv) W2 mem2 _ pv' dv' Hkat KK);
      [ unfold CB_PERS, CM_SPEC_C24 in *; lia | unfold CB_PERS, CM_SPEC_C24 in *; lia
      | replace (FA g pos + 192 + 8) with (FA g pos + 200) by lia; HV Ef Vp
      | replace (FA g pos + 192 + 16) with (FA g pos + 208) by lia; HV Ef Vd ] ]
  end end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Definition rd12h_cs : list YP09.chunk := [YP09.mkChunk 200 (CVal 8 (SOff 37 0)); YP09.mkChunk 208 (CVal 8 (SOff 38 0))].

Lemma rd12_head : forall g pos sp1 ops W2 c2, inv_rd B MT K XM_LIB g pos sp1 ops 12 W2 c2 ->
  SRr tfibsegs W2 c2 (mcut B MT K XM_LIB g pos sp1 0 0x80fc0 (rd12_Pa g pos sp1 ops)).
Proof using TL LAWS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hkind &
  (c & pv & dv & od & Hcur & Hc1 & Hpd & R22 & Hkat)).
replace (rd_pc 12) with 0x80fa4 by (vm_compute; reflexivity).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hpdr : 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64)
  by (destruct Hpd as [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold CB_PERS, CM_SPEC_C24, CM_SPEC_PC; lia).
set (ys := [pv; dv]).
pose proof Hkat as ((V0 & V8 & V16 & _) & _). cbn [kz_p kz_desk k_rdZ] in V8, V16.
assert (EY0 : ew (bm_env g pos c regs2 ys) 37 = Z_to_bv 64 pv) by exact (bm_ew_y g pos c regs2 ys 0).
assert (EY1 : ew (bm_env g pos c regs2 ys) 38 = Z_to_bv 64 dv) by exact (bm_ew_y g pos c regs2 ys 1).
assert (Hcs : Forall (YP09.chunk_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) rd12h_cs).
{ unfold rd12h_cs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 200 8 (SOff 37 0) pv).
    + rewrite (bm_den_off _ 37 pv 0 EY0) by lia. rewrite Z.add_0_r. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + lia.
    + replace (FA g pos + 200) with (FA g pos + 192 + 8) by lia. exact V8.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 208 8 (SOff 38 0) dv).
    + rewrite (bm_den_off _ 38 dv 0 EY1) by lia. rewrite Z.add_0_r. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + lia.
    + replace (FA g pos + 208) with (FA g pos + 192 + 16) by lia. exact V16. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys [] 0x80fa4 8 24 rd12h_cs
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) Hcs ltac:(vm_compute; reflexivity) I) as [HS SHOK].
assert (HAE : env_agree 39 (bm_env g pos c regs2 ys) (bm_env g pos c regs2 ys)) by apply env_agree_refl.
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (subst E; rewrite (bm_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 pv) by (subst E; exact (eq_trans (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl) R22)).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (bm_ew_CN g pos c regs2 ys)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 8 24 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
change (fs_frame_bytes 3) with 512 in Hfceil.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 0x80fa4) with (Z_to_bv 64 0x80fa4).
(* 0x80fa4 bnez s6 *)
cw_branch Hb1; rewrite branch_ne_U in Hb1;
rewrite (cw_U_offx E 22 pv 0 E22 ltac:(lia)) in Hb1; rewrite U_lit in Hb1 by lia; rewrite Z.mod_small in Hb1 by lia;
first [apply negb_true_iff, Z.eqb_neq in Hb1 | apply negb_false_iff, Z.eqb_eq in Hb1].
- (* k.p <> NULL: taken to 0x80fc0, k as the cut has it *)
  assert (Hd : exists d, od = Some d)
    by (destruct Hpd as [(H1 & _ & _) | [(_ & _ & H1) | (_ & _ & H1)]]; [lia | eauto | eauto]).
  destruct Hd as [d ->].
  rd12h_end B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k HJ0 Hfr Hk Hmo HC Hops HAE HEE B2 B33 EFA KE.
  rd12h_fin g pos sp1 W2 mem2 pv dv c pv dv d ltac:(exact Hpd) ltac:(fun Ef V =>
    first [ rewrite (bm_den_off Ef 37 pv 0 (eq_trans (rd_ag 39 _ _ 37 HAf ltac:(lia)) (bm_ew_y g pos c regs2 ys 0))) in V
              by lia
          | rewrite (bm_den_off Ef 38 dv 0 (eq_trans (rd_ag 39 _ _ 38 HAf ltac:(lia)) (bm_ew_y g pos c regs2 ys 1))) in V
              by lia ];
    rewrite Z.add_0_r, unsigned_lit_small in V by lia; exact V).
- (* k.p = NULL: diginet_personality_of(1), SPEC_C24, the two stores *)
  rd12h_end B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k HJ0 Hfr Hk Hmo HC Hops HAE HEE B2 B33 EFA KE.
  rd12h_fin g pos sp1 W2 mem2 pv dv c CB_PERS CM_SPEC_C24 DgnSpec.c24
    ltac:(right; left; split; [reflexivity | split; reflexivity])
    ltac:(fun Ef V => cbn [sv_denot] in V; rewrite unsigned_lit_small in V by lia; exact V).
Qed.
End d.
End c.
