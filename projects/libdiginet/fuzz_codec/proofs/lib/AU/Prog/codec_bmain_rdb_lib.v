(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its numbers changed; 208 of its 242 lines of code are new or changed and 232 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd9.v, with its module paths, module names and numbers changed; 198 of its 253 lines of code are new or changed and 187 lines of the source are left out. *)
(* The pieces the reader segments RD6 .. RD10 of the image-B walk of LLVMFuzzerTestOneInput share, on top of the
   reader layer lib/AU/Prog/codec_bmain_rdlib.v and lib/AU/Prog/codec_bmain_rdin.v (the image-A pieces of
   lib/A/Prog/codec_amain_rd6.v / codec_amain_rd10.v at image B: k = F + 192, cursor 184(sp1) / 192(sp1), RUN
   0x826f4).
   - rdb_brn: a test of in.n - j as the fact x = 0, or 0 < x (so lia never splits a disequality).
   - rdb_explore: every path of a reader from its cut, like codec_bmain_rdin.v's rd_explore, for a test of in.n
     whose taken side is either the end of the input (beqz) or the next byte (bnez): the side whose fact is 0 < x
     gets the next input byte's region.
   - rdb_end / rdb_fin: the end at RUN of a reader of kind 6 .. 8 (k.bytes and k.n untouched), as rd_end / rd_fin
     for kinds 0 .. 4.
   - rd_bytes8, rdb_bfin: the end at RUN of a reader that writes k.bytes[0 .. 8) (SCRIBBLE, COUNTER) on rd_endk;
     the fields inside the window it does not write start as chunks of HEAD's zeros and are read back; for
     COUNTER, k.b < 256 from the engine's range of the stored value or the in.n tested 0 (rdb_blt). *)
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

(* ================================ the tests of in.n ================================ *)
(* a branch on in.n - j (the atom 36 at offset -j), as x = 0 or 0 < x *)
Ltac rdb_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
rewrite ?negb_true_iff, ?negb_false_iff in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [ apply Z.eqb_eq in Hb
      | apply Z.eqb_neq in Hb;
        lazymatch type of Hb with ?x <> 0 =>
          let H := fresh "Hlt" in assert (H : 0 < x) by lia; clear Hb; rename H into Hb end ].
(* Every path of a reader from its cut: run; at RUN finish with fin; at a test of in.n split it, and on the side
   with 0 < in.n - j put the next input byte's region (j = the bytes taken, read off the cursor chunk) first. *)
Ltac rdb_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin :=
rd_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
lazymatch goal with
| HS : st_ok _ _ ?ss _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with
  | 534260 => fin
  | _ =>
    let Hb := fresh "Hb" in
    cw_branch Hb; rdb_brn Hb E36;
    lazymatch type of Hb with
    | _ = 0 => rdb_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
    | 0 < _ =>
      lazymatch goal with HS' : st_ok _ _ ?ss' _ |- _ =>
        let jz := eval vm_compute in (rd_cur_off (ss_mem ss')) in
        lazymatch jz with Some ?jj =>
          let j := eval vm_compute in (Z.to_nat jj) in
          rd_in_add LAWS HJ0 HFR HC c j E35 EYall HSEP;
          rdb_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
        end
      end
    end
  end
end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ the end of a reader of kinds 6 .. 8 ================================ *)
(* RUN 0x826f4 for a reader of kind 6 .. 8 (k.bytes and k.n as HEAD left them): codec_bmain_rdin.v's rd_end *)
Lemma rdb_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kind pv dv od lo hi Ef ss ms md3 j a b cc d,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
k_at g pos (k_rdZ kind pv dv) W2 mem2 -> pd_okB pv dv od -> 6 <= kind <= 8 -> 0 <= c ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 41 (bm_env g pos c regs2 ys) Ef ->
st_ok tfibsegs Ef ss (restrict (w_H W2) ms) -> ss_pc ss = PC_RUN -> ss_resv ss = None ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
24 <= lo -> hi <= 40 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi x -> aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 184 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 192 (CVal 8 (SOff 36 (- j)))) ->
0 <= j -> c + j <= e_n g ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 192 + 24) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 192 + 28) 4 b ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 192 + 32) 4 cc ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 192 + 36) 4 d ->
0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= cc < 2 ^ 32 -> - 2 ^ 31 <= d < 2 ^ 31 ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kind pv dv od lo hi Ef ss ms md3 j a b cc d
  HJ Hfr Hk Hmo HC Hops Hkat Hpd Hkind Hc HJ3 HAG HS Hpc Hresv Hkeep H20 Hlo Hhi KE Ca Cb Hj Hcj Va Vb Vc Vd Ha Hb Hcc Hd.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _ & Hsp & Hsp0c & Hsp047 & _ & _ & Hng & Hp & Hpn & _).
unfold BM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
change (fs_frame_bytes 3) with 512 in Hfceil.
destruct HAG as (HA & HD).
assert (E35 : ew Ef 35 = Z_to_bv 64 (e_p g + c)) by (rewrite (HA 35%nat ltac:(lia)); exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew Ef 36 = Z_to_bv 64 (e_n g - c)) by (rewrite (HA 36%nat ltac:(lia)); exact (bm_ew_CN g pos c regs2 ys)).
apply (rd_exit B MT K XM_LIB LAWS g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k Ef ss ms md3 (c + j)
  (rdk kind pv dv a b cc d (repeat 0 24)) od HJ Hfr Hk Hmo HC Hops HJ3).
- split; [intros i Hi; apply HA; lia | exact HD].
- exact HS.
- exact Hpc.
- exact Hresv.
- exact Hkeep.
- exact H20.
- lia.
- lia.
- exact KE.
- exact (rd_cur g sp1 c j W2 (ms_mem ms) Ef Ca Cb E35 E36 Hc Hj Hcj ltac:(lia) ltac:(lia)).
- apply (rd_kat g pos W2 mem2 (ms_mem ms) kind pv dv a b cc d (repeat 0 24) Hkat).
  + intros x Hx Hw. apply KE; [lia|]. unfold rd_zone. lia.
  + exact Ha.
  + exact Hb.
  + exact Hcc.
  + exact Hd.
  + apply repeat_length.
  + exact Va.
  + exact Vb.
  + exact Vc.
  + exact Vd.
  + destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _). cbn [kz_bytes k_rdZ] in Vy.
    apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vy].
    intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat] in Hx. apply KE; [lia|]. unfold rd_zone. lia.
- apply rd_enc_ok; [lia | exact Hpd |].
  unfold codec_owe.reader_ok. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply repeat_length|]. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
  split; [lia|]. split; [intros; lia|]. split; intros; lia.
Qed.

(* ================================ k.bytes[0 .. 8) ================================ *)
(* k.bytes at the end of a reader that writes its first 8 bytes (k + 40 .. k + 48, the frame's F + 232 .. F + 240):
   each written byte as its 1-byte value, the other 16 kept from the cut's zeros *)
Lemma rd_bytes8 : forall g pos sp1 lo hi (W2 : world tfibsegs) mem2 mem3 kind pv dv x0 x1 x2 x3 x4 x5 x6 x7,
k_at g pos (k_rdZ kind pv dv) W2 mem2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
4096 <= FA g pos -> FA g pos + 512 <= sp1 -> sp1 <= 2 ^ 47 -> 0 <= lo -> hi <= 48 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 232) 1 x0 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 233) 1 x1 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 234) 1 x2 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 235) 1 x3 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 236) 1 x4 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 237) 1 x5 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 238) 1 x6 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 239) 1 x7 ->
garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 192 + 40)
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
  + replace (FA g pos + 192 + 40 + Z.of_nat 0) with (FA g pos + 232) by lia. exact (VB _ _ V0).
  + replace (FA g pos + 192 + 40 + Z.of_nat 1) with (FA g pos + 233) by lia. exact (VB _ _ V1).
  + replace (FA g pos + 192 + 40 + Z.of_nat 2) with (FA g pos + 234) by lia. exact (VB _ _ V2).
  + replace (FA g pos + 192 + 40 + Z.of_nat 3) with (FA g pos + 235) by lia. exact (VB _ _ V3).
  + replace (FA g pos + 192 + 40 + Z.of_nat 4) with (FA g pos + 236) by lia. exact (VB _ _ V4).
  + replace (FA g pos + 192 + 40 + Z.of_nat 5) with (FA g pos + 237) by lia. exact (VB _ _ V5).
  + replace (FA g pos + 192 + 40 + Z.of_nat 6) with (FA g pos + 238) by lia. exact (VB _ _ V6).
  + replace (FA g pos + 192 + 40 + Z.of_nat 7) with (FA g pos + 239) by lia. exact (VB _ _ V7).
- assert (Hn : nth j (map (fun x => x mod 256) [x0; x1; x2; x3; x4; x5; x6; x7] ++ repeat 0 16) 0 = 0).
  { rewrite app_nth2 by (cbn [length map]; lia). apply nth_repeat. }
  rewrite Hn. split; [|lia].
  destruct (Vy j ltac:(rewrite repeat_length; lia)) as [Vj _]. rewrite nth_repeat in Vj.
  apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Vj].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KE; [lia | unfold rd_zone; lia].
Qed.
End b.
End a.

(* the end at RUN of a reader of kind kd (6 .. 8) with window [lo, hi): codec_bmain_rdin.v's rd_fin on rdb_end *)
Ltac rdb_fin LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kd pv dv od lo hi :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in
  rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb;
  rewrite ?ew_ewset_other in Ca, Cb by lia; rewrite B2 in Ca, Cb;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Ca with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 184 (CVal 8 (SOff 35 ?j))) =>
  eapply (rdb_end _ _ _ _ LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kd pv dv od lo hi Ef ssf msf _ j _ _ _ _
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd ltac:(lia) ltac:(lia) HJm
    ltac:(env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE
  | first [lia | apply rd_u32_range] | first [lia | apply rd_u32_range] | first [lia | apply rd_u32_range]
  | first [lia | apply s32_range] ]
  end
end.

(* k.b < 256 at COUNTER's end: the engine's range of the stored value, or the in.n tested 0 *)
Ltac rdb_blt E36 :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf _ |- bv_unsigned (sv_denot ?Ef' ?vb) mod 2 ^ 32 < 256 =>
  first
  [ let r := eval vm_compute in (sv_urange (ss_facts ssf) vb) in
    lazymatch r with Some (?lo, ?hi) =>
      let Hvb := fresh "Hvb" in
      pose proof (sv_urange_sound Ef (ss_facts ssf) vb lo hi (st_ok_facts_ok tfibsegs Ef ssf _ HS)
        ltac:(vm_compute; reflexivity)) as Hvb; unfold U in Hvb;
      rewrite Z.mod_small by lia; lia end
  | lazymatch vb with SOff 36 ?o =>
      lazymatch type of E36 with ew _ 36 = Z_to_bv 64 ?x =>
      change (bv_unsigned (sv_denot Ef' vb)) with (U Ef' vb);
      rewrite (cw_U_offx Ef' 36 x o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia));
      replace (x + o) with 0 by lia; rewrite !Z.mod_0_l by lia; lia end end ]
end.

(* the end at RUN of a reader of kind kd (9 SCRIBBLE, 10 COUNTER) with window [lo, hi) that wrote
   k.bytes[0 .. 8): the four scalar fields kept or read from their chunks (codec_bmain_rdin.v rd_field), the
   bytes from their 1-byte chunks (rd_bytes8) *)
Ltac rdb_bfin LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kd pv dv od lo hi :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in
  let Y0 := fresh "Y0" in let Y1 := fresh "Y1" in let Y2 := fresh "Y2" in let Y3 := fresh "Y3" in
  let Y4 := fresh "Y4" in let Y5 := fresh "Y5" in let Y6 := fresh "Y6" in let Y7 := fresh "Y7" in
  rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb;
  rd_chunk HS 33%nat 232 Y0; rd_chunk HS 33%nat 233 Y1; rd_chunk HS 33%nat 234 Y2; rd_chunk HS 33%nat 235 Y3;
  rd_chunk HS 33%nat 236 Y4; rd_chunk HS 33%nat 237 Y5; rd_chunk HS 33%nat 238 Y6; rd_chunk HS 33%nat 239 Y7;
  rewrite ?ew_ewset_other in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7 by lia;
  rewrite B33 in Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Ca with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 184 (CVal 8 (SOff 35 ?j))) =>
  lazymatch type of Y0 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 232 (CVal 1 ?y0)) =>
  lazymatch type of Y1 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 233 (CVal 1 ?y1)) =>
  lazymatch type of Y2 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 234 (CVal 1 ?y2)) =>
  lazymatch type of Y3 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 235 (CVal 1 ?y3)) =>
  lazymatch type of Y4 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 236 (CVal 1 ?y4)) =>
  lazymatch type of Y5 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 237 (CVal 1 ?y5)) =>
  lazymatch type of Y6 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 238 (CVal 1 ?y6)) =>
  lazymatch type of Y7 with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 239 (CVal 1 ?y7)) =>
  (eapply (rd_endk _ _ _ _ LAWS g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k kd pv dv od Ef ssf msf _ j _ _ _ _
    (map (fun x => x mod 256) [bv_unsigned (sv_denot Ef y0); bv_unsigned (sv_denot Ef y1); bv_unsigned (sv_denot Ef y2);
       bv_unsigned (sv_denot Ef y3); bv_unsigned (sv_denot Ef y4); bv_unsigned (sv_denot Ef y5);
       bv_unsigned (sv_denot Ef y6); bv_unsigned (sv_denot Ef y7)] ++ repeat 0 16)
    HJ0 Hfr Hk Hmo HC Hops ltac:(lia) Hpd Hkat ltac:(lia) HJm
    ltac:(env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ idtac
  | rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE
  | apply (rd_bytes8 g pos sp1 lo hi W2 mem2 _ kd pv dv _ _ _ _ _ _ _ _ Hkat KE); [lia | lia | lia | lia | lia
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y0) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y1)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y2) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y3)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y4) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y5)
      | exact (rd_val_of_chunk _ _ _ _ 1 _ Y6) | exact (rd_val_of_chunk _ _ _ _ 1 _ Y7) ] ]);
  unfold codec_owe.reader_ok;
  split; [first [lia | apply rd_u32_range]|]; split; [first [lia | apply rd_u32_range]|];
  split; [first [lia | apply rd_u32_range]|]; split; [first [lia | apply s32_range]|];
  split; [reflexivity|];
  split; [apply Forall_app; split;
          [ cbn [map]; repeat (apply Forall_cons; [apply Z.mod_pos_bound; lia|]); apply Forall_nil
          | apply Forall_forall; let x := fresh "x" in let Hx := fresh "Hx" in
            intros x Hx; apply repeat_spec in Hx; lia ]|];
  split; [lia|]; split; [intros; discriminate|];
  split; [ first [intros; discriminate | intros _; rdb_blt E36] | intros; discriminate ]
  end end end end end end end end end
end.
