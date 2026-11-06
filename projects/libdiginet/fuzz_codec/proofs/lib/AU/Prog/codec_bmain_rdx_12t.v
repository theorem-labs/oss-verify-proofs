(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 197 of its 237 lines of code are new or changed and 183 lines of the source are left out. *)
(* Segment RD12 (SCRIBBLE_TEXT) of the image-B walk of LLVMFuzzerTestOneInput, second part: from the inner cut
   rd12_Pa at 0x80fc0 (lib/AU/Prog/codec_bmain_rdx_l12.v) to the inner cut rd12_Pb at 0x815e0.
     0x80fc0 .. 0x81000  k.a = fuzz_u8 & 0x7f: the in.n test (a missing byte reads 0 at 0x815cc), the cursor moved
                         with its UBSan check (decided by the engine), the input byte's instrumented check (slow path
                         0x83134) and the mask;
     0x815d0  sw a0,24(s7): k.a; 0x815d4 a0 = &in = sp1 + 184; 0x815d8 a1 = text = F + 80 (the spill at 104(sp1));
     0x815dc  jal text_arg (0x83ba0), ra = 0x815e0, bound through cdcU_text_arg_specX with the premises of
              lib/AU/Prog/codec_bmain_rdx_l13.v's r13_ta_pre; the cut is carried over the call by
              lib/AU/Prog/codec_bmain_rdx_l12.v's r12_call_kept (the call writes the cursor and the text only).
   It is the image-A part lib/A/Prog/codec_amain_rd12t.v at image B. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkKeptU CPgWalkCallU CPgSatU CPgTokJU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdlib codec_bmain_rdin codec_bmain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdx_l13 codec_bmain_rdx_l12.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma r12t_ag : forall E E', env_agree 38 E E' -> env_agree 35 E E'.
Proof. intros E E' [HA HD]. split; [intros n Hn; apply HA; lia | exact HD]. Qed.

(* the cut at text_arg's entry, after j input bytes were taken *)
Ltac rd12t_fin B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k pv dv d HJ0 Hfr Hk Hmo HC Hops Hkat Hpd HAE HEE B2 B33 A2 A33 E35 E36 KE j :=
  lazymatch goal with
  | HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?Wx) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in
    let G1 := fresh "G1" in let G10 := fresh "G10" in let G11 := fresh "G11" in
    let HAf := fresh "HAf" in let A2f := fresh "A2f" in let A33f := fresh "A33f" in
    let F35 := fresh "F35" in let F36 := fresh "F36" in let KK := fresh "KK" in
    rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb; rd_chunk HS 33%nat 216 Cx;
    rewrite ?ew_ewset_other in Ca, Cb, Cx by lia; rewrite B2 in Ca, Cb; rewrite B33 in Cx;
    rewrite ?wvb_collapse in HJm;
    assert (HAf : env_agree 38 (bm_env g pos c regs2 ys) Ef) by (rewrite <- HEE; env_agree_chain HAE);
    assert (A2f : ew Ef 2 = Z_to_bv 64 sp1) by (rewrite (rd_ag 38 _ _ 2 HAf ltac:(lia)), <- HEE; exact A2);
    assert (A33f : ew Ef 33 = Z_to_bv 64 (FA g pos))
      by (rewrite (rd_ag 38 _ _ 33 HAf ltac:(lia)), <- HEE; exact A33);
    assert (F35 : ew Ef 35 = Z_to_bv 64 (e_p g + c))
      by (rewrite (rd_ag 38 _ _ 35 HAf ltac:(lia)), <- HEE; exact E35);
    assert (F36 : ew Ef 36 = Z_to_bv 64 (e_n g - c))
      by (rewrite (rd_ag 38 _ _ 36 HAf ltac:(lia)), <- HEE; exact E36);
    rreg HS (1%bv : bv 5) G1; rreg HS (10%bv : bv 5) G10; rreg HS (11%bv : bv 5) G11;
    rewrite ?ew_ewset_other in G10, G11 by lia; rewrite B2 in G10; rewrite B33 in G11;
    apply (r12_exit B MT K XM_LIB LAWS g pos sp1 24 28 c ys ly2 S2 W2 regs2 mem2 md2 k Ef ssf msf _ BM_text_arg _
      HJ0 Hfr Hk Hmo HC HJm (r12t_ag _ _ HAf) HS ltac:(reflexivity) ltac:(reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) KE);
    assert (KK : forall x, FA g pos + 192 <= x < FA g pos + 376 -> ~ (FA g pos + 216 <= x < FA g pos + 256) ->
      aview tfibsegs (w_H Wx) (ms_mem msf) x = aview tfibsegs (w_H Wx) mem2 x)
      by (intros x Hx1 Hx2; apply KE; [lia | unfold rd_zone; lia]);
    split;
    [ exact (r12_ops g pos c regs2 ys Ef ssf Wx msf ops (r12t_ag _ _ HAf) HS ltac:(reflexivity) Hops) |];
    lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 216 (CVal 4 ?va)) =>
      exists (c + j), pv, dv, d, (bv_unsigned (sv_denot Ef va) mod 2 ^ 32);
      split;
      [ exact (rd_cur g sp1 c j Wx (ms_mem msf) Ef Ca Cb F35 F36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) |];
      split; [lia|]; split; [exact Hpd|]; split; [apply rd_u32_range|];
      split;
      [ apply (rd_kat g pos Wx mem2 (ms_mem msf) 12 pv dv (bv_unsigned (sv_denot Ef va) mod 2 ^ 32) 0 0 0
          (repeat 0 24) Hkat KK);
        [ apply rd_u32_range | lia | lia | lia | apply repeat_length
        | lazymatch goal with |- val_mem _ _ (?F + 192 + 24) 4 _ => replace (F + 192 + 24) with (F + 216) by lia end;
          exact (rd_chunk_u32 _ _ _ _ _ Cx)
        | apply (rd_kept4 g pos sp1 Wx mem2 _ 12 pv dv 24 28 28 Hkat); first [exact KE | lia]
        | apply (rd_kept4 g pos sp1 Wx mem2 _ 12 pv dv 24 28 32 Hkat); first [exact KE | lia]
        | apply (rd_kept4 g pos sp1 Wx mem2 _ 12 pv dv 24 28 36 Hkat); first [exact KE | lia]
        | destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _); cbn [kz_bytes k_rdZ] in Vy;
          apply (rd_garr8_kept_k g pos sp1 24 28 Wx mem2 _ 40 (repeat 0 24) KE);
          [lia | lia | lia | lia | rewrite repeat_length; cbn; lia | rewrite repeat_length; cbn; lia | exact Vy] ] |];
      split; [rewrite G1; cbn [sv_denot]; first [reflexivity | vm_compute; reflexivity] |];
      split; [exact G10 | exact G11]
    end
  end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* 0x83ba0, text_arg's entry: k.a stored, the two arguments in a0 / a1 and the return address in ra *)
Definition rd12_Pc (g : ectx) (pos sp1 ops : Z)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\
exists c pv dv d a, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okB pv dv (Some d) /\ 0 <= a < 2 ^ 32 /\
k_at g pos (rdk 12 pv dv a 0 0 0 (repeat 0 24)) W2 mem2 /\
getr regs2 1 = w64 0x815e0 /\ getr regs2 10 = w64 (sp1 + 184) /\ getr regs2 11 = w64 (FA g pos + 80).

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis CTA : cdcU_text_arg_specX tfibsegs B MT BM_text_arg.

(* ---- 0x80fc0 .. 0x83ba0: the input byte, k.a and the call's arguments ---- *)
Lemma rd12_tb : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x80fc0 (rd12_Pa g pos sp1 ops) W2 c2 ->
  SRr tfibsegs W2 c2 (mcut B MT K XM_LIB g pos sp1 0 BM_text_arg (rd12_Pc g pos sp1 ops)).
Proof using TL LAWS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & (c & pv & dv & d & Hcur & Hc1 & Hpd & Hkat))).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
set (ys := rd_ys g c 1).
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys (rd_AF 1) 0x80fc0 24 28 []
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl (rd_AF_ok g pos c regs2 1)) as [HS SHOK].
assert (HAE : env_agree 38 (bm_env g pos c regs2 ys) (bm_env g pos c regs2 ys)) by apply env_agree_refl.
assert (EYall : forall j, (j < 1)%nat ->
  ew (bm_env g pos c regs2 ys) (BM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)))
  by exact (rd_EY g pos c regs2 1).
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (A2 : ew E 2 = Z_to_bv 64 sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. reflexivity. }
assert (A33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply bm_ew_F).
assert (B2 : bv_unsigned (ew E 2) = sp1) by (rewrite A2; apply unsigned_lit_small; lia).
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite A33; apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (bm_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (bm_ew_SB g pos c regs2 ys)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 28 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 0x80fc0) with (Z_to_bv 64 0x80fc0).
(* 0x80fc0 ld a1,192(s1); 0x80fc4 beqz a1 *)
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 0x83ba0. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd_brn Hb1 E36.
- (* no byte left: 0x815cc li a0,0; k.a = 0 *)
  cwj_run_to ltac:(rdj_awr B2 B33 EFA) 0x83ba0. cw_keep ltac:(rdj_kwr B2 B33).
  rd12t_fin B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k pv dv d
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd HAE HEE B2 B33 A2 A33 E35 E36 KE 0.
- (* a byte is left: its check, the mask, 0x815d0 *)
  rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EYall HSEP.
  cwj_run_to ltac:(rdj_awr B2 B33 EFA) 0x83ba0; try (rd_obl LAWS HJ0 Hfr HC c E35 E32).
  cw_keep ltac:(rdj_kwr B2 B33).
  rd12t_fin B MT K XM_LIB LAWS g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k pv dv d
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd HAE HEE B2 B33 A2 A33 E35 E36 KE 1.
Qed.

(* ---- the call of text_arg, to 0x815e0 ---- *)
Lemma rd12_tc : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 BM_text_arg (rd12_Pc g pos sp1 ops) W2 c2 ->
  SRr tfibsegs W2 c2 (mcut B MT K XM_LIB g pos sp1 0 0x815e0 (rd12_Pb g pos sp1 ops)).
Proof using MTL LAWS CTA.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & (c & pv & dv & d & a & Hcur & Hc1 & Hpd & Ha & Hkat & R1 & R10 & R11))).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof Hcur as (Hc & C184 & C192).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
set (dat := skipn (Z.to_nat c) (map (fun b : byte => bv_unsigned b) (e_pl g))).
set (tj := r13_cur W2 mem2 (FA g pos + 80) 65).
destruct (r13_ta_pre B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c ly2 S2 W2 mem2 md2 kev
  HC HJ Hfr HJ Hfr HPerm0 ltac:(lia)
  (bm_bs_text B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 HC))
  as (TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8 & TA9 & TA10 & TA11 & TA12 & TA13).
fold dat in TA1, TA2, TA3, TA4, TA5, TA6, TA10, TA11, TA12.
fold tj in TA8, TA9.
assert (Usp : spZ regs2 = sp1).
{ pose proof HC as (_ & _ & R2 & _). unfold spZ. rewrite R2. apply unsigned_lit_small. lia. }
eapply SRr_bind.
{ eapply (CTA LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly2 S2 W2 mem2 md2 kev regs2 (sp1 + 184) (FA g pos + 80) (e_p g + c) dat tj).
  - apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev TB_text_arg 0x815e0
      HJ Hfr Hk HC R1 ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(unfold TB_text_arg; lia)
      satU_T_main_text_arg).
  - exact R10.
  - exact TA13.
  - rewrite Usp. exact TA1.
  - exact C184.
  - rewrite TA2. replace (sp1 + 184 + 8) with (sp1 + 192) by lia. exact C192.
  - exact TA3.
  - exact TA4.
  - exact TA5.
  - rewrite Usp. exact TA6.
  - exact R11.
  - rewrite Usp. exact TA7.
  - exact TA8.
  - exact TA9.
  - exact TA10.
  - exact TA11.
  - exact TA12. }
cbv beta. intros W3 c3 Hwle HP.
destruct HP as (ly3 & S3 & regs3 & mem3 & md4 & -> & HJ4 & HPR & Hfrs & HPerm4 & HIO & HMO4 & KT & Vip & Vin & Gtx).
unfold EV_CDC in HJ4. rewrite Z.add_0_r in HJ4.

destruct (r12_call_kept B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev TB_text_arg
  (fun x => sp1 + 184 <= x < sp1 + 184 + 16 \/ FA g pos + 80 <= x < FA g pos + 80 + 65)
  ly3 S3 W3 regs3 mem3 md4 kev HJ Hfr HC
  ltac:(intros x Hx; cbv beta in Hx; lia) HJ4 HPR HPerm4 KT) as (HC3 & KF).
rewrite R1. cbn [sv_denot].
change (mkCfg (mkst regs3 (w64 0x815e0) mem3 (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs 0x815e0 regs3 mem3 md4).
apply SRr_ret.
apply (bm_mcut B MT K XM_LIB g pos sp1 0 0x815e0 _ ly3 S3 W3 regs3 mem3 md4 kev HJ4
  ltac:(rewrite Hfrs; exact Hfr) Hk (mo_le_trans MT MTL _ _ _ 0 0 Hmo HMO4) HC3).
cbv beta.
assert (Hused : (text_usedZ dat <= length dat)%nat) by apply r12_used_le.
assert (Hlen : Z.of_nat (length dat) = e_n g - c) by exact TA2.
split.
- destruct Hops as (Hops & R20). split; [exact Hops|].
  assert (H20 : getr regs3 20 = getr regs2 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
  rewrite H20. exact R20.
- exists (c + Z.of_nat (text_usedZ dat)), pv, dv, d, a, (r12_tb dat tj).
  split.
  { split; [lia|]. split.
    - replace (e_p g + (c + Z.of_nat (text_usedZ dat))) with (e_p g + c + Z.of_nat (text_usedZ dat)) by lia.
      exact Vip.
    - replace (e_n g - (c + Z.of_nat (text_usedZ dat))) with (Z.of_nat (length dat - text_usedZ dat)%nat)
        by (rewrite Nat2Z.inj_sub by exact Hused; lia).
      replace (sp1 + 192) with (sp1 + 184 + 8) by lia. exact Vin. }
  split; [exact Hpd|]. split; [exact Ha|].
  split.
  { apply (k_at_kept g pos (rdk 12 pv dv a 0 0 0 (repeat 0 24)) W2 W3 mem2 mem3 Hkat).
    intros x Hx. apply KF; [lia|]. cbv beta. lia. }
  split; [exact Gtx|].
  split; [exact (r12_tb_len dat tj TA9) | apply r12_tb_in0].
Qed.

(* ---- the two parts chained ---- *)
Lemma rd12_ta : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x80fc0 (rd12_Pa g pos sp1 ops) W2 c2 ->
  SRr tfibsegs W2 c2 (mcut B MT K XM_LIB g pos sp1 0 0x815e0 (rd12_Pb g pos sp1 ops)).
Proof using MTL TL LAWS CTA.
intros g pos sp1 ops W2 c2 H.
eapply SRr_bind; [exact (rd12_tb g pos sp1 ops W2 c2 H)|].
intros W3 c3 _ H3. exact (rd12_tc g pos sp1 ops W3 c3 H3).
Qed.
End b.
End a.
