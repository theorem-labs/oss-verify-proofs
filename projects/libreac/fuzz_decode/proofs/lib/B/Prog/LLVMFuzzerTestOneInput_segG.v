(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segA.v, with its module paths and module names changed; 191 of its 227 lines of code are new or changed and 587 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segG: segment group 7 (up) of the image-B walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, +0x840 .. +0x968: llvm_b_up_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v, from
   llvm_b_st_840 (the return of reac_upstream_channels) to llvm_b_st_96c (the return of reac_upstream_decode #3).

   The walk, in code order (each piece in its own file):
   - +0x840 .. +0x8a4, the channel-count check and its abort edge +0x8a0 (segX_up_a up_phaseA, arithmetic in
     segX_up_arith / segX_up_den, the multiplier at 0x10338 in segX_up_rom);
   - +0x8a4 .. malloc #3 (+0x8c4) and the malloc itself (segX_up_b up_B1, up_malloc_call);
   - +0x8c8 .. __asan_memset (+0x8d8), the NULL check +0x8c8 refuted (segX_up_c up_B2), and the memset
     (segX_up_d up_memset_step);
   - the two refusing reac_upstream_decode calls +0x8e8 / +0x8fc (segX_up_c up_C1 / up_C2, segX_up_d up_ud_step)
     and their abort edges +0x904 / +0x908 (segX_up_c up_D);
   - the scan loop L5 +0x918 .. +0x958, its UBSan guard +0x918, its in-line ASan report +0x954 and its abort edge
     +0x958, then the third call's entry (segX_up_loop up_loop);
   - reac_upstream_decode #3 (+0x968, segX_up_d up_ud_step), whose return is llvm_b_st_96c.
   Between malloc #3 and the end the walk carries segX_up_d's up_inv; the fill 0xa5 of the upstream buffer is
   carried beside it. Call-site discharges: YC85.v amalloc04_sub (malloc), crt1's c1e_memset_call (memset),
   leafb's dec_leafb_upstream_decode (the three leaf calls). Templates: a Theorem Labs lane's Pa walks
   (a working branch CtrlIdentityPollBlock.v, GrantBuildSweepWalk.v) and cgif's ASan walk of
   LLVMFuzzerTestOneInput (origin/ossv/recipes lib/A/ACf0.v, ACf2.v). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa
  DecodeBImg DecodeBPaLib check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs
  reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_upstream_decode_c reac_decode_c LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs
  LLVMFuzzerTestOneInput_segX_up_arith LLVMFuzzerTestOneInput_segX_up_den LLVMFuzzerTestOneInput_segX_up_kit
  LLVMFuzzerTestOneInput_segX_up_a
  LLVMFuzzerTestOneInput_segX_up_b LLVMFuzzerTestOneInput_segX_up_c LLVMFuzzerTestOneInput_segX_up_loop
  LLVMFuzzerTestOneInput_segX_up_d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ZBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* A callee-saved register through a call. *)
Lemma up_pres : forall regs regs2, aregs_preserved regs regs2 ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 HP r Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Ltac cs_tac := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.
Ltac in_tac := repeat (first [left; reflexivity | right]).

(* s9 = s7 ^ -1 (+0x914) is ~s7. *)
Lemma up_xor_m1 {rc : YM05.RunCeil} : forall regs upb, YK11.getr regs 23 = w64 upb -> 0 <= upb < 18446744073709551616 ->
  sv_denot (EUP regs) (SAlu ALU_XOR (SOff 23 0) (SLit (-1))) = w64 (Z.lnot upb).
Proof.
intros regs upb H23 Hu. apply bv_eq. change (bv_unsigned (sv_denot (EUP regs) (SAlu ALU_XOR (SOff 23 0) (SLit (-1)))))
  with (U (EUP regs) (SAlu ALU_XOR (SOff 23 0) (SLit (-1)))).
rewrite U_SAlu, (up_U_atom regs 23 23%bv upb eq_refl H23 Hu), U_SLit. cbn [zalu_raw].
change (zcanon (-1)) with 18446744073709551615. rewrite ZBridge.zb_lxor_ones by lia.
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite up_lnot_mod by lia. apply zcanon_id. change M64 with 18446744073709551616. lia.
Qed.

Section sg. Context {rc : YM05.RunCeil}.
(* lib/B/Prog/LLVMFuzzerTestOneInput_segs.v Section seg, variable for variable. *)
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* The frame invariant at other registers and another model, the memory unchanged. *)
Lemma up_core_regs : forall cx ly S W regs mem md k regs' md',
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head decodesegsB0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem md' k ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 -> YK11.getr regs' 8 = YK11.getr regs 8 ->
  YK11.getr regs' 9 = YK11.getr regs 9 ->
  dec_b_core B cx ly S W regs' mem md' k.
Proof.
intros cx ly S W regs mem md k regs' md' Hcore HJ' K2 K3 K4 K8 K9.
pose proof Hcore as (_ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFp & _ & Hpay & _).
apply (ex_core_kept B cx ly S W regs mem md k ly S W regs' mem md' k Hcore HJ' Hfr K8 K9);
  [unfold spZ; rewrite K2; reflexivity | exact K3 | exact K4 | intros; reflexivity | intros; reflexivity
  | intros a Ha; exact (HFp a Ha) | exact Hpay | intros; reflexivity].
Qed.

Ltac incl_tac := intros x Hx; cbn [In up_keepI] in Hx;
  repeat (destruct Hx as [<- | Hx]; [cbn; in_tac|]); destruct Hx.

Theorem llvm_b_up_ok :
  llvm_b_up_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_up_stmt.
intros HPCM HUTR HCELLS HROWN HNOERR LAWS ML MTL AMS AMAL HLEAF cx W' c' HBASE HROM HST.
destruct HST as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & Hcore & Hperm & Hres &
  Hmle & Hmok & Hfrs_s & H10 & H22 & H27 & Hmode & Hfsh & Hgarr & S24 & S32 & S40 & S80 & S112).
destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HBASE)
  as (Hraok & HRA & Hgp0 & Htp0 & Hstk0 & Hch & Hpn & Hnlen & Hfrs0 & Hnev0 & Hlive0 & _ & _ & _ & Hra4).
assert (Hn : 0 <= d_n cx < 67108864) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
assert (Hpay0 : 0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))
  by (intros Hn0; destruct Hpn as [[Hq _] | [_ Hq]]; [lia | exact Hq]).
assert (HB : up_base RA_LLVMF cx)
  by exact (conj Hch (conj Hstk0 (conj Hra4 (conj HRA (conj Hnev0 (conj Hlive0 (conj Hn Hnlen))))))).
assert (Hmem0 : up_mem cx W' mem' res mode nch ns)
  by exact (conj Hfrs_s (conj Hmode (conj Hfsh (conj Hgarr (conj S24 (conj S32 (conj S40 (conj S80 S112)))))))).
pose proof (@alloc_ceiling_val rc) as (HAC & _).
(* +0x840 .. +0x8a4 *)
rewrite (@up_cfg_eq fx' rc regs' mem' md' 0x840).
apply (@up_phaseA fx' rc B LAWS cx ly' S' W' regs' mem' md' _ Hcore S32 H22 H10 Hn HCELLS).
intros msA mdA HmA HmkA HkA H18A H21A HJA.
rewrite HmkA.
assert (HcoreA : dec_b_core B cx ly' S' W' (ms_regs msA) mem' mdA dec_ev_840)
  by (apply (up_core_regs cx ly' S' W' regs' mem' md' dec_ev_840 _ mdA Hcore HJA); apply HkA; in_tac).
(* +0x8a4 .. malloc #3 *)
apply (@up_B1 fx' rc B LAWS W' (ms_regs msA) mem' mdA (up_r cx) _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
  (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_840 HJA H21A
  (up_result_range (up_len cx) ltac:(unfold UP_NMAX, up_len, dec_b_len; lia))).
intros rB mdB HB10 HB24 HBra HkB HJB.
assert (HcoreB : dec_b_core B cx ly' S' W' rB mem' mdB dec_ev_840)
  by (apply (up_core_regs cx ly' S' W' _ mem' mdA dec_ev_840 rB mdB HcoreA HJB); apply HkB; in_tac).
rewrite <- HPCM.
apply (@up_malloc_call fx' rc B MT RA_LLVMF LAWS MTL HUTR HCELLS HROWN HNOERR (AMAL fx') cx ly' S' W' rB mem' mdB res
  mode nch ns _ HB HROM HcoreB Hperm Hres Hmle Hmok Hmem0 HB10 HBra).
{ rewrite (HkB 18%bv ltac:(in_tac)). exact H18A. }
{ rewrite (HkB 21%bv ltac:(in_tac)). exact H21A. }
{ rewrite (HkB 22%bv ltac:(in_tac)), (HkA 22%bv ltac:(in_tac)). exact H22. }
{ exact HB24. }
{ rewrite (HkB 27%bv ltac:(in_tac)), (HkA 27%bv ltac:(in_tac)). exact H27. }
intros W2 rM mM mdM ly2 S2 upb HcoreM HpermM HblM Hupb HmleM HmokM HmemM HM10 HM18 HM21 HM22 HM24 HM27.
assert (HinvM : up_inv B MT cx res mode nch ns upb ly2 S2 W2 rM mM mdM)
  by exact (conj HcoreM (conj HpermM (conj Hres (conj Hupb (conj HmleM (conj HmokM (conj HmemM
    (conj HM18 (conj HM21 (conj HM22 (conj HM24 HM27))))))))))).
destruct (up_inv_blocks B MT LAWS cx res mode nch ns upb ly2 S2 W2 rM mM mdM Hn Hpay0 HinvM)
  as (HinU & HninU & HresU & HdresU & HdpayU & Huo & HcU).
pose proof HcoreM as (HJM & _).
(* +0x8c8 .. __asan_memset *)
apply (@up_B2 fx' rc B LAWS W2 rM mM mdM upb _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
  (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 dec_ev_96c HJM HM10 ltac:(lia)).
intros rB2 mdB2 HB211 HB212 HB223 HB2ra HkB2 HJB2.
pose proof (up_inv_run B MT cx res mode nch ns upb ly2 S2 W2 rM mM mdM rB2 mdB2 HinvM HJB2
  ltac:(intros y Hy; apply HkB2; revert y Hy; incl_tac)) as HinvB2.
apply (@up_memset_step fx' rc B MT LAWS cx res mode nch ns upb ly2 S2 W2 rB2 mM mdB2 _ AMS HCELLS HROWN HNOERR HROM
  Hn Hnlen Hpay0 HinvB2).
{ rewrite (HkB2 10%bv ltac:(in_tac)). exact HM10. }
{ exact HB211. }
{ rewrite HB212. exact HM24. }
{ exact HB2ra. }
intros rS mS mdS HinvS HPS HfillS.
assert (HS23 : YK11.getr rS 23 = w64 upb)
  by (rewrite (up_pres _ _ HPS 23%bv ltac:(cs_tac)), HB223; exact HM10).
pose proof HinvS as ((HJS & _) & _ & _ & _ & _ & _ & _ & HS18 & HS21 & HS22 & HS24 & HS27).
(* +0x8dc .. reac_upstream_decode #1 *)
apply (@up_C1 fx' rc B LAWS W2 rS mS mdS _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
  (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 dec_ev_96c HJS).
intros rC1 mdC1 HC110 HC111 HC112 HC1ra HkC1 HJC1.
pose proof (up_inv_run B MT cx res mode nch ns upb ly2 S2 W2 rS mS mdS rC1 mdC1 HinvS HJC1
  ltac:(intros y Hy; apply HkC1; revert y Hy; incl_tac)) as HinvC1.
apply (@up_ud_step fx' rc B MT LAWS cx res mode nch ns upb ly2 S2 W2 rC1 mS mdC1 0 upb 0x8ec _ HLEAF HCELLS HROWN
  HNOERR HROM Hn Hnlen Hpay0 HinvC1 (or_introl eq_refl) (or_intror eq_refl) HC110).
{ rewrite HC111. exact HS22. }
{ rewrite HC112. exact HS23. }
{ exact HC1ra. }
{ lia. }
{ reflexivity. }
intros rU1 mU1 mdU1 HinvU1 HPU1 HU110 HeffU1 _.
replace (reac_upstream_decode_c.up_ok 0 upb (up_len cx) (d_body cx)) with false in HU110, HeffU1 by reflexivity.
assert (HfillU1 : dec_b_filled W2 mU1 upb (up_uo cx)).
{ apply (up_filled_kept B MT LAWS cx res mode nch ns upb ly2 S2 W2 rC1 mS mdC1 mU1 (LeafCgKit.in_wr []) Hn Hpay0
    HinvC1 HeffU1); [intros a Ha; apply Exists_nil in Ha; exact Ha | exact HfillS]. }
pose proof HinvU1 as ((HJU1 & _) & _ & _ & _ & _ & _ & _ & HU118 & HU121 & HU122 & HU124 & HU127).
(* +0x8ec .. reac_upstream_decode #2 *)
apply (@up_C2 fx' rc B LAWS W2 rU1 mU1 mdU1 _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
  (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 dec_ev_96c HJU1).
intros rC2 mdC2 HC210 HC211 HC212 HC225 HC2ra HkC2 HJC2.
pose proof (up_inv_run B MT cx res mode nch ns upb ly2 S2 W2 rU1 mU1 mdU1 rC2 mdC2 HinvU1 HJC2
  ltac:(intros y Hy; apply HkC2; revert y Hy; incl_tac)) as HinvC2.
apply (@up_ud_step fx' rc B MT LAWS cx res mode nch ns upb ly2 S2 W2 rC2 mU1 mdC2 res 0 0x900 _ HLEAF HCELLS HROWN
  HNOERR HROM Hn Hnlen Hpay0 HinvC2 (or_intror eq_refl) (or_introl eq_refl)).
{ rewrite HC210. exact HU127. }
{ rewrite HC211. exact HU122. }
{ exact HC212. }
{ exact HC2ra. }
{ lia. }
{ reflexivity. }
intros rU2 mU2 mdU2 HinvU2 HPU2 HU210 HeffU2 _.
replace (reac_upstream_decode_c.up_ok res 0 (up_len cx) (d_body cx)) with false in HU210, HeffU2
  by (unfold reac_upstream_decode_c.up_ok; destruct (negb (res =? 0)); reflexivity).
assert (HfillU2 : dec_b_filled W2 mU2 upb (up_uo cx)).
{ apply (up_filled_kept B MT LAWS cx res mode nch ns upb ly2 S2 W2 rC2 mU1 mdC2 mU2 (LeafCgKit.in_wr []) Hn Hpay0
    HinvC2 HeffU2); [intros a Ha; apply Exists_nil in Ha; exact Ha | exact HfillU1]. }
pose proof HinvU2 as ((HJU2 & _) & _ & _ & _ & _ & _ & _ & HU218 & HU221 & HU222 & HU224 & HU227).
assert (HU223 : YK11.getr rU2 23 = w64 upb).
{ rewrite (up_pres _ _ HPU2 23%bv ltac:(cs_tac)), (HkC2 23%bv ltac:(in_tac)), (up_pres _ _ HPU1 23%bv ltac:(cs_tac)),
    (HkC1 23%bv ltac:(in_tac)). exact HS23. }
(* +0x900 .. +0x918 *)
apply (@up_D fx' rc B LAWS W2 rU2 mU2 mdU2 _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
  (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 dec_ev_96c HJU2).
{ rewrite (up_pres _ _ HPU2 25%bv ltac:(cs_tac)), HC225. exact HU110. }
{ exact HU210. }
intros rL mdL HL11 HL12 HL25 HkD HJD.
assert (HL25' : YK11.getr rL 25 = w64 (Z.lnot upb)) by (rewrite HL25; apply up_xor_m1; [exact HU223 | lia]).
(* the scan loop L5, then reac_upstream_decode #3 *)
refine (@up_loop fx' rc B LAWS W2 DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
  [(DEC_FCLASS, d_fpos cx)] ly2 S2 dec_ev_96c rL mU2 upb (up_uo cx) _ HinU Huo _ _ _ _ HL25' _
  (Z.to_nat (up_uo cx - 0)) 0 rL mdL eq_refl ltac:(lia) HJD HL11 HL12 (fun x _ => eq_refl)).
{ intros j Hj. exact (HfillU2 j Hj). }
{ rewrite (HkD 18%bv ltac:(in_tac)). exact HU218. }
{ rewrite (HkD 23%bv ltac:(in_tac)). exact HU223. }
{ rewrite (HkD 24%bv ltac:(in_tac)). exact HU224. }
intros rT mdT HT10 HT11 HT12 HTra HkT HJT.
pose proof (up_inv_run B MT cx res mode nch ns upb ly2 S2 W2 rU2 mU2 mdU2 rT mdT HinvU2 HJT
  ltac:(intros y Hy; rewrite (HkT y ltac:(revert y Hy; incl_tac)); apply HkD; revert y Hy; incl_tac)) as HinvT.
apply (@up_ud_step fx' rc B MT LAWS cx res mode nch ns upb ly2 S2 W2 rT mU2 mdT res upb 0x96c _ HLEAF HCELLS HROWN
  HNOERR HROM Hn Hnlen Hpay0 HinvT (or_intror eq_refl) (or_intror eq_refl)).
{ rewrite HT10, (HkD 27%bv ltac:(in_tac)). exact HU227. }
{ rewrite HT11, (HkD 22%bv ltac:(in_tac)). exact HU222. }
{ rewrite HT12, (HkD 23%bv ltac:(in_tac)). exact HU223. }
{ exact HTra. }
{ lia. }
{ reflexivity. }
intros r3 m3 md3 Hinv3 HP3 H310 Heff3 HX3.
apply SRr_ret.
pose proof Hinv3 as (Hcore3 & Hperm3 & _ & _ & Hmle3 & Hmok3 & Hmem3 & H318 & H321 & H322 & H324 & H327).
pose proof Hmem3 as (Hfrs3 & Hmode3 & Hfsh3 & Hgarr3 & S324 & S332 & S340 & S380 & S3112).
exists fx', ly2, S2, r3, m3, md3, res, upb, mode, nch, ns.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact Hcore3|]. split; [exact Hperm3|].
split; [exact Hres|]. split; [lia|]. split; [exact Hmle3|]. split; [exact Hmok3|]. split; [exact Hfrs3|].
split; [exact H310|]. split; [exact H318|]. split; [exact H321|]. split; [exact H322|].
split.
{ rewrite (up_pres _ _ HP3 23%bv ltac:(cs_tac)), (HkT 23%bv ltac:(in_tac)), (HkD 23%bv ltac:(in_tac)). exact HU223. }
split; [exact H324|].
split.
{ rewrite (up_pres _ _ HP3 25%bv ltac:(cs_tac)), (HkT 25%bv ltac:(in_tac)). exact HL25'. }
split; [exact H327|]. split; [exact Hmode3|]. split; [exact Hfsh3|]. split; [exact Hgarr3|].
split; [exact HX3|].
split.
{ intros Hnok. change (dec_b_len (d_n cx)) with (up_len cx) in Hnok. rewrite Hnok in Heff3.
  apply (up_filled_kept B MT LAWS cx res mode nch ns upb ly2 S2 W2 rT mU2 mdT m3 (LeafCgKit.in_wr []) Hn Hpay0
    HinvT Heff3); [intros a Ha; apply Exists_nil in Ha; exact Ha | exact HfillU2]. }
exact (conj S324 (conj S332 (conj S340 (conj S380 S3112)))).
Qed.
End sg.
