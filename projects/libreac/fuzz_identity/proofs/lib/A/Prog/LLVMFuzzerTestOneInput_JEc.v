(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_JE.v, with its addresses and numbers changed; 232 of its 474 lines of code are new or changed and 1220 lines of the source are left out. *)
(* Sub-run C of piece E of segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan, build A):
   0x81d00 .. 0x81d8c (BASE + 0x15f4 .. BASE + 0x1680), jeC_stmt of LLVMFuzzerTestOneInput_JE.v.
     0x81d00 .. 0x81d10  a2 = ld, a3 = object 9 (" in / "), a4 = 7, a6 = the shadow base (mf + 176)
     0x81d14 .. 0x81d4c  s7 = 1 .. 6: exp_dp[ld] = s2 (the shadow of exp_dp is zero, SH_jeC), then s2 = obj9[s7]
                         (the shadow cell of object 9 is 7, the last granule of a 7-byte global, so the slow path
                         at 0x81d60 .. 0x81d68 compares s7 < 7), ld = ld + 1
     0x81d50 .. 0x81d84  ld stored back, a0 = exp_dp, a1 = &ld, a2 = out, a3 = 1, s7 = 1
     0x81d88             put_dec(exp_dp, &ld, out, 1) (je_call)
   One token run covers 0x81d00 .. 0x81d88: the counter s7 is concrete, and the shadow cell of object 9 is a
   region at the declared shadow atom 36, so the loop unrolls. Object 9's bytes come from HIMG (llvmf_img), its
   shadow cell from GM with G_IN. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_JE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow-cell arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x81d00 ------------------------------------------------------------------------ *)
(* Atoms: 32 = ld, 33 = out, 34 = exp_dp + ld (the alias of s8 + a2), 35 = the shadow base, 36 = the shadow cell
   of object 9 (declared as (obj9 >> 3) + a6), A_OBJ 9 = object 9 itself (8-aligned). *)
Definition jeC_dp : YP09.region := YP09.mkRegion (Some 34%nat) 0 6 0 6 [].
Definition jeC_mf : YP09.region := YP09.mkRegion (Some 9%nat) 168 208 200 208
  [YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 35 0));
   YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition jeC_o9 : YP09.region := YP09.mkRegion (Some (A_OBJ 9)) 0 7 0 0
  [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 105));
   YP09.mkChunk 2 (CVal 1 (SLit 110)); YP09.mkChunk 3 (CVal 1 (SLit 32));
   YP09.mkChunk 4 (CVal 1 (SLit 47)); YP09.mkChunk 5 (CVal 1 (SLit 32));
   YP09.mkChunk 6 (CVal 1 (SLit 0))].
Definition jeC_s9 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 7))].
Definition jeC_facts : facts :=
  mkFacts [(35%nat, mkAF SB_E SB_E 0); (32%nat, mkAF 4 25 0); (33%nat, mkAF 0 40 0);
           (34%nat, mkAF 4096 (2 ^ 47 - 64) 0); (24%nat, mkAF 4096 (2 ^ 47 - 64) 0);
           (9%nat, mkAF 0x7fff7f804000 (2 ^ 47) 0); (A_OBJ 9, mkAF IMG_LO IMG_TOP 3)] []
    [(SAlu ALU_ADD (SOff 24 0) (SOff 32 0), SOff 34 0);
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff (A_OBJ 9) 0) (SLit 3)) (SOff 35 0), SOff 36 0)].
Definition jeC_regs : list sv := sr_set (sr_set sr_atoms 18%bv (SLit 32)) 23%bv (SLit 1).
Definition ss_jeC : sstate := mkSS 0x15f4 jeC_regs [jeC_dp; jeC_mf; jeC_o9; jeC_s9] None jeC_facts.
Definition Bx_C : sv := SOff 35 0.
Definition SH_jeC : list shent := [mkSHE 34 0 6].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v / _JE.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* _JE.v's names, at this Section's variables *)
#[local] Notation je_call := (LLVMFuzzerTestOneInput_JE.je_call B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK
  EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HSTK HEV LAWS HPD).

Let RUN := paj_run B LAWS.

Lemma jeC : LLVMFuzzerTestOneInput_JE.jeC_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold LLVMFuzzerTestOneInput_JE.jeC_stmt.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HK HPRE HG Hwok Hnm21 HM Vout Vsh
  Rsp Rs1 Rgp Rtp R24 R18 R23.
pose proof HG as HG0.
destruct HG0 as (HSF0 & HSF1 & HSFapp & HSF64 & Hmf0 & Hmfb & Hmf32 & Hsp47).
pose proof HM as (ZNM & ZDP & BNM & BDP & Vld).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity.
assert (HWS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof HJ as (HAR & Hly & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
pose proof (JEModel.nm_pos (e_pl g)) as Hspos.
destruct (JEModel.in_range (e_pl g) Hwok) as [Hin0 Hout0].
pose proof (JEModel.dec_len1 (SlotModel.t_in (e_pl g)) Hin0) as Hdl.
pose proof (pa_obj_img 9%nat ltac:(lia)) as HOB.
(* object 9's bytes, from the read-only image at the current state *)
pose proof HPRE as HPRE0.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE0.
destruct HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
pose proof (HIMG W2 mem2
  (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ HAROS))) as HIM.
unfold llvmf_img in HIM.
destruct HIM as (_ & _ & _ & _ & _ & _ & _ & _ & HO9 & _).
(* object 9's shadow cell: the one granule of a registered 7-byte global holds 7 (GM, G_IN) *)
destruct (GM ly2 S2 W2 mem2 md2 (VAL (A_OBJ 9)) 7 G_IN HAR) as (H9al & _ & HBS).
pose proof (HBS 0 ltac:(lia)) as HB9. clear HBS.
change (if 0 <? 7 / 8 then 0 else 7 mod 8) with 7 in HB9.
rewrite Z.add_0_r in HB9. unfold shadow_of_addr in HB9.
set (SF := SFa g pos) in *.
set (s := SlotModel.n_EXP_NM (e_pl g)) in *.
set (P := s ++ SlotModel.str_bytes " ("%string ++ IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1) in *.
set (L := Z.of_nat (length P)) in *.
set (A9 := VAL (A_OBJ 9)) in *.
set (sa := SHADOW_OFF + A9 / 8) in *.
assert (HL : 4 <= L <= 25).
{ unfold L, P. rewrite !length_app, JEModel.s1_len. unfold put_dec_c.dec_len in Hdl.
  clear - Hdl Hspos Hnm21. lia. }
assert (Hdp0 : 4096 <= SF + V_dp) by (unfold V_dp; clear - HSF0; lia).
assert (Hsa : SHADOW_OFF + 8192 <= sa <= SHADOW_OFF + 783360) by (unfold sa; clear - HOB; lia).
(* the destination bytes are none of object 9's: their shadow is 0, object 9's is 7 *)
assert (HD9 : SF + V_dp + L + 6 <= A9 \/ A9 + 7 <= SF + V_dp + L).
{ destruct (Z_le_gt_dec (SF + V_dp + L + 6) A9) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (A9 + 7) (SF + V_dp + L)) as [H2|H2]; [right; exact H2|].
  exfalso.
  set (x := Z.max (SF + V_dp + L) A9).
  assert (Hx1 : A9 <= x < A9 + 7) by (unfold x; clear - H1 H2 HL; lia).
  assert (Hx2 : SF + V_dp + L <= x < SF + V_dp + L + 6) by (unfold x; clear - H1 H2 HL; lia).
  clearbody x.
  assert (Hi : 0 <= (x - (SF + V_dp)) / 8 < N_dp / 8)
    by (unfold N_dp; clear - Hx2 HL; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  pose proof (ZDP _ Hi) as Z0.
  assert (Ec : shadow_of_addr SHADOW_OFF (SF + V_dp) + (x - (SF + V_dp)) / 8 = sa).
  { unfold shadow_of_addr, sa, V_dp. clear - Hx1 Hx2 H9al HSF64. lia. }
  rewrite Ec, HB9 in Z0. discriminate Z0. }
assert (HDs : SF + V_dp + L + 6 <= sa \/ sa + 1 <= SF + V_dp + L).
{ destruct HSFapp as (_ & [HLo | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, V_dp in *.
  - left. clear - HLo HL Hsa. unfold SHADOW_OFF in *. lia.
  - right. clear - HH HL Hsa. unfold SHADOW_OFF in *. lia. }
(* the environment: atom 32 = ld, 33 = out, 34 = exp_dp + ld, 35 = the shadow base, 36 = obj9's shadow cell *)
remember (Eimg (Ereg regs2 [w64 L; w64 (SlotModel.t_out (e_pl g)); w64 (SF + V_dp + L); w64 SHADOW_OFF; w64 sa]))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32
  (Ereg regs2 [w64 L; w64 (SlotModel.t_out (e_pl g)); w64 (SF + V_dp + L); w64 SHADOW_OFF; w64 sa]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 L)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 (SlotModel.t_out (e_pl g)))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 (SF + V_dp + L))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 SHADOW_OFF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = w64 sa)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E9o : ew E (A_OBJ 9) = Z_to_bv 64 A9)
  by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
assert (E9 : ew E 9 = w64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (E24 : ew E 24 = w64 (SF + V_dp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9; apply je_unsigned; clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
assert (U34 : bv_unsigned (ew E 34) = SF + V_dp + L)
  by (rewrite E34; apply je_unsigned; unfold V_dp; clear - HSF0 HSF1 C1 HL; lia).
assert (U24 : bv_unsigned (ew E 24) = SF + V_dp)
  by (rewrite E24; apply je_unsigned; unfold V_dp; clear - HSF0 HSF1 C1; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply je_unsigned; unfold SHADOW_OFF; clear; lia).
assert (U36 : bv_unsigned (ew E 36) = sa)
  by (rewrite E36; apply je_unsigned; clear - Hsa; unfold SHADOW_OFF in *; lia).
assert (U32 : bv_unsigned (ew E 32) = L) by (rewrite E32; apply je_unsigned; clear - HL; lia).
assert (U33 : bv_unsigned (ew E 33) = SlotModel.t_out (e_pl g))
  by (rewrite E33; apply je_unsigned; clear - Hout0; lia).
assert (U9o : bv_unsigned (ew E (A_OBJ 9)) = A9)
  by (rewrite E9o; apply je_unsigned; clear - HOB; lia).
(* the symbolic state at 0x81d00 *)
assert (HS : st_ok_pi SEGS VAL E ss_jeC
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x15f4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jeC, jeC_regs. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [| intros X; discriminate X | rewrite R23; cbn [sv_denot]; reflexivity].
    apply regs_ok_pin; [exact ER | intros X; discriminate X | rewrite R18; cbn [sv_denot]; reflexivity].
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + unfold jeC_dp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
      split; [clear - Hdp0 HL; lia|]. split; [unfold V_dp; clear - HSF1 C1 HL; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFpres (SF + V_dp + L + o) ltac:(unfold V_dp; clear - Ho HL; lia))).
    + unfold jeC_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1 HES; lia|]. split; [clear - Hsp47 Hmfb; unfold e_sp0 in *; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres.
        clear - Ho Hmfb HWS. unfold e_sp0 in *. lia. }
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 33 0) (SlotModel.t_out (e_pl g))).
        -- apply je_sv. rewrite (je_U E 33 _ 0 E33), Z.add_0_r.
           rewrite Z.mod_small by (clear - Hout0; lia). reflexivity.
        -- cbn. clear - Hout0. lia.
        -- cbn. lia.
        -- exact Vout.
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 35 0) SHADOW_OFF).
        -- apply je_sv. rewrite (je_U E 35 _ 0 E35), Z.add_0_r.
           rewrite Z.mod_small by (unfold SHADOW_OFF; clear; lia). reflexivity.
        -- cbn. unfold SHADOW_OFF. clear. lia.
        -- cbn. lia.
        -- exact Vsh.
      * apply (chunk_ok_val SEGS E _ mf 200 8 (SOff 32 0) L).
        -- apply je_sv. rewrite (je_U E 32 _ 0 E32), Z.add_0_r.
           rewrite Z.mod_small by (clear - HL; lia). reflexivity.
        -- cbn. clear - HL. lia.
        -- cbn. lia.
        -- unfold M_n2 in Vld. exact Vld.
    + unfold jeC_o9, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9o.
      split; [clear - HOB; lia|]. split; [clear - HOB; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor;
        [|constructor; [|constructor]]]]]]].
      * apply (chunk_ok_val SEGS E _ A9 0 1 (SLit 32) 32);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 0%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 1 1 (SLit 105) 105);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 1%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 2 1 (SLit 110) 110);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 2%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 3 1 (SLit 32) 32);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 3%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 4 1 (SLit 47) 47);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 4%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 5 1 (SLit 32) 32);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 5%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ A9 6 1 (SLit 0) 0);
          [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HO9 6%nat ltac:(cbn; lia)))].
    + unfold jeC_s9, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U36.
      split; [clear - Hsa; unfold SHADOW_OFF in *; lia|]. split; [clear - Hsa; unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sa 0 1 (SLit 7) 7); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (je_vm1 (w_H W2) mem2 sa 7 HB9).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, jeC_dp, jeC_mf, jeC_o9, jeC_s9.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U34, U9, U9o, U36.
    repeat split; try exact I.
    all: clear - HD9 HDs HSF1 C1 HES Hmf0 HL HOB Hsa; unfold V_dp, SHADOW_OFF in *; lia.
  - unfold facts_ok, jeC_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U35, U32, U33, U34, U24, U9, U9o, !Z.pow_0_r, !Z.mod_1_r.
      change (2 ^ 3) with 8.
      unfold SB_E, SHADOW_OFF, V_dp.
      repeat split; try reflexivity;
        clear - HL Hout0 HSF0 HSF1 C1 Hmf0 Hmfb Hsp47 HES HOB H9al; unfold e_sp0 in *; lia.
    + split; [|split; [|exact I]].
      * rewrite (je_sv E (SOff 34 0) (SF + V_dp + L))
          by (rewrite (je_U E 34 _ 0 E34), Z.add_0_r; rewrite Z.mod_small;
              [reflexivity | unfold V_dp; clear - HSF0 HSF1 C1 HL; lia]).
        apply je_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (je_U E 24 _ 0 E24), (je_U E 32 _ 0 E32), !Z.add_0_r.
        unfold zcanon, M64. rewrite <- Zplus_mod. f_equal; clear; lia.
      * exact (shadow_decl_ok E (A_OBJ 9) 35 36 A9 SHADOW_OFF E9o ltac:(clear - HOB; lia) E35 E36). }
assert (SHOK : sh_ok SEGS Bx_C SH_jeC E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, SH_jeC. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E Bx_C 34 (SF + V_dp) N_dp (SF + V_dp + L) 0 6).
  - apply (range_addressable_sub _ _ (SF + V_dp) N_dp);
    [ apply zero_shadow_range; [unfold V_dp; clear - HSF64; lia | unfold N_dp; clear; lia | exact ZDP]
    | clear; lia | clear; lia ].
  - unfold Bx_C. rewrite (je_U E 35 _ 0 E35), Z.add_0_r.
    rewrite Z.mod_small; [reflexivity | unfold SHADOW_OFF; clear; lia].
  - rewrite (je_U E 34 _ 0 E34), Z.add_0_r.
    apply Z.mod_small. unfold V_dp. clear - HSF0 HSF1 C1 HL. lia.
  - clear - HL. lia.
  - unfold N_dp. clear - HL. lia.
  - intros x Hx Hb.
    destruct HSFapp as (_ & [HLo | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, V_dp in *.
    + clear - Hx Hb HLo HL. lia.
    + clear - Hx Hb HH HL. lia. }
pose proof HJ as HJ0.
unfold cfg_at. change (w64 (BASE + 0x15f4)) with (Z_to_bv 64 (BASE + 0x15f4)).
(* 0x81d00 .. 0x81d88: the loop, the counter stored back, put_dec's arguments; the run stops at the call *)
paj_run_tok RUN HS HJ SHOK Bspan_E;
 [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
     let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
   repeat first
   [ apply awr_ok_nil
   | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
   | eapply awr_ok_cons_gen;
     [ reflexivity | first [exact U34 | exact U9]
     | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa;
       first [ left; clear - Haa Hmfb HWS; unfold e_sp0 in *; lia
             | right; right; right; exists 4, pos; split; [left; reflexivity|];
               unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024; fold SF;
               left; clear - Haa HL HSF0; unfold V_dp in *; lia ]
     | ] ]
 | ].
(* what the run wrote: the six bytes of " in / " and ld + 6 *)
pose proof (je_kept_of W2 _ _ _ _
  (fun a => SF + V_dp + L <= a < SF + V_dp + L + 6 \/ mf + 200 <= a < mf + 208) HFr
  ltac:(je_win2 U34 U9)) as KEEPC.
cbn beta in KEEPC.
je_get_region HS 0%nat RDP. cbn [ms_mem restrict] in RDP.
je_get_region HS 1%nat RMF. cbn [ms_mem restrict] in RMF.
assert (B0 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 0) 1 32)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 0 1%N (SLit 32) 32 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B1 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 1) 1 105)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 1 1%N (SLit 105) 105 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B2 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 2) 1 110)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 2 1%N (SLit 110) 110 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B3 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 3) 1 32)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 3 1%N (SLit 32) 32 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B4 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 4) 1 47)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 4 1%N (SLit 47) 47 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (B5 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + L + 5) 1 32)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + L) _ 0 6 0 6 5 1%N (SLit 32) 32 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (VldC : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 200) 8 (L + 6)).
{ lazymatch type of RMF with region_ok _ ?Ef _ _ =>
    assert (E32f : ew Ef 32 = w64 L) by (repeat rewrite ew_ewset_other by lia; exact E32);
    exact (field_of_region Ef _ 9%nat mf _ 168 208 200 208 200 8%N (SOff 32 6) (L + 6) RMF
             ltac:(repeat rewrite ew_ewset_other by lia; exact U9) ltac:(je_in)
             ltac:(apply je_sv; rewrite (je_U Ef 32 _ 6 E32f); reflexivity) ltac:(clear - HL; cbn; lia)
             ltac:(cbn; lia)) end. }
clear RDP RMF.
(* the call put_dec(exp_dp, &ld, out, 1) at 0x81d88 *)
lazymatch type of HS with st_ok _ ?Ef _ _ =>
  assert (HAEf : env_agree 32
    (Ereg regs2 [w64 L; w64 (SlotModel.t_out (e_pl g)); w64 (SF + V_dp + L); w64 SHADOW_OFF; w64 sa]) Ef)
    by (destruct HAE as [HA1 HA2]; split;
        [intros n Hn; repeat rewrite ew_ewset_other by lia; exact (HA1 n Hn) | exact HA2]);
  pose proof (regs_kept_of_st_ok SEGS Ef _ _ regs2 _ JE_KEPT HS HAEf
    ltac:(vm_compute; reflexivity)) as RKC;
  assert (E24f : ew Ef 24 = w64 (SF + V_dp)) by (repeat rewrite ew_ewset_other by lia; exact E24);
  assert (E33f : ew Ef 33 = w64 (SlotModel.t_out (e_pl g))) by (repeat rewrite ew_ewset_other by lia; exact E33);
  assert (E9f : ew Ef 9 = w64 mf) by (repeat rewrite ew_ewset_other by lia; exact E9) end.
cbn [ms_regs restrict] in RKC.
pmkst HS.
rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
prreg HS (1%bv : bv 5) Rra.
je_reg HS (10%bv : bv 5) Ra0. je_reg HS (11%bv : bv 5) Ra1. je_reg HS (12%bv : bv 5) Ra2.
je_reg HS (13%bv : bv 5) Ra3. je_reg HS (23%bv : bv 5) Rs7.
lazymatch type of HS with st_ok _ ?Ef _ _ =>
  assert (Rs7' : getr (ms_regs ms) 23 = w64 1)
    by (rewrite Rs7; apply je_sv; rewrite (je_Ulit Ef); reflexivity) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_put_dec) rg mm mdx) Q) end.
(* what the piece carries into the call *)
set (s2 := SlotModel.str_bytes " in / "%string) in *.
assert (MC : jeM g pos mf (P ++ s2) W2 (ms_mem ms)).
{ split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZNM].
    intros i Hi. unfold N_nm in Hi. change (32 / 8) with 4 in Hi. apply KEEPC.
    - unfold shadow_of_addr, SHADOW_OFF, V_nm.
      assert (0 <= (SF + 528) / 8 <= SF + 528)
        by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
      clear - Hi H HSF0 HSF1 C1. lia.
    - intros [Hc|Hc].
      + apply (je_sh_out SF 1024 (SF + V_nm) i HSFapp HSF0 HSF1 ltac:(clear; lia)
                 ltac:(unfold V_nm; clear; lia) ltac:(unfold V_nm; clear; lia) ltac:(clear - Hi; lia)).
        unfold shadow_of_addr, SHADOW_OFF, V_nm, V_dp in *. clear - Hc HL. lia.
      + unfold shadow_of_addr, SHADOW_OFF, V_nm in *.
        assert (0 <= (SF + 528) / 8 <= SF + 528)
          by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
        clear - Hi H HSF0 HSF1 C1 Hmf0 HES Hc. lia. }
  split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZDP].
    intros i Hi. unfold N_dp in Hi. change (64 / 8) with 8 in Hi. apply KEEPC.
    - unfold shadow_of_addr, SHADOW_OFF, V_dp.
      assert (0 <= (SF + 592) / 8 <= SF + 592)
        by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
      clear - Hi H HSF0 HSF1 C1. lia.
    - intros [Hc|Hc].
      + apply (je_sh_out SF 1024 (SF + V_dp) i HSFapp HSF0 HSF1 ltac:(clear; lia)
                 ltac:(unfold V_dp; clear; lia) ltac:(unfold V_dp; clear; lia) ltac:(clear - Hi; lia)).
        unfold shadow_of_addr, SHADOW_OFF, V_nm, V_dp in *. clear - Hc HL. lia.
      + unfold shadow_of_addr, SHADOW_OFF, V_dp in *.
        assert (0 <= (SF + 592) / 8 <= SF + 592)
          by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
        clear - Hi H HSF0 HSF1 C1 Hmf0 HES Hc. lia. }
  split.
  { apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BNM].
    intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk. fold s in Hk.
    assert (Hk21 : 0 <= k <= 21) by (clear - Hk Hnm21; lia).
    apply KEEPC; [clear - Hk21 HSF0 HSF1 C1; unfold V_nm; lia
                 | clear - Hk21 HL HSF0 HSF1 C1 Hmf0 HES; unfold V_nm, V_dp; lia]. }
  split.
  { unfold bytes_at8. rewrite map_app. apply garr8_app. split.
    - apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BDP].
      intros k Hk. rewrite length_map in Hk. fold L in Hk.
      apply KEEPC; [clear - Hk HL HSF0 HSF1 C1; unfold V_dp; lia
                   | clear - Hk HL HSF0 HSF1 C1 Hmf0 HES; unfold V_dp; lia].
    - rewrite length_map. fold L. unfold s2. rewrite JEModel.s2_bytes.
      intros j Hj. cbn [length] in Hj.
      destruct j as [|[|[|[|[|[|j]]]]]]; cbn [nth Z.of_nat];
        [ split; [exact B0 | lia] | split; [exact B1 | lia] | split; [exact B2 | lia]
        | split; [exact B3 | lia] | split; [exact B4 | lia] | split; [exact B5 | lia] | lia ]. }
  rewrite length_app. unfold s2. rewrite JEModel.s2_len. unfold M_n2.
  replace (Z.of_nat (length P + 6)) with (L + 6) by (unfold L; clear; lia). exact VldC. }
eapply (je_call g pos mf ly2 S2 W2 _ (ms_mem ms) _ (P ++ s2) (SlotModel.t_out (e_pl g)) 0x1680).
- exact HJ.
- exact Hfrs.
- exact HK.
- exact HPRE.
- rewrite (RKC 2%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rsp.
- rewrite (RKC 3%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rgp.
- rewrite (RKC 4%bv ltac:(unfold JE_KEPT; cbn; tauto)). exact Rtp.
- exact HG.
- exact MC.
- rewrite length_app. unfold s2. rewrite JEModel.s2_len. clear - HL. unfold L in *. lia.
- rewrite length_app. unfold s2. rewrite JEModel.s2_len. clear - HL. unfold L in *. lia.
- clear - Hout0. lia.
- exact Hnm21.
- exact Rra.
- clear. lia.
- clear. reflexivity.
- rewrite Ra0. apply je_sv. rewrite (je_U _ 24 _ 0 E24f). f_equal; clear; lia.
- rewrite Ra1. apply je_sv. rewrite (je_U _ 9 _ 200 E9f). unfold M_n2. f_equal; clear; lia.
- rewrite Ra2. apply je_sv. rewrite (je_U _ 33 _ 0 E33f). f_equal; clear; lia.
- rewrite Ra3. apply je_sv. rewrite je_Ulit. reflexivity.
- (* after the call *)
  intros ly3 S3 W3 regs3 mem3 md3 HJ3 Hfr3 Hab3 HRP MD HKC.
  apply SRr_ret.
  exists ly3, S3, regs3, mem3, md3.
  split; [reflexivity|].
  split.
  { split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfrs|].
    split; [rewrite Hab3; apply Permutation_refl|].
    split.
    { intros a Ha Hw Hc. rewrite (HKC a Ha Hw Hc). apply KEEPC; [exact Ha|].
      intros [Hx|Hx]; [apply Hw; apply jeWJ_fr; fold SF; unfold V_dp in Hx; clear - Hx HL; lia
                      | apply Hw; apply jeWJ_cnt; clear - Hx; lia]. }
    split.
    { intros r Hr. rewrite (je_pres_keep _ _ HRP r Hr). exact (RKC r Hr). }
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 D2].
    destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [D3 D4].
    split; [intros fd; rewrite D3, D1; reflexivity | rewrite D4, D2; reflexivity]. }
  split.
  { unfold P in MD. rewrite <- !app_assoc in MD. exact MD. }
  exact (eq_trans (HRP 23 ltac:(unfold acallee_saved; lia)) Rs7').
Qed.

End c.
End b.
End a.
