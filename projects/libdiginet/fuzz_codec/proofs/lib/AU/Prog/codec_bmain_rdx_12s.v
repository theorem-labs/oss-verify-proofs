(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths, module names and addresses changed; 205 of its 244 lines of code are new or changed and 184 lines of the source are left out. *)
(* Segment RD12 (SCRIBBLE_TEXT) of the image-B walk of LLVMFuzzerTestOneInput (fuzz_codec.asan-ubsan), last part:
   from the inner cut rd12_Pb at 0x815e0 (text_arg returned; lib/AU/Prog/codec_bmain_rdx_l12.v) to ENC9 0x82734, the
   cut inv_enc .. 9 of lib/AU/Prog/codec_bmain_inv.v.
     0x815e0 .. 0x815f4  a0 = k.desk and its two UBSan checks (fuzz_codec.c:509): `bnez a0` over the trap at 0x815e8
                         and `andi a1,a0,7; beqz a1` over the trap at 0x815f4; the engine decides both from the desk
                         atom's fact (SPEC_C24 or SPEC_PC, 8-aligned: pd_okB);
     0x815f8 .. 0x8161c  a0 = k.desk + 10 and its instrumented check, a2 = the chars byte there, a0 = text (the spill
                         at 104(sp1)), a1 = k.bytes (the spill at 120(sp1)), `jal check_text_scribble` (0x83dbc,
                         ra = 0x81620);
     0x81620 .. 0x81628  k.kind = 9 (`sw`), `j 0x82734`.
   The first run starts by codec_bmain_rdlib.v's rd_start with no k window and the desk field (k + 16) as the atom
   37, the chars byte as the atom 38, and the one-byte region r12_chr at k.desk + 10 added. The check of k.desk + 10
   is left by the engine as an obligation; the four desk bytes at k.desk + 8 are marked usable in every state
   (codec_bmain_lem.v adesk_usable_of_pd). check_text_scribble is bound through cdcU_check_text_scribble_specX
   (lib/AU/Prog/CPgChkU.v) with the call-site witnesses of lib/AU/Prog/CPgSatU.v and lib/A/Prog/CPgSat.v; the cut
   facts are carried across the call by codec_bmain_headl.v's bm_call_kept_x (write set k.bytes = F + 232 ..
   F + 256). The second run writes k.kind only; the exit is codec_bmain_rdx_l12.v's r12_exit with
   k = rdk 9 pv dv a 0 0 0 (scribble_bytes tb chars).
   It is the image-A part lib/A/Prog/codec_amain_rd12s.v at image B. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdlib codec_bmain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_encl codec_bmain_rdx_l12.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition r12s_cs : list YP09.chunk := [YP09.mkChunk 208 (CVal 8 (SOff 37 0))].
Definition r12s_AF : list (nat * afact) := [(37%nat, mkAF 0x9dfc0 0x9dfe0 3); (38%nat, mkAF 0 255 0)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis CTS : cdcU_check_text_scribble_specX tfibsegs B MT BM_check_text_scribble.

Lemma rd12_ts : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x815e0 (rd12_Pb g pos sp1 ops) W2 c2 ->
  SRr tfibsegs W2 c2 (inv_enc B MT K XM_LIB g pos sp1 ops 9).
Proof using MTL TL LAWS GM IV ROB CTS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops &
  (c & pv & dv & d & a & tb & Hcur & Hpd & Ha & Hkat & Htb & Hltb & Hin0)).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof (r12_desk_range pv dv d Hpd) as (Hdv & Hdv8). unfold CM_SPEC_C24, CM_SPEC_PC in Hdv.
pose proof (r12_pd_chars pv dv d Hpd) as Hch.
set (ys := [dv; d_chars d]).
pose proof Hkat as ((_ & _ & V16 & _) & _). cbn [kz_desk rdk] in V16.
assert (EY0 : ew (bm_env g pos c regs2 ys) 37 = Z_to_bv 64 dv) by exact (bm_ew_y g pos c regs2 ys 0).
assert (EY1 : ew (bm_env g pos c regs2 ys) 38 = Z_to_bv 64 (d_chars d)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (Hcs : Forall (YP09.chunk_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) r12s_cs).
{ unfold r12s_cs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ (FA g pos) 208 8 (SOff 37 0) dv).
  - rewrite (bm_den_off _ 37 dv 0 EY0) by lia. rewrite Z.add_0_r. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - replace (FA g pos + 208) with (FA g pos + 192 + 16) by lia. exact V16. }
assert (HAF : atoms_ok (bm_env g pos c regs2 ys) r12s_AF).
{ unfold r12s_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EY0, EY1, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
  repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys r12s_AF 0x815e0 0 0 r12s_cs
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) Hcs ltac:(vm_compute; reflexivity) HAF) as [HS SHOK].
assert (HAE : env_agree 39 (bm_env g pos c regs2 ys) (bm_env g pos c regs2 ys)) by apply env_agree_refl.
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (subst E; rewrite (bm_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (B37 : bv_unsigned (ew E 37) = dv) by (rewrite EY0; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (bm_ew_SB g pos c regs2 ys)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 0 0 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof HJ as (HAR & _).
assert (HRO : arodata_ok B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 k (proj1 HC) HJ).
pose proof (r12_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (dv + 10) 1 192 376 HAR
  ltac:(rewrite Hfr; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(change (fs_frame_bytes 3) with 512; lia)) as GAP.
rewrite EFA in GAP.
(* the chars byte's region *)
pose proof (ast_ok_add_region tfibsegs E _ _ r12_chr HS eq_refl) as HS1.
specialize (HS1 ltac:(cbn [ms_mem restrict]; exact (r12_chr_ok B TL E W2 mem2 pv dv d HRO Hpd EY0 EY1))).
specialize (HS1 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in let ry2 := eval vm_compute in ry in change (all_disjoint Ey ry2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?B2, ?B33, ?B37; repeat split; lia)).
clear HS; rename HS1 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 0x815e0) with (Z_to_bv 64 0x815e0).
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 0x83dbc.
(* the instrumented check of k.desk + 10: the four desk bytes are marked usable in every state *)
all: lazymatch goal with
| |- range_addressable _ _ _ _ =>
  rewrite (cw_U_offx E 37 dv 10 EY0 ltac:(lia)), Z.mod_small by lia;
  let HU := fresh "HU" in let Hra := fresh "Hra" in
  destruct (adesk_usable_of_pd B pv dv d GM IV Hpd) as [HU _];
  destruct (HU ly2 S2 W2 mem2 md2 HAR) as [Hra _];
  eapply obl_of_range; [exact Hra | exact (cw_U_Bx E E32) | lia | lia]
| |- _ => idtac end.
cw_keep ltac:(rdj_kwr B2 B33).
destruct (rd_zone_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ0 Hfr HC) as
  (Happ & Hf4096' & Hfc & Hsp0 & Hspx & Hsp47 & Hclo').
rreg HS (1%bv : bv 5) Gra. rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
rewrite ?wvb_collapse in HJ.
(* the cut's facts at the call *)
lazymatch goal with
| HSx : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H _) ?msf) |- _ =>
  destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c (rdk 12 pv dv a 0 0 0 (repeat 0 24)) ly2 S2 W2 regs2 mem2 md2 k
    ys Ef ssf msf _ HJ0 Hfr HC Hops Hcur Hkat HJ
    ltac:(rewrite <- HEE; apply (env_agree_le 39 37); [lia | env_agree_chain HAE]) HSx ltac:(reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; repeat (first [left; reflexivity | right]))
    ltac:(intros aa Ha1 Ha2; apply KE; [exact Ha1 | unfold rd_zone; lia])) as (HCc & Hopsc & Hcurc & Hkatc)
end.
lazymatch goal with HSx : YP0l.st_ok _ _ ?ssx (restrict _ ?msx) |- _ =>
  let Hshape := fresh "Hshape" in
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HSx eq_refl) as Hshape;
  cbn [ss_pc] in Hshape; rewrite Hshape; clear Hshape end.
assert (Uspc : spZ (ms_regs ms) = sp1).
{ pose proof HCc as (_ & _ & R2' & _). unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. lia. }
assert (Htbc : garr8 tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 80) tb).
{ apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Htb].
  intros x Hx. rewrite Hltb in Hx. change (Z.of_nat 65) with 65 in Hx.
  apply KE; [lia | unfold rd_zone; lia]. }
pose proof Hkatc as ((V0c & _ & _ & _ & _ & _ & _ & G40c & _) & _). cbn [kz_kind kz_bytes rdk] in V0c, G40c.
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
(* check_text_scribble through its contract *)
eapply SRr_bind.
{ apply (CTS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly2 S2 W2 (ms_mem ms) _ k (ms_regs ms) (FA g pos + 80) (FA g pos + 232) (d_chars d) tb (repeat 0 24)).
  - apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ k TB_check_text_scribble 0x81620
      HJ Hfr Hk HCc Gra); first [lia | reflexivity | exact satU_T_main_check_text_scribble
                                 | apply Z.leb_le; vm_compute; reflexivity].
  - rewrite Ga0, B33. reflexivity.
  - rewrite Uspc. split; [lia|]. split; [exact Htbc|]. split; [exact Hin0|].
    rewrite Hltb. change (Z.of_nat 65) with 65.
    apply (satU_main_text_rd tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) _ sp1 TB_check_text_scribble pos (FA g pos)
      LLVMF_STK (e_sp0 g) (proj1 HJ) Hin3 EFA Hf64
      (bm_bs_text B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HCc));
      unfold TB_check_text_scribble, ESTACK; lia.
  - rewrite Hltb. change (Z.of_nat 65) with 65.
    eapply sat_cobj_frame; [exact Hin3 | exact EFA | lia | change (fs_frame_bytes 3) with 512; lia].
  - eapply sat_cobj_frame; [exact Hin3 | exact EFA | lia | change (fs_frame_bytes 3) with 512; lia].
  - rewrite Ga1, B33. reflexivity.
  - rewrite Uspc.
    apply (sat_frame_dst_in tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(3, pos)] ly2 S2 W2 (ms_mem ms) _ k sp1 TB_check_text_scribble 3 pos (FA g pos) 192 184 232 24
      HJ ltac:(left; reflexivity) Hin3 EFA Hf64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(change (fs_frame_bytes 3) with 512; lia)
      (bm_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HCc));
      unfold TB_check_text_scribble, ESTACK; lia.
  - replace (FA g pos + 232) with (FA g pos + 192 + 40) by lia. exact G40c.
  - apply repeat_length.
  - rewrite Ga2, EY1. reflexivity.
  - exact Hch.
  - left. rewrite Hltb. change (Z.of_nat 65) with 65. lia.
  - symmetry. apply scribble_agree.
  - rewrite Hfr. cbn. lia. }
cbv beta. intros W3 c3 Hwle HP.
destruct HP as (ly3 & S3 & regs3 & mem3 & md4 & -> & HJ4 & HPR & Hfrs3 & HPerm3 & HIO3 & HMLE3 & HK3 & HR3).
unfold EV_CDC in HJ4. rewrite Z.add_0_r in HJ4.
destruct (bm_call_kept_x B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ k c
  TB_check_text_scribble (fun x => FA g pos + 232 <= x < FA g pos + 232 + 24) ly3 S3 W3 regs3 mem3 md4 k HJ Hfr HCc Hcurc
  ltac:(intros aa Ha'; cbv beta in Ha'; lia) HJ4 HPR HPerm3 HK3) as (HC4 & Hcur4 & KF).
(* k at the return: the 24 bytes the call wrote, the rest kept *)
set (bs := scribble_bytes tb (d_chars d)) in *.
assert (Hbs : reader_ok 9 a 0 0 0 bs 0) by exact (reader_ok_12 tb a (d_chars d) Ha ltac:(lia) (r12_garr8_bytes _ _ _ _ Htb)).
pose proof Hbs as (_ & _ & _ & _ & Hlbs & _).
assert (Hkat3 : k_at g pos (kz_set_kb (rdk 12 pv dv a 0 0 0 (repeat 0 24)) 12 bs) W3 mem3).
{ apply (r12_kat_kb g pos _ W2 W3 (ms_mem ms) mem3 12 bs Hkatc).
  - intros x Hx1 Hx2. apply KF; [lia | cbv beta; lia].
  - lia.
  - exact Hlbs.
  - apply (cw_val_mem_kept (w_H W2) (w_H W3) (ms_mem ms) mem3); [|exact V0c].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KF; [lia | cbv beta; lia].
  - replace (FA g pos + 192 + 40) with (FA g pos + 232) by lia. exact HR3. }
assert (Hops3 : ops_at ops regs3).
{ destruct Hopsc as (Ho1 & Ho2). split; [exact Ho1|].
  assert (H20' : getr regs3 20 = getr (ms_regs ms) 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
  rewrite H20'. exact Ho2. }
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3; exact Hfr).
assert (Hmo3 : mo_le MT (e_S g) S3 0) by exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo HMLE3).
clear KF KE HS SHOK HJ HJ0 HAE HEE.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly3 S3 W3 regs3 mem3 md4 k HJ4 Hfr3 HC4) as (EFA3 & _).
(* 0x81620 li a0,9; 0x81624 sw a0,0(s7); 0x81628 j 0x82734 *)
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly3 S3 W3 regs3 mem3 md4 k c [] [] 0x81620 0 4 []
  HJ4 Hfr3 HC4 Hcur4 ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl I) as [HS SHOK].
assert (HAE : env_agree 37 (bm_env g pos c regs3 []) (bm_env g pos c regs3 [])) by apply env_agree_refl.
remember (bm_env g pos c regs3 []) as E2 eqn:HEE.
assert (B2' : bv_unsigned (ew E2 2) = sp1).
{ subst E2. pose proof HC4 as (_ & _ & R2 & _). rewrite (bm_ew_reg g pos c regs3 [] 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (B33' : bv_unsigned (ew E2 33) = FA g pos)
  by (subst E2; rewrite (bm_ew_F g pos c regs3 []); apply unsigned_lit_small; lia).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 0 4 a ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
cw_keep_j0 HJ4 HJ40.
rewrite Gra. unfold inv_enc. replace (enc_pc 9) with 0x82734 by reflexivity.
cwj_run_to ltac:(rdj_awr B2' B33' EFA3) 0x82734.
cw_keep ltac:(rdj_kwr B2' B33').
rewrite ?wvb_collapse in HJ4.
pose proof HC4 as (_ & _ & R2 & _).
(* ENC9 0x82734: the cut inv_enc .. 9 with k = rdk 9 pv dv a 0 0 0 bs *)
lazymatch goal with
| HSx : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H _) ?msf) |- _ =>
  assert (HAf : env_agree 37 (bm_env g pos c regs3 []) Ef) by (rewrite <- HEE; env_agree_chain HAE);
  pose proof (r12_ops g pos c regs3 [] Ef ssf W3 msf ops (env_agree_le 37 35 _ _ ltac:(lia) HAf) HSx eq_refl Hops3)
    as Hopsf;
  pose proof (bm_cur_end g pos c regs3 [] Ef ssf W3 msf sp1 HAf HSx
    ltac:(vm_compute; repeat (first [left; reflexivity | right])) R2 ltac:(lia) ltac:(lia) Hc ltac:(lia) ltac:(lia))
    as Hcurf;
  let Ck := fresh "Ck" in
  rd_chunk HSx 33%nat 192 Ck; rewrite ?ew_ewset_other in Ck by lia; rewrite B33' in Ck;
  pose proof (rd_val_of_chunk Ef _ (FA g pos) 192 4 (SLit 9) Ck) as Vk;
  change (N.to_nat 4) with 4%nat in Vk;
  replace (bv_unsigned (sv_denot Ef (SLit 9))) with 9 in Vk by reflexivity;
  assert (Hkatf : k_at g pos (rdk 9 pv dv a 0 0 0 bs) W3 (ms_mem msf));
  [ change (rdk 9 pv dv a 0 0 0 bs) with (kz_set_kb (kz_set_kb (rdk 12 pv dv a 0 0 0 (repeat 0 24)) 12 bs) 9 bs);
    apply (r12_kat_kb g pos _ W3 W3 mem3 (ms_mem msf) 9 bs Hkat3);
    [ intros x Hx1 Hx2; apply KE; [lia | unfold rd_zone; lia]
    | lia
    | exact Hlbs
    | exact Vk
    | apply (rd_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem msf)); [|replace (FA g pos + 192 + 40) with (FA g pos + 232) by lia; exact HR3];
      intros x Hx; rewrite Hlbs in Hx; change (Z.of_nat 24) with 24 in Hx; apply KE; [lia | unfold rd_zone; lia] ]
  | apply (r12_exit B MT K XM_LIB LAWS g pos sp1 0 4 c [] ly3 S3 W3 regs3 mem3 md4 k Ef ssf msf _ 0x82734 _
      HJ40 Hfr3 Hk Hmo3 HC4 HJ4 (env_agree_le 37 35 _ _ ltac:(lia) HAf) HSx eq_refl eq_refl
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) KE);
    cbv beta; split; [exact Hopsf|]; split; [lia|];
    exists c, (rdk 9 pv dv a 0 0 0 bs), (Some d);
    split; [exact Hcurf|]; split; [exact Hkatf|];
    split; [apply rd_enc_ok; [lia | exact Hpd | exact Hbs] | reflexivity] ]
end.
Qed.
End d.
End c.
