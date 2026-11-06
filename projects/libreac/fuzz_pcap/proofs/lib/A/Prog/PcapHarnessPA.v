(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap's program walk, written in the form of
   lib/A/Prog/PcapHarnessTail.v (the same lane's tail walks) and of cgif_file_fuzzer's per-function walks. *)

(* Phase A of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput, 0x807c8, ASan build of libreac v1.9.0):
   PcapEntryPhases.GI_K1 (0x80944) to GI_K2 (0x809a0), in PcapEntryDefs.pe_from's shape
   `pe_from SK B MT KS POST GI_K2 -> pe_from SK B MT KS POST GI_K1`, which is PcapEntryTop.v's Section hypothesis
   pe_A. Every number is read from the original v1.9.0 pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...;
   symbols from fuzz_pcap.asan (sha256 36da3052c383), capstone disassembly); the comment beside a number names
   its instruction.

   The code of the phase (0x80944 .. 0x809a0):
     0x80944 mv s3,a0          the copy b that malloc returned (a0), kept in s3
     0x80948 beqz s6,+8        |F| = 0 skips the NULL test (malloc(0) may return anything)
     0x8094c beqz s3,0x81340   the harness's `if (!file) abort()`: closed by 4096 <= b (GI_K1)
     0x80950 addi a0,s7,0x20   &ps = F + 32
     0x80954 sd a0,0x58(s1)    the PS_PSP spill
     0x80958 beqz s6,+0x18     |F| = 0 skips the copy
     0x8095c mv a0,s3 / mv a1,s5 / mv a2,s6
     0x80968 jal __asan_memcpy (0x51514)       memcpy(b, src, |F|)
     0x8096c ld a0,0x58(s1)    &ps again (the branch lands here too, with a0 = &ps from 0x80950)
     0x80970 sd s3,0(s2)       g_file := b         (a pe_G byte)
     0x80974 sb zero,4(s9) / 5(s9) / 6(s9)         ps comes into scope: PSH_entry -> PSH_ps
     0x80980 addi a1,zero,0xa5 / addi a2,zero,0x18 / mv s2,a0
     0x8098c jal __asan_memset (0x519b0)       memset(&ps,0xa5,24)
     0x80990 auipc a0,0xfffa0 / addi a1,a0,0x370   the path literal (object 3)
     0x80998 mv a0,s2
     0x8099c jal pcap_source_open                   -> PP_K2 0x809a0

   The Section hypotheses, each of the exact type of the fact it stands for, discharged by the composer
   (PcapEntryTop.v's Section top):
     LAWS, TL, MLAWS, ASIL, HRO   the kit's own (as in PcapHarnessTail.v);
     HCPY, HSET                   aintrin_realizes SEGS B OCpy / OSet at the two trampolines, from AsanAPI's
                                  aa_asan_memcpy / aa_asan_memset (Reusable/YG0d.v:538-539);
     (the writability of a byte of pe_G, that no byte of pe_G is a stream environment cell, and the separation of
      g_file_len below g_file are not Section hypotheses: pe_base carries them since a working branch 4b5f67b5a60, a Theorem Labs lane)
     OPENS, FM_RA, CTX, ROI, HROI, HPATH, HCTX, HFMU, HGLEN   pcap_source_open's statement and its side
                                  conditions, with the tail lane's names; HCTX is at PP_K2, this call's landing. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00 YG0h.
(* The phase data first: PcapEntry pulls in modules whose short names (YI16, YK11, ...) also exist under lib/U, so
   the lib/Reusable imports below must come after it for those short names to mean lib/Reusable's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YImgTop YE00 YE01 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 YC85G YC88 PcapFrame PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapFuzzFopenDefs
  PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs
  PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapHarnessA PcapHarnessTail.
Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is EXPLICIT on every lemma of this file (a Theorem Labs lane, 21:57Z): the only global sink_head instance in this
   closure is the plain build's, so it must never be inferred. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Variable POST : ecx -> world SEGS -> config -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MLAWS : ameter_laws MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Context {HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* The two ASan intrinsics the phase calls (0x80968, 0x8098c), at the trampolines PcapAddr names. *)
Hypothesis HCPY : aintrin_realizes SEGS B OCpy (pa_sigma PS___asan_memcpy).
Hypothesis HSET : aintrin_realizes SEGS B OSet (pa_sigma PS___asan_memset).
(* pcap_source_open's statement and its side conditions, with a Theorem Labs lane's names. *)
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis OPENS : tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4))
  (pa_val (A_OBJ 2)) ROI B KS MT FM_RA CTX (BASE + AF_pcap_source_open).
Hypothesis HROI : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (pa_val (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (pa_val (A_OBJ 3)) 13.
Hypothesis HCTX : In [BASE + PP_K2; RA_LLVMF] CTX /\ In [BASE + PP_K2] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).
Hypothesis HGLEN : pa_val (A_HI 8) + PE_GLEN_LO = pa_val (A_OBJ 4).
Let RUN := paj_run (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).

(* The symbolic state at PP_K1: the PS_PSP slot the phase writes and reads back (s1 + 88), the g_file word the
   store 0x80970 writes (s2 = &g_file), and the three shadow bytes of ps (s9 + 4 .. s9 + 7). *)
Definition pa_rs : smem :=
  [ YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
    YP09.mkRegion (Some 18%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 25%nat) 4 7 4 7 [] ].
(* One atom fact per region base, so the engine can place each region statically: s1 the realigned stack pointer
   (32-aligned), s2 = &g_file (an image byte), s9 the frame's shadow (8-aligned, inside the shadow band), and the
   copy b, whose 4096 <= b closes the NULL test 0x8094c `beqz s3` after 0x80944 `mv s3,a0`. *)
Definition pa_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 4);
           (18%nat, mkAF 65536 pcap_img_end 0); (25%nat, mkAF (2147450880 + 512) (2147450880 + 2 ^ 44) 3)] [] [].
(* The symbolic state at 0x8096c, back from __asan_memcpy: the PS_PSP slot as the run at 0x80954 left it (&ps =
   s7 + 32, read back at 0x8096c; no write), g_file and the three shadow bytes of ps, as in pa_rs. *)
Definition pa_rs2 : smem :=
  [ YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 23 32))];
    YP09.mkRegion (Some 18%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 25%nat) 4 7 4 7 [] ].

(* The three regions the phase writes, as bytes the journal lets it write: the spill slot is stack, g_file is a
   byte of pe_G (the journal's program-global ranges), the shadow bytes are the call's own frame's. *)
Ltac pa_awr HU9 HU18 HU25 HEfa :=
  try unfold pa_rs; try unfold pa_rs2; cbn [ss_mem add_cond];
  apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite HU9 in Ha;
      left; split; [left; unfold LLVMF_STK; lia | lia]
    | apply awr_ok_x_cons_g;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite HU18 in Ha;
          apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia
        | apply awr_ok_x_cons;
            [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite HU25 in Ha;
              left; split; [apply (awr_ownframe _ _ _ _ _ _ _ _ a HEfa); right; lia | lia]
            | apply awr_ok_x_nil ] ] ].

(* PcapHarnessA's dlia1 / zuf are Section-local there, so this file carries its own copy: lia over ONE folded
   separation fact, so that the other calls do not case-split on all of them. *)
Ltac pa_zuf H := unfold zdisjoint, in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H; cbn [fst snd] in H.
Ltac pa_dlia1 H := let X := fresh "X" in pose proof H as X; pa_zuf X; lia.
Ltac pa_dlia2 H1 H2 := let X := fresh "X" in pose proof H1 as X; pa_zuf X; pa_dlia1 H2.

Theorem pe_A : pe_from SK B MT KS POST (GI_K2 B MT KS) -> pe_from SK B MT KS POST (GI_K1 B MT KS).
Proof.
intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hb4096 &
  R10 & R18 & R20 & R21 & R22 & R23 & R25 & SD & SGLEN & SF0 & Hglob & Hsrcnone).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
destruct Hregs as (Rsp & Rs0 & Rs1 & Rs11 & Rgp & Rtp).
pose proof (tail_geo B MT KS cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ &
  _ & _ & _ & Hmok & Hneed & HGX & HGD & HGDISJ & _).
(* what pe_base's per-byte pe_G clause gives the global store 0x80970 (a working branch 4b5f67b5a60) *)
assert (HGW : forall (W : world SEGS) (mem : word -> option byte) a, inG pe_G a -> writable_at SEGS (rdW W mem) a)
  by (intros W mem a Ha; exact (proj2 (proj2 (proj2 (proj2 (proj2 (HGD a Ha))))) _)).
assert (HGENV : forall a, inG pe_G a -> ~ asrc_env_addr KS a)
  by (intros a Ha; exact (proj1 (proj2 (proj2 (proj2 (proj2 (HGD a Ha))))))).
(* the inner donor journal of the harness's gx journal *)
pose proof HJ as HJgx.
edestruct gx_open as (memS & HJi & Hag); [exact HJ|]. clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk0 & _ & _ & _ & _ & _ & HJpres & _).
destruct (lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (_ & _ & HFpres & HFSpres).
rewrite Efa in HFpres, HFSpres. change (fs_frame_bytes PE_CID) with 128 in HFpres.
change (fs_frame_bytes PE_CID / 8) with 16 in HFSpres.
(* the copy b, the block the phase fills *)
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb (p_nF cx) HAR Hbin) as (Hb16 & Hb4096' & Hbceil & Hbapp & Hbpres & _ & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrqb1 Hrqb2].
(* the shadow of the frame, as the aligned shadow of its base *)
assert (ESH : pSH cx fp = SHADOW_OFF + pF cx fp / 8) by (unfold pSH, shadow_of_addr; reflexivity).
assert (HSHr : 2147450880 + 512 <= pSH cx fp /\ pSH cx fp + 16 <= 2147450880 + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
{ destruct (h_div8_of_mul64 (pF cx fp) Hfa64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF.
  pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
  replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
    by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
  split; [lia|]. split; [lia|].
  rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
  apply Z_mod_mult. }
(* the harness's globals: image bytes, so their addresses are the listing's objects 2 and 4 *)
pose proof (pa_obj_img 2 ltac:(lia)) as O2. pose proof (pa_obj_img 4 ltac:(lia)) as O4.
unfold pcap_img_end, IMG_TOP in O2, O4.
(* the symbolic state at 0x80944 *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E27 : ew E 27 = getr (ms_regs ms3) 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 27 27%bv eq_refl)).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 10 10%bv eq_refl)).
assert (E18 : ew E 18 = getr (ms_regs ms3) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
assert (E25 : ew E 25 = getr (ms_regs ms3) 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = bb) by (rewrite E10, R10; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = pa_val (A_OBJ 2)) by (rewrite E18, R18; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp) by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS PP_K1 sr_atoms pa_rs None pa_facts) (restrict (w_H W3) ms3)).
{ rewrite HEdef. rewrite HEdef in U9, U10, U18, U25.
  apply entryR; try assumption; [vm_compute; reflexivity | | |].
  - unfold pa_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LLVMF_STK. lia.
    + rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply HGW. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    + rewrite U25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      replace (pSH cx fp + o) with (shadow_addr (pF cx fp) + o) by (rewrite ESH; unfold shadow_addr; lia).
      apply HFSpres. lia.
  - apply pairwise_disjoint_of_extents. unfold pa_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold pa_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2 fst snd]. unfold pcap_img_end, IMG_TOP.
    rewrite U9, U10, U18, U25. repeat match goal with |- _ /\ _ => split end;
      first [ lia | (change (2 ^ 5) with 32; exact Hs1m) | (change (2 ^ 4) with 16; exact Hb16)
            | (change (2 ^ 3) with 8; exact (proj2 (proj2 HSHr)))
            | (change (2 ^ 0) with 1; apply Z.mod_1_r) | exact I ]. }
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SLit SB) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose (RUNX := paj_run_x B LAWS pe_G HGX 0 []).
(* 0x80944 mv s3,a0; 0x80948 beqz s6: the branch on |F| *)
paj_run_tok RUNX HS HJgx SHOK (0, 0);
  [ pa_awr U9 U18 U25 Efa |].
(* 0x80948 beqz s6: an empty file skips the NULL test and the copy *)
psrr_branch_tok RUNX BR HS SHOK (0, 0).
{ (* |F| = 0: 0x80950 &ps; 0x80954 the PS_PSP spill; 0x80958 skips the copy; 0x80970 g_file := b;
     0x80974..0x8097c ps comes into scope; 0x8098c jal __asan_memset *)
  (* the branch was taken: s6 = |F| = 0 *)
  assert (HnF0 : p_nF cx = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom E 22 (p_nF cx)) in Hc by (first [rewrite E22, R22; reflexivity | lia]).
    rewrite U_lit in Hc by lia. exact Hc. }
  clear Hc. paj_run_tok RUNX HS HJgx SHOK (0, 0); [ pa_awr U9 U18 U25 Efa |].
  (* 0x8098c jal __asan_memset: a0 = ps = F + 32, a1 = 0xa5, a2 = 24 *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
  prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  (* the three shadow bytes of ps, as the run has just written them (0x80974, 0x80978, 0x8097c) *)
  assert (SHz : forall i : nat, (4 <= i <= 6)%nat ->
    aview SEGS (w_H W3) (ms_mem ms0) (pSH cx fp + Z.of_nat i) = Some 0).
  { intros i Hi. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms0)); [|lia].
    refine (h_field E _ (restrict (w_H W3) ms0) 2 25 4 7 4 7 _ (pSH cx fp) (Z.of_nat i) 1
      (SLit 0) 0 HS eq_refl U25 _ eq_refl _ _).
    - assert (Hc : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia.
      destruct Hc as [Hc1 | [Hc1 | Hc1]]; subst i; cbn; tauto.
    - cbn. lia.
    - cbn. lia. }
  edestruct gx_open as (memS1 & HJ1 & Hag1); [exact HJgx|].
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (pa_sigma PS___asan_memset) HSET
      W3 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) memS1 (c_md cx) [(PE_CID, fp)] ly3 S3 _ k
      (pF cx fp + 32) 165 24 (c_sp1 cx - spZ (c_regs cx)) _ HJ1).
    - rewrite Q10, E23, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite Q11. reflexivity.
    - rewrite Q12. reflexivity.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact (o_mod16 B MT KS cx HB).
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite Q3, E3, Rgp. exact Hgp0.
    - rewrite Q4, E4, Rtp. exact Htp0.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [apply (awr_ownframe _ _ _ _ _ _ _ _ a Efa); left; lia | unfold ESTACK; lia].
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. pa_dlia1 Hfapp.
    - (* the shadow of ps: the three bytes the run has just zeroed (0x80974..0x8097c) *)
      apply (h_ra_frame (w_H W3) (ms_mem ms0) (pF cx fp) (pSH cx fp) 32 24 ESH Hfa64);
        [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      apply SHz. lia.
    - (* its hull: SH is 8-aligned, so the hull of [F + 32, F + 56) is [SH, SH + 8), inside the frame's shadow *)
      intros _ s Hs. unfold shadow_addr in Hs.
      assert (Hs' : 0 <= s - pSH cx fp < 16)
        by (destruct HSHr as (_ & _ & Hm8); rewrite ESH; unfold SHADOW_OFF in *;
            Z.div_mod_to_equations; lia).
      apply (aview_keeps_vis SEGS (w_H W3) (ms_mem ms3) (ms_mem ms0) s
        (mem_grows_trans _ _ _ HG HG0)).
      apply aview_some_of_apresent.
      replace s with (shadow_addr (pF cx fp) + (s - pSH cx fp))
        by (rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia).
      exact (proj1 (HFSpres (s - pSH cx fp) ltac:(lia))).
    - exact I. }
  (* back from __asan_memset at 0x80990, with ps filled with 0xa5 *)
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hret2 & Hset & Hkeep & Hpres2 & Hsame).
  assert (HJgx2 : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem2 md2 k)
    by (eapply gx_pack0; [exact HJ2 | exact Hag1]).
  (* 0x80990 auipc / 0x80994 addi: the path literal; 0x80998 mv a0,s2; 0x8099c jal pcap_source_open *)
  pose proof (entry0 600 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) W3
    ltac:(cbn [ms_pc_val mkst]; rewrite Q1; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl) as HS2.
  cbn [ms_regs ms_mem mkst] in HS2.
  remember (Eimg (Ereg regs2 [])) as Ex eqn:HEx in HS2.
  assert (HEI2 : img_env VAL A_LIM Ex) by (subst Ex; apply Eimg_env).
  assert (ELx : forall n, (n < A_TEXT)%nat -> ew Ex n = ew (Ereg regs2 []) n)
    by (intros n Hn; subst Ex; apply Eimg_low; exact Hn).
  assert (EO3 : ew Ex 244%nat = Z_to_bv 64 (pa_val (A_OBJ 3)))
    by (subst Ex; apply (Eimg_img _ 244%nat); unfold A_TEXT, A_LIM; lia).
  assert (SHOK2 : sh_ok SEGS (SLit SB) [] Ex (mrestrict (w_H W3) mem2)) by constructor.
  paj_run_tok RUNX HS2 HJgx2 SHOK2 (0, 0); [ apply awr_ok_x_nil |].
  (* at the call of pcap_source_open, 0x8099c: the run wrote nothing *)
  assert (HFm2 : ms_mem ms1 = mem2) by exact (frame_of_nil _ _ _ HF1).
  pmkst HS2.
  prreg HS2 (1%bv : bv 5) P1. prreg HS2 (2%bv : bv 5) P2. prreg HS2 (3%bv : bv 5) P3. prreg HS2 (4%bv : bv 5) P4.
  prreg HS2 (8%bv : bv 5) P8. prreg HS2 (10%bv : bv 5) P10. prreg HS2 (11%bv : bv 5) P11.
  prreg HS2 (9%bv : bv 5) P9. prreg HS2 (27%bv : bv 5) P27.
  prreg HS2 (19%bv : bv 5) P19. prreg HS2 (20%bv : bv 5) P20.
  prreg HS2 (23%bv : bv 5) P23. prreg HS2 (25%bv : bv 5) P25.
  (* the registers at the call, as values *)
  assert (PP : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r))
    by exact HP2.
  assert (XR : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew Ex n = getr regs2 r)
    by (intros n r Hn Hr; rewrite ELx by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  assert (Y2 : getr (ms_regs ms1) 2 = w64 (c_sp1 cx)).
  { rewrite P2, (XR 2%nat 2%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 2); [exact (PP 2 ltac:(unfold acallee_saved; lia)) | rewrite Q2, E2; exact Rsp]. }
  assert (Y3 : getr (ms_regs ms1) 3 = getr (c_regs cx) 3).
  { rewrite P3, (XR 3%nat 3%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 3); [exact (PP 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3, E3; exact Rgp]. }
  assert (Y4 : getr (ms_regs ms1) 4 = getr (c_regs cx) 4).
  { rewrite P4, (XR 4%nat 4%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 4); [exact (PP 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4, E4; exact Rtp]. }
  assert (Y8 : getr (ms_regs ms1) 8 = w64 (spZ (c_regs cx))).
  { rewrite P8, (XR 8%nat 8%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 8); [exact (PP 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8, E8; exact Rs0]. }
  assert (Y10 : getr (ms_regs ms1) 10 = w64 (pF cx fp + 32)).
  { rewrite P10, (XR 18%nat 18%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 18); [exact (PP 18 ltac:(unfold acallee_saved; lia)) |].
    rewrite Q18, E23, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Y11 : getr (ms_regs ms1) 11 = Z_to_bv 64 (pa_val (A_OBJ 3))) by (rewrite P11; exact EO3).
  assert (Hsp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Y2; unfold w64; apply unsigned_lit_small; lia).
  (* what the phase wrote: the two runs wrote the PS_PSP slot, g_file and three shadow bytes; __asan_memset wrote ps
     and its own scratch window below sp; the last run wrote nothing. Every other byte is as at PP_K1. *)
  pose (PW := fun a => (c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/
                      (pSH cx fp + 4 <= a < pSH cx fp + 7)).
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ PW a ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms) PW HFr).
    intros bw wlo whi a Hwn Ha. vm_compute in Hwn.
    repeat (destruct Hwn as [Hq | Hwn];
      [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U9, ?U18, ?U25 in Ha; cbv [PW]; lia |]).
    destruct Hwn. }
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ PW a ->
    aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms) (ms_mem ms0) PW HFr0).
    intros bw wlo whi a Hwn Ha. vm_compute in Hwn.
    repeat (destruct Hwn as [Hq | Hwn];
      [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U9, ?U18, ?U25 in Ha; cbv [PW]; lia |]).
    destruct Hwn. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/
       (pSH cx fp + 4 <= a < pSH cx fp + 7)) ->
    ~ (pF cx fp + 32 <= a < pF cx fp + 56) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2 H3. rewrite HFm2, (Hkeep a Ha ltac:(lia) ltac:(unfold ESTACK; lia)).
    rewrite (KR2 a Ha H1). exact (KR1 a Ha H1). }
  (* 0x8099c jal pcap_source_open(&ps, "<fuzz-input>") *)
  rewrite pa_sigma_pcap_source_open.
  edestruct gx_open as (memS3 & HJ3 & Hag3); [exact HJgx2|].
  pose proof HJ3 as (HAR1 & _).
  (* the facts the call reads, at the call memory *)
  pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as HFo.
  rewrite Efa in HFo. change (fs_frame_bytes PE_CID) with 128 in HFo.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo.
  assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1))); [exact (proj1 Hsaved)|].
    intros i Hi. apply KALL; unfold PW; pa_dlia1 HSHr. }
  assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (proj2 Hsaved 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1))); [exact H0|].
    intros i Hi. apply KALL; unfold PW; pa_dlia1 HSHr. }
  assert (HARO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms1)))
    by (eapply aro_now; eassumption).
  assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  assert (EBB : blocks_bytes S3 = blocks_bytes (c_S cx) + p_nF cx).
  { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
    rewrite (bsum_perm _ _ Hperm), bsum_app. cbn [bsum fold_right snd]. lia. }
  (* g_file as the run stored it at 0x80970 (region 1, s2 + 0), at the memset's entry memory *)
  assert (GF0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pa_val (A_OBJ 2) + 0) 8 bb).
  { refine (h_field E _ (restrict (w_H W3) ms0) 1 18 0 8 0 8 _ (pa_val (A_OBJ 2)) 0 8 (SOff 10 0) bb
      HS eq_refl U18 _ _ _ _).
    - cbn. tauto.
    - rewrite h_denot_off0, E10, R10. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  rewrite Z.add_0_r in GF0.
  eapply SRr_bind.
  { eapply (OPENS LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS3 (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms1) _ k (ms_regs ms1) (pch cx) (pPS cx fp) (p_nF cx) bb (c_M cx)
      (p_C cx) PE_CID fp HJ3).
    - exact HARO.
    - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite P1, unsigned_lit_small by lia. lia.
    - rewrite Y3. exact Hgp0.
    - rewrite Y4. exact Htp0.
    - rewrite Y10. reflexivity.
    - rewrite Y11. reflexivity.
    - rewrite Hsp. unfold s0Z at 1. rewrite Y8. unfold w64. rewrite unsigned_lit_small by lia.
      eapply pch_achain; [exact HB | exact HJ3 | exact Hag3 | exact Hs8 | exact Hs16].
    - unfold raZ. rewrite P1, unsigned_lit_small by lia.
      unfold pch, spine. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
      + cbn [map]. rewrite HraL. exact (proj1 HCTX).
      + cbn [map]. exact (proj2 HCTX).
    - rewrite Hsp. pose proof Hs1m as Hm. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq].
      apply Z.mod_divide; [lia|]. exists (2 * q). lia.
    - rewrite Hsp, TPCAP_SOURCE_OPEN_STK_val. unfold LLVMF_STK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, Etop. lia.
    - rewrite Hfrs. cbn [length Z.of_nat]. lia.
    - left. reflexivity.
    - rewrite Efa. unfold pPS, PO_PS. lia.
    - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS. exact (h_mod64_add (pF cx fp) 32 Hfa64 eq_refl).
    - unfold pPS, PO_PS.
      apply (h_ra_frame (w_H W3) (ms_mem ms1) (pF cx fp) (pSH cx fp) 32 24 ESH Hfa64); [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      rewrite HFm2, (Hkeep (pSH cx fp + 4 + j) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(unfold ESTACK; lia)).
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      apply SHz. lia.
    - exists sink_token. split; [left; reflexivity|]. unfold sink_token. cbn [fst snd]. lia.
    - apply HROI. exact HARO.
    - exact (proj1 (HPATH ly3 S3 W3 (ms_mem ms1) _ HAR1)).
    - exact (proj2 (HPATH ly3 S3 W3 (ms_mem ms1) _ HAR1)).
    - eapply (val_mem_frame SEGS); [|exact (proj2 Hglob)]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply KALL; [lia | lia | lia | lia].
    - eapply (val_mem_frame SEGS); [|exact GF0]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). rewrite HFm2. apply Hkeep; [lia | lia | unfold ESTACK; lia].
    - lia.
    - apply (OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceCloseSpec.asource_none_frame_segs
        SEGS KS (rdW W3 (ms_mem ms3))); [|exact Hsrcnone].
      intros a Ha. apply (mbyte_of_aview SEGS).
      destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He).
      pose proof (pa_img_range a Hi) as Hr1. unfold pcap_img_end, IMG_TOP in Hr1.
      apply KALL; [lia | | lia | lia].
      unfold PW. intros [Hp | [Hp | Hp]]; [lia | | lia].
      apply (HGENV a); [| exact Ha]. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    - symmetry. exact ELC.
    - lia.
    - intros H1. exfalso. lia.
    - eapply meta_now; eassumption.
    - unfold EV_OPEN, EV_FUZZ_FOPEN, EV_LIB in *. lia.
    - rewrite EBB. unfold SRC_FILE_BLOCK, LIVE_LIB in *. lia.
    - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT SRC_FILE_BLOCK) MLAWS Hmok Hmo
        (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia))).
      pose proof (PA_K12_need MT MLAWS cx) as Hn. pose proof (mo_free_nonneg MT MLAWS).
      pose proof (mo_malloc_nonneg MT MLAWS (p_bn cx) ltac:(lia)).
      pose proof (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)).
      unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in *. lia.
    - exact (proj1 HFMU).
    - exact (proj2 HFMU). }
  (* back from pcap_source_open at PP_K2 0x809a0 *)
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HP4 & Hfr4 & Hfd4 & Hfs4 & HK4 & Hmle4 &
    Hz12 & Hz16 & Hz20 & Harm).
  rewrite P1.
  destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 bb (p_nF cx) HAR Hbin) as HBo.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HBo.
  (* the body bytes outside the slots and the shadow, from PP_K1 to the call and then across the call *)
  assert (Hns1 : forall a, hfoot_ns cx fp a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. destruct (Z.eq_dec (c_n cx) 0) as [Hz|Hz].
    - unfold hfoot_ns in Ha. apply KALL; [lia | pa_dlia1 Hfapp | lia | lia].
    - pose proof (input_block B MT KS cx ly3 S3 _ HB Hperm ltac:(lia)) as Hpin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR Hpin) as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as Hrq.
      pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hpin) as HPo.
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HPo.
      destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hsep & _).
      assert (Hdisj : zdisjoint (c_p cx, req_size (c_n cx)) (pF cx fp, 128)).
      { apply (pairwise_In zdisjoint _ _ _ _ _ eq_refl Hsep).
        - apply in_map_iff. exists (c_p cx, c_n cx). split; [cbn [fst snd]; reflexivity | exact Hpin].
        - apply in_map_iff. exists (PE_CID, fp).
          split; [cbn [fst snd]; rewrite Efa; change (fs_frame_bytes PE_CID) with 128; reflexivity | exact Hfin]. }
      unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
      unfold hfoot_ns in Ha. apply KALL; [lia | pa_dlia2 Hfapp Hpapp | lia | lia]. }
  destruct (tail_kept_ns cx fp W3 ms3 W3 ms1 Hns1 Hsaved Hhdr Hin) as (Hsaved1 & Hhdr1 & Hin1).
  assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha.
    refine (foot_kept B MT KS cx fp ly3 S3 W3 (ms_mem ms1) W4 mem4 _ _
      (fun a => pPS cx fp <= a < pPS cx fp + 22) HB
      (fun a Ha1 Ha2 _ => K1 a Ha1 Ha2) K2 K4 _ Hfin Efa (input_block B MT KS cx ly3 S3 _ HB Hperm) _ a Ha);
      [rewrite Hsp; lia|].
    intros x Hx Hw.
    exact (frame_off_hfoot B MT KS LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 22 HB HAR Hperm Hfin Efa
      ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS; lia) x Hx Hw). }
  destruct (tail_kept_ns cx fp W3 ms1 W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS))
    ltac:(intros a Ha; cbn [ms_mem mkst]; apply Hfoot; unfold hfoot, hfoot_ns in *; tauto)
    Hsaved1 Hhdr1 Hin1) as (T1 & T2 & T3).
  assert (PK : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r))
    by exact HP4.
  (* the frame's shadow at PP_K2 is PSH_entry with ps in scope, which is PSH_ps *)
  assert (Hnth : forall j, (j < 16)%nat -> (j < 4 \/ 7 <= j)%nat -> nth j PSH_ps 0 = nth j PSH_entry 0).
  { intros j Hj Hj2.
    do 16 (destruct j as [|j]; [solve [vm_compute; reflexivity | exfalso; lia] |]).
    exfalso. lia. }
  assert (TSH : pshadow cx fp W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) PSH_ps).
  { intros i Hi. cbn [ms_mem mkst]. vm_compute in Hi.
    rewrite Hfoot by (unfold hfoot; right; right; right; left; lia).
    destruct (Nat.ltb_spec i 4) as [H4|H4]; [|destruct (Nat.leb_spec 7 i) as [H7|H7]].
    - rewrite (KALL (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(lia)).
      rewrite (Hsh i ltac:(vm_compute; lia)), (Hnth i ltac:(lia) ltac:(lia)). reflexivity.
    - rewrite (KALL (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(lia)).
      rewrite (Hsh i ltac:(vm_compute; lia)), (Hnth i ltac:(lia) ltac:(lia)). reflexivity.
    - rewrite HFm2, (Hkeep (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(pa_dlia1 Hfapp)
        ltac:(unfold ESTACK; lia)).
      rewrite (SHz i ltac:(lia)).
      assert (Hq : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia.
      destruct Hq as [Hq|[Hq|Hq]]; subst i; vm_compute; reflexivity. }
  (* the registers of the body at PP_K2, from the call's callee-saved post *)
  assert (PRG : pregs cx (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS))).
  { unfold pregs. cbn [ms_regs mkst].
    split; [transitivity (getr (ms_regs ms1) 2); [exact (PK 2 ltac:(unfold acallee_saved; lia)) | exact Y2]|].
    split; [transitivity (getr (ms_regs ms1) 8); [exact (PK 8 ltac:(unfold acallee_saved; lia)) | exact Y8]|].
    split; [transitivity (getr (ms_regs ms1) 9); [exact (PK 9 ltac:(unfold acallee_saved; lia)) |
              rewrite P9, (XR 9%nat 9%bv) by first [unfold A_TEXT; lia | reflexivity];
              transitivity (getr (ms_regs ms0) 9); [exact (PP 9 ltac:(unfold acallee_saved; lia)) |
                rewrite Q9, E9; exact Rs1]]|].
    split; [transitivity (getr (ms_regs ms1) 27); [exact (PK 27 ltac:(unfold acallee_saved; lia)) |
              rewrite P27, (XR 27%nat 27%bv) by first [unfold A_TEXT; lia | reflexivity];
              transitivity (getr (ms_regs ms0) 27); [exact (PP 27 ltac:(unfold acallee_saved; lia)) |
                rewrite Q27, E27; exact Rs11]]|].
    split; [transitivity (getr (ms_regs ms1) 3); [exact (PK 3 ltac:(unfold acallee_saved; lia)) | exact Y3]|].
    transitivity (getr (ms_regs ms1) 4); [exact (PK 4 ltac:(unfold acallee_saved; lia)) | exact Y4]. }
  (* the cut's callee-saved registers, through both calls *)
  assert (RK19 : getr regs4 19 = w64 bb).
  { transitivity (getr (ms_regs ms1) 19); [exact (PK 19 ltac:(unfold acallee_saved; lia))|].
    rewrite P19, (XR 19%nat 19%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 19); [exact (PP 19 ltac:(unfold acallee_saved; lia))|].
    rewrite Q19, E10. exact R10. }
  assert (RK20 : getr regs4 20 = w64 (pF cx fp)).
  { transitivity (getr (ms_regs ms1) 20); [exact (PK 20 ltac:(unfold acallee_saved; lia))|].
    rewrite P20, (XR 20%nat 20%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 20); [exact (PP 20 ltac:(unfold acallee_saved; lia))|].
    rewrite Q20, E20. exact R20. }
  assert (RK23 : getr regs4 23 = w64 (pF cx fp)).
  { transitivity (getr (ms_regs ms1) 23); [exact (PK 23 ltac:(unfold acallee_saved; lia))|].
    rewrite P23, (XR 23%nat 23%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 23); [exact (PP 23 ltac:(unfold acallee_saved; lia))|].
    rewrite Q23, E23. exact R23. }
  assert (RK25 : getr regs4 25 = w64 (pSH cx fp)).
  { transitivity (getr (ms_regs ms1) 25); [exact (PK 25 ltac:(unfold acallee_saved; lia))|].
    rewrite P25, (XR 25%nat 25%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 25); [exact (PP 25 ltac:(unfold acallee_saved; lia))|].
    rewrite Q25, E25. exact R25. }
  assert (EFDS : m_fds md4 = m_fds (c_md cx)).
  { rewrite Hfd4, (proj1 (fs_wvb _ _)), (proj1 (sbm_fds _ _ Hsame)), (proj1 (fs_wvb _ _)). exact Hfds. }
  assert (EFS : m_fs md4 = m_fs (c_md cx)).
  { rewrite Hfs4, (proj2 (fs_wvb _ _)), (proj2 (sbm_fds _ _ Hsame)), (proj2 (fs_wvb _ _)). exact Hfs. }
  (* the spill slots the cut states: two from PP_K1, PS_PSP written by the run at 0x80954 *)
  assert (SD1 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx + PS_D) = Some (p_d cx)).
  { rewrite <- SD. apply rdword_ext. intros i Hi.
    apply KALL; [unfold PS_D; lia | unfold PS_D; lia | unfold PS_D; pa_dlia1 Hfapp | unfold PS_D; lia]. }
  assert (SG1 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx + PS_GLEN) = Some (pa_val (A_HI 8))).
  { rewrite <- SGLEN. apply rdword_ext. intros i Hi.
    apply KALL; [unfold PS_GLEN; lia | unfold PS_GLEN; lia | unfold PS_GLEN; pa_dlia1 Hfapp
                | unfold PS_GLEN; lia]. }
  assert (SP1 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx + PS_PSP) = Some (pPS cx fp)).
  { assert (SP0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (c_sp1 cx + 88) 8 (pF cx fp + 32)).
    { refine (h_field E _ (restrict (w_H W3) ms0) 0 9 88 96 88 96 _ (c_sp1 cx) 88 8 (SOff 23 32)
        (pF cx fp + 32) HS eq_refl U9 _ _ _ _).
      - cbn. tauto.
      - apply (h_denot_off E 23 (pF cx fp) 32); [rewrite E23; exact R23 | lia].
      - cbn. lia.
      - cbn. lia. }
    unfold PS_PSP, pPS, PO_PS.
    rewrite <- (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms0) (c_sp1 cx + 88) (pF cx fp + 32) SP0 ltac:(lia)).
    apply rdword_ext. intros i Hi. rewrite HFm2.
    apply Hkeep; [lia | pa_dlia1 Hfapp | unfold ESTACK; lia]. }
  assert (SLOT : forall off v, 8 <= off /\ off + 8 <= 120 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx + off) = Some v ->
    rdword (aview SEGS (w_H W4) mem4) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hv.
    rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms1)) (aview SEGS (w_H W4) mem4)); [exact Hv|].
    intros i Hi. apply Hfoot. unfold hfoot. lia. }
  (* the harness's globals: image bytes, kept by the call's image clause *)
  assert (GIMG : forall a, inG pe_G a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply K3.
    - exact (proj1 (HGX a Ha)).
    - exact (proj2 (HGX a Ha)).
    - exact (proj1 (proj2 (proj2 (HGD a Ha)))).
    - exact (proj1 (proj2 (proj2 (proj2 (HGD a Ha))))). }
  (* the two globals at the call memory, then across the call *)
  assert (GF1 : val_mem SEGS (rdW W3 (ms_mem ms1)) (pa_val (A_OBJ 2)) 8 bb).
  { eapply (val_mem_frame SEGS); [|exact GF0]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). rewrite HFm2. apply Hkeep; [lia | lia | unfold ESTACK; lia]. }
  assert (GLEN1 : val_mem SEGS (rdW W3 (ms_mem ms1)) (pa_val (A_OBJ 4)) 8 (p_nF cx)).
  { eapply (val_mem_frame SEGS); [|exact (proj2 Hglob)]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). apply KALL; [lia | lia | lia | lia]. }
  assert (GLOB4 : p_glob cx W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) bb).
  { split; cbn [ms_mem mkst].
    - eapply (val_mem_frame SEGS); [|exact GF1]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply GIMG. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. lia.
    - eapply (val_mem_frame SEGS); [|exact GLEN1]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply GIMG. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. lia. }
  (* an empty file: the copy holds no bytes *)
  assert (HC0 : p_C cx = []) by (apply length_zero_iff_nil; lia).
  (* the body at PP_K2 *)
  assert (PB2 : pe_body cx fp PP_K2 W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) PSH_ps).
  { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact PRG|]. split; [exact T1|]. split; [exact T2|]. split; [exact TSH|].
    split; [vm_compute; reflexivity | exact T3]. }
  destruct Harm as [(HJ4 & Ha0 & Hgood & hh & Hh4096 & Hh16 & Hbl4 & Hpsf & Hpsw & Hsrc4 & Hmle2)
                   |(HJ4 & Ha0 & Hbad & Hps0 & Hps812 & Hbl4 & Hsrc4)].
  - (* the file was accepted *)
    eapply (NEXT cx fp (k + EV_FUZZ_FOPEN) (acc + mo_malloc MT SRC_FILE_BLOCK) ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) md4 HB).
    + eapply gx_pack0; [exact HJ4 | exact Hag3].
    + rewrite Hfr4. exact Hfrs.
    + exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle2).
    + unfold GI_K2. exists bb.
      split; [exact PB2|]. split; [exact Hn26|]. split; [exact EFDS|]. split; [exact EFS|].
      split; [exact RK19|]. split; [exact RK20|]. split; [exact RK23|]. split; [exact RK25|].
      split; [exact (SLOT PS_D (p_d cx) ltac:(unfold PS_D; lia) SD1)|].
      split; [exact (SLOT PS_GLEN (pa_val (A_HI 8)) ltac:(unfold PS_GLEN; lia) SG1)|].
      split; [exact (SLOT PS_PSP (pPS cx fp) ltac:(unfold PS_PSP; lia) SP1)|].
      split; [exact GLOB4|].
      split; [unfold p_copy; rewrite HC0; apply garr8_nil|].
      left. split; [rewrite <- goodZ_good; exact Hgood|].
      split; [cbn [ms_regs mkst]; exact Ha0|].
      split; [unfold EV_FUZZ_FOPEN; lia|].
      split; [unfold PA_K2g, PA_K1 in *; lia|].
      exists hh.
      split; [rewrite Hbl4; eapply Permutation_trans;
              [apply (Permutation_app_tail [(hh, SRC_FILE_BLOCK)] Hperm)|];
              rewrite <- app_assoc; cbn [app]; apply Permutation_refl|].
      split; [unfold p_psopen, pval; cbn [ms_mem mkst]; split; [exact Hpsf|];
              rewrite <- swZ_sw; exact Hpsw|].
      split; [|cbn [ms_mem mkst]; exact Hsrc4].
      unfold p_psfresh, pval. cbn [ms_mem mkst].
      split; [exact Hz12|]. split; [exact Hz16|]. split; [exact Hz20|].
      unfold p_pspad. cbn [ms_mem mkst].
      intros j Hj. cbn [length] in Hj.
      assert (Hj2 : (j = 0 \/ j = 1)%nat) by lia.
      assert (HA : aview SEGS (w_H W4) mem4 (pPS cx fp + 22 + Z.of_nat j) = Some (nth j [165; 165] 0)).
      { rewrite (K4 PE_CID fp (pPS cx fp + 22 + Z.of_nat j) Hfin
          ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa;
                change (fs_frame_bytes PE_CID) with 128; unfold pPS, PO_PS; lia)
          ltac:(cbv beta; unfold pPS, PO_PS; lia)).
        rewrite HFm2.
        replace (pPS cx fp + 22 + Z.of_nat j) with (pF cx fp + 32 + (22 + Z.of_nat j))
          by (unfold pPS, PO_PS; lia).
        rewrite (Hset (22 + Z.of_nat j) ltac:(lia)).
        destruct Hj2 as [Hq|Hq]; subst j; cbn [nth]; reflexivity. }
      split; [exact (proj1 (val_mem1_of_aview SEGS (w_H W4) mem4 _ _ HA))
             | destruct Hj2 as [Hq|Hq]; subst j; cbn [nth]; lia].
  - (* the file was refused *)
    rewrite goodZ_good in Hbad.
    eapply (NEXT cx fp (k + EV_OPEN) (acc + OPEN_METER MT) ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) md4 HB).
    + eapply gx_pack0; [exact HJ4 | exact Hag3].
    + rewrite Hfr4. exact Hfrs.
    + exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle4).
    + unfold GI_K2. exists bb.
      split; [exact PB2|]. split; [exact Hn26|]. split; [exact EFDS|]. split; [exact EFS|].
      split; [exact RK19|]. split; [exact RK20|]. split; [exact RK23|]. split; [exact RK25|].
      split; [exact (SLOT PS_D (p_d cx) ltac:(unfold PS_D; lia) SD1)|].
      split; [exact (SLOT PS_GLEN (pa_val (A_HI 8)) ltac:(unfold PS_GLEN; lia) SG1)|].
      split; [exact (SLOT PS_PSP (pPS cx fp) ltac:(unfold PS_PSP; lia) SP1)|].
      split; [exact GLOB4|].
      split; [unfold p_copy; rewrite HC0; apply garr8_nil|].
      right. split; [exact Hbad|].
      split; [cbn [ms_regs mkst]; exact Ha0|].
      split; [unfold EV_OPEN, EV_FUZZ_FOPEN; lia|].
      split; [unfold PA_K2r, PA_K1, OPEN_METER; unfold PA_K1 in Hacc; lia|].
      split; [eapply Permutation_trans; [exact Hbl4 | exact Hperm]|].
      split; [unfold p_psnull, pval; cbn [ms_mem mkst]; exact Hps0|].
      cbn [ms_mem mkst]. exact Hsrc4. }
{ (* 0 < |F|: 0x8094c the NULL test (closed by 4096 <= b); 0x80950; 0x80954; 0x8095c..0x80964 the arguments;
     0x80968 jal __asan_memcpy *)
  (* the branch was not taken: s6 = |F| <> 0 *)
  assert (HnF1 : p_nF cx <> 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
    rewrite (U_atom E 22 (p_nF cx)) in Hc by (first [rewrite E22, R22; reflexivity | lia]).
    rewrite U_lit in Hc by lia. exact Hc. }
  clear Hc. paj_run_tok RUNX HS HJgx SHOK (0, 0); [ pa_awr U9 U18 U25 Efa |].
  (* 0x80968 jal __asan_memcpy: a0 = b, a1 = src = s5, a2 = |F| = s6 *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
  prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  edestruct gx_open as (memS1 & HJ1 & Hag1); [exact HJgx|].
  pose proof HJ1 as (HARc & _).
  (* the input is not empty: its first byte d is followed by F *)
  assert (Hpl : exists d rest, c_pl cx = d :: rest).
  { destruct (c_pl cx) as [|d rest] eqn:Epl; [|eauto].
    exfalso. apply HnF1. unfold p_nF, p_F. rewrite Epl. reflexivity. }
  destruct Hpl as (d0 & rest0 & Epl).
  assert (Esrc : p_src cx = c_p cx + 1) by (unfold p_src; rewrite Epl; reflexivity).
  assert (EnF : p_nF cx = c_n cx - 1) by (unfold p_nF, p_F, c_n; rewrite Epl; cbn [tl length]; lia).
  pose proof (input_block B MT KS cx ly3 S3 _ HB Hperm ltac:(lia)) as Hpin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HARc Hpin)
    as (_ & Hp4096 & Hpceil & Hpapp & Hppres & Hbsep & _).
  pose proof (req_size_bounds (c_n cx) ltac:(lia)) as (Hrq0 & Hrq1 & Hrq2).
  pose proof (req_size_bounds (p_nF cx) ltac:(lia)) as (Hrb0 & Hrb1 & Hrb2).
  (* the copy b is this walk's block, not the caller's *)
  assert (HND : List.NoDup (ablocks B ly3 S3)) by (eapply h_ablocks_nodup; eassumption).
  assert (HNI : ~ In (bb, p_nF cx) (ablocks B (c_ly cx) (c_S cx)))
    by exact (h_nodup_app_disj _ _ _ _ (Permutation_NoDup Hperm HND) (or_introl eq_refl)).
  assert (Hsd : zdisjoint (bb, req_size (p_nF cx)) (c_p cx, req_size (c_n cx))).
  { destruct (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0h.pairwise_zdisjoint_In _ _ _ Hbsep
      ltac:(apply in_map_iff; exists (bb, p_nF cx); split; [reflexivity | exact Hbin])
      ltac:(apply in_map_iff; exists (c_p cx, c_n cx); split; [reflexivity | exact Hpin])) as [Heq | Hd];
      [injection Heq as Eq1 Eq2; lia | exact Hd]. }
  unfold zdisjoint in Hsd. cbn [fst snd] in Hsd.
  assert (Hsp0 : spZ (ms_regs ms0) = c_sp1 cx)
    by (unfold spZ; rewrite Q2, E2, Rsp; unfold w64; apply unsigned_lit_small; lia).
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (pa_sigma PS___asan_memcpy) HCPY
      W3 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) memS1 (c_md cx) [(PE_CID, fp)] ly3 S3 _ k
      bb (p_src cx) (p_nF cx) (c_sp1 cx - spZ (c_regs cx)) _ HJ1).
    - rewrite Q10, E10. exact R10.
    - rewrite Q11, E21. exact R21.
    - rewrite Q12, E22. exact R22.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Q2, E2, Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact (o_mod16 B MT KS cx HB).
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite Q3, E3, Rgp. exact Hgp0.
    - rewrite Q4, E4, Rtp. exact Htp0.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [|unfold ESTACK; lia].
      right. right. left. exists bb, (p_nF cx). split; [exact Hbin|]. split; [exact HNI | lia].
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. pa_dlia1 Hbapp.
    - eapply (range_addressable_of_block SEGS B LAWS); [exact HARc | exact Hbin | lia | lia].
    - intros Hn0. eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HARc | exact Hbin | lia | lia | exact Hn0].
    - rewrite Esrc, EnF.
      split; [lia|]. split; [lia|].
      split; [intros a Ha; split;
              [apply aview_some_of_apresent; exact (proj1 (Hppres a ltac:(lia)))
              | rewrite Hsp0; unfold ESTACK; pa_dlia1 Hpapp]|].
      split; [rewrite <- Esrc, <- EnF; lia|].
      split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; pa_dlia1 Hpapp|].
      split; [eapply (range_addressable_of_block SEGS B LAWS); [exact HARc | exact Hpin | lia | lia]|].
      intros Hn0. eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HARc | exact Hpin | lia | lia | exact Hn0]. }
  (* back from __asan_memcpy at 0x8096c: b holds F, a0 = b *)
  cbv beta. intros WC cC HwleC (-> & regsC & memC & mdC & -> & HJC & HPC & HretC & HcpyC & HkeepC & HpresC & HsameC).
  assert (HJgxC : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 memC mdC k)
    by (eapply gx_pack0; [exact HJC | exact Hag1]).
  pose proof HJC as (HARC & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HARC Hfin) as (_ & _ & _ & HFSpresC).
  rewrite Efa in HFSpresC. change (fs_frame_bytes PE_CID / 8) with 16 in HFSpresC.
  assert (PPC : forall r : Z, acallee_saved r -> getr regsC (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r))
    by exact HPC.
  (* the PS_PSP slot as the run stored it at 0x80954, at the copy's entry memory, then kept by the copy *)
  assert (SP0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (c_sp1 cx + 88) 8 (pF cx fp + 32)).
  { refine (h_field E _ (restrict (w_H W3) ms0) 0 9 88 96 88 96 _ (c_sp1 cx) 88 8 (SOff 23 32)
      (pF cx fp + 32) HS eq_refl U9 _ _ _ _).
    - cbn. tauto.
    - apply (h_denot_off E 23 (pF cx fp) 32); [rewrite E23; exact R23 | lia].
    - cbn. lia.
    - cbn. lia. }
  assert (SPC : rdword (aview SEGS (w_H W3) memC) (c_sp1 cx + 88) = Some (pF cx fp + 32)).
  { rewrite <- (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms0) (c_sp1 cx + 88) (pF cx fp + 32) SP0 ltac:(lia)).
    apply rdword_ext. intros i Hi.
    apply HkeepC; [lia | pa_dlia1 Hbapp | unfold ESTACK; lia]. }
  (* 0x8096c ld a0,0x58(s1): the symbolic state back from the copy *)
  remember (Eimg (Ereg regsC [])) as EC eqn:HECdef.
  assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply Eimg_env).
  assert (ELc : forall n, (n < A_TEXT)%nat -> ew EC n = ew (Ereg regsC []) n)
    by (intros n Hn; subst EC; apply Eimg_low; exact Hn).
  assert (XC : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew EC n = getr regsC r)
    by (intros n r Hn Hr; rewrite ELc by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  (* its registers as values: the callee-saved ones as at 0x80968, a0 = b *)
  assert (EC2 : ew EC 2 = w64 (c_sp1 cx)).
  { rewrite (XC 2%nat 2%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 2); [exact (PPC 2 ltac:(unfold acallee_saved; lia))|]. rewrite Q2, E2. exact Rsp. }
  assert (EC3 : ew EC 3 = getr (c_regs cx) 3).
  { rewrite (XC 3%nat 3%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 3); [exact (PPC 3 ltac:(unfold acallee_saved; lia))|]. rewrite Q3, E3. exact Rgp. }
  assert (EC4 : ew EC 4 = getr (c_regs cx) 4).
  { rewrite (XC 4%nat 4%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 4); [exact (PPC 4 ltac:(unfold acallee_saved; lia))|]. rewrite Q4, E4. exact Rtp. }
  assert (EC8 : ew EC 8 = w64 (spZ (c_regs cx))).
  { rewrite (XC 8%nat 8%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 8); [exact (PPC 8 ltac:(unfold acallee_saved; lia))|]. rewrite Q8, E8. exact Rs0. }
  assert (EC9 : ew EC 9 = w64 (c_sp1 cx)).
  { rewrite (XC 9%nat 9%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 9); [exact (PPC 9 ltac:(unfold acallee_saved; lia))|]. rewrite Q9, E9. exact Rs1. }
  assert (EC18 : ew EC 18 = w64 (pa_val (A_OBJ 2))).
  { rewrite (XC 18%nat 18%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 18); [exact (PPC 18 ltac:(unfold acallee_saved; lia))|].
    rewrite Q18, E18. exact R18. }
  assert (EC19 : ew EC 19 = w64 bb).
  { rewrite (XC 19%nat 19%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 19); [exact (PPC 19 ltac:(unfold acallee_saved; lia))|].
    rewrite Q19, E10. exact R10. }
  assert (EC20 : ew EC 20 = w64 (pF cx fp)).
  { rewrite (XC 20%nat 20%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 20); [exact (PPC 20 ltac:(unfold acallee_saved; lia))|].
    rewrite Q20, E20. exact R20. }
  assert (EC23 : ew EC 23 = w64 (pF cx fp)).
  { rewrite (XC 23%nat 23%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 23); [exact (PPC 23 ltac:(unfold acallee_saved; lia))|].
    rewrite Q23, E23. exact R23. }
  assert (EC25 : ew EC 25 = w64 (pSH cx fp)).
  { rewrite (XC 25%nat 25%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 25); [exact (PPC 25 ltac:(unfold acallee_saved; lia))|].
    rewrite Q25, E25. exact R25. }
  assert (EC27 : ew EC 27 = getr (ms_regs ms3) 27).
  { rewrite (XC 27%nat 27%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms0) 27); [exact (PPC 27 ltac:(unfold acallee_saved; lia))|].
    rewrite Q27, E27. reflexivity. }
  assert (UC9 : bv_unsigned (ew EC 9) = c_sp1 cx) by (rewrite EC9; unfold w64; apply unsigned_lit_small; lia).
  assert (UC10 : bv_unsigned (ew EC 10) = bb).
  { rewrite (XC 10%nat 10%bv), HretC by first [unfold A_TEXT; lia | reflexivity].
    unfold w64. apply unsigned_lit_small; lia. }
  assert (UC18 : bv_unsigned (ew EC 18) = pa_val (A_OBJ 2)) by (rewrite EC18; unfold w64; apply unsigned_lit_small; lia).
  assert (UC25 : bv_unsigned (ew EC 25) = pSH cx fp) by (rewrite EC25; unfold w64; apply unsigned_lit_small; lia).
  assert (HS3 : st_ok_pi SEGS VAL EC (mkSS 564 sr_atoms pa_rs2 None pa_facts)
    (restrict (w_H W3) (mkst regsC (getr (ms_regs ms0) 1) memC (seg_rom SEGS)))).
  { rewrite HECdef in UC9, UC10, UC18, UC25, EC23 |- *.
    apply (entryR 564 (mkst regsC (getr (ms_regs ms0) 1) memC (seg_rom SEGS)) W3 [] pa_rs2 pa_facts);
      [cbn [ms_pc_val mkst]; rewrite Q1; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | vm_compute; reflexivity | | |]; cbn [ms_regs ms_mem mkst].
    - unfold pa_rs2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite UC9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (h_slot_chunk_ok _ (w_H W3) memC (c_sp1 cx) 88 (SOff 23 32) (pF cx fp + 32)); [exact SPC | | lia].
        apply (h_denot_off _ 23 (pF cx fp) 32); [exact EC23 | lia].
      + rewrite UC18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply HGW. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + rewrite UC25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS).
        replace (pSH cx fp + o) with (shadow_addr (pF cx fp) + o) by (rewrite ESH; unfold shadow_addr; lia).
        apply HFSpresC. lia.
    - apply pairwise_disjoint_of_extents. unfold pa_rs2, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UC9, UC18, UC25.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - unfold pa_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2 fst snd]. unfold pcap_img_end, IMG_TOP.
      rewrite UC9, UC10, UC18, UC25. repeat match goal with |- _ /\ _ => split end;
        first [ lia | (change (2 ^ 5) with 32; exact Hs1m) | (change (2 ^ 4) with 16; exact Hb16)
              | (change (2 ^ 3) with 8; exact (proj2 (proj2 HSHr)))
              | (change (2 ^ 0) with 1; apply Z.mod_1_r) | exact I ]. }
  clear HECdef ELc.
  assert (SHOK3 : sh_ok SEGS (SLit SB) [] EC (mrestrict (w_H W3) memC)) by constructor.
  (* 0x8096c ld a0 (&ps); 0x80970 g_file := b; 0x80974..0x8097c ps comes into scope; 0x80980..0x80988; stops at
     0x8098c jal __asan_memset *)
  paj_run_tok RUNX HS3 HJgxC SHOK3 (0, 0); [ pa_awr UC9 UC18 UC25 Efa |].
  pmkst HS3.
  prreg HS3 (1%bv : bv 5) T1. prreg HS3 (2%bv : bv 5) T2. prreg HS3 (3%bv : bv 5) T3. prreg HS3 (4%bv : bv 5) T4.
  prreg HS3 (10%bv : bv 5) T10. prreg HS3 (11%bv : bv 5) T11. prreg HS3 (12%bv : bv 5) T12.
  prreg HS3 (8%bv : bv 5) T8. prreg HS3 (9%bv : bv 5) T9. prreg HS3 (18%bv : bv 5) T18.
  prreg HS3 (19%bv : bv 5) T19. prreg HS3 (20%bv : bv 5) T20. prreg HS3 (23%bv : bv 5) T23.
  prreg HS3 (25%bv : bv 5) T25. prreg HS3 (27%bv : bv 5) T27.
  (* the three shadow bytes of ps, as the run has just written them (0x80974, 0x80978, 0x8097c) *)
  assert (SHz : forall i : nat, (4 <= i <= 6)%nat ->
    aview SEGS (w_H W3) (ms_mem ms1) (pSH cx fp + Z.of_nat i) = Some 0).
  { intros i Hi. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms1)); [|lia].
    refine (h_field EC _ (restrict (w_H W3) ms1) 2 25 4 7 4 7 _ (pSH cx fp) (Z.of_nat i) 1
      (SLit 0) 0 HS3 eq_refl UC25 _ eq_refl _ _).
    - assert (Hc : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia.
      destruct Hc as [Hc1 | [Hc1 | Hc1]]; subst i; cbn; tauto.
    - cbn. lia.
    - cbn. lia. }
  (* the PS_PSP slot, read back at 0x8096c: as at the copy's return (the run does not write it) *)
  assert (SPm : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (c_sp1 cx + 88) 8 (pF cx fp + 32)).
  { refine (h_field EC _ (restrict (w_H W3) ms1) 0 9 88 96 0 0 _ (c_sp1 cx) 88 8 (SOff 23 32)
      (pF cx fp + 32) HS3 eq_refl UC9 _ _ _ _).
    - cbn. tauto.
    - apply (h_denot_off EC 23 (pF cx fp) 32); [exact EC23 | lia].
    - cbn. lia.
    - cbn. lia. }
  (* g_file as the run stored it at 0x80970 (region 1, s2 + 0; s3 = b), at the memset's entry memory *)
  assert (GF0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (pa_val (A_OBJ 2) + 0) 8 bb).
  { refine (h_field EC _ (restrict (w_H W3) ms1) 1 18 0 8 0 8 _ (pa_val (A_OBJ 2)) 0 8 (SOff 19 0) bb
      HS3 eq_refl UC18 _ _ _ _).
    - cbn. tauto.
    - rewrite h_denot_off0, EC19. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  rewrite Z.add_0_r in GF0.
  (* 0x8098c jal __asan_memset: a0 = ps = F + 32, a1 = 0xa5, a2 = 24 *)
  edestruct gx_open as (memS5 & HJ5 & Hag5); [exact HJgxC|].
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (pa_sigma PS___asan_memset) HSET
      W3 (ms_regs ms1) (ms_mem ms1) LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) memS5 (c_md cx) [(PE_CID, fp)] ly3 S3 _ k
      (pF cx fp + 32) 165 24 (c_sp1 cx - spZ (c_regs cx)) _ HJ5).
    - rewrite T10, EC23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite T11. reflexivity.
    - rewrite T12. reflexivity.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite T2, EC2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact (o_mod16 B MT KS cx HB).
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite T3, EC3. exact Hgp0.
    - rewrite T4, EC4. exact Htp0.
    - reflexivity.
    - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [apply (awr_ownframe _ _ _ _ _ _ _ _ a Efa); left; lia | unfold ESTACK; lia].
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. pa_dlia1 Hfapp.
    - (* the shadow of ps: the three bytes the run has just zeroed (0x80974..0x8097c) *)
      apply (h_ra_frame (w_H W3) (ms_mem ms1) (pF cx fp) (pSH cx fp) 32 24 ESH Hfa64);
        [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      apply SHz. lia.
    - (* its hull: [SH, SH + 8), inside the frame's shadow, present since the copy's return *)
      intros _ s Hs. unfold shadow_addr in Hs.
      assert (Hs' : 0 <= s - pSH cx fp < 16)
        by (destruct HSHr as (_ & _ & Hm8); rewrite ESH; unfold SHADOW_OFF in *;
            Z.div_mod_to_equations; lia).
      apply (aview_keeps_vis SEGS (w_H W3) memC (ms_mem ms1) s HG1).
      apply aview_some_of_apresent.
      replace s with (shadow_addr (pF cx fp) + (s - pSH cx fp))
        by (rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia).
      exact (proj1 (HFSpresC (s - pSH cx fp) ltac:(lia))).
    - exact I. }
  (* back from __asan_memset at 0x80990, with ps filled with 0xa5 *)
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hret2 & Hset & Hkeep & Hpres2 & Hsame).
  assert (HJgx2 : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem2 md2 k)
    by (eapply gx_pack0; [exact HJ2 | exact Hag5]).
  (* 0x80990 auipc / 0x80994 addi: the path literal; 0x80998 mv a0,s2; 0x8099c jal pcap_source_open *)
  pose proof (entry0 600 (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)) W3
    ltac:(cbn [ms_pc_val mkst]; rewrite T1; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl) as HS2.
  cbn [ms_regs ms_mem mkst] in HS2.
  remember (Eimg (Ereg regs2 [])) as Ex eqn:HEx in HS2.
  assert (HEIx : img_env VAL A_LIM Ex) by (subst Ex; apply Eimg_env).
  assert (ELx : forall n, (n < A_TEXT)%nat -> ew Ex n = ew (Ereg regs2 []) n)
    by (intros n Hn; subst Ex; apply Eimg_low; exact Hn).
  assert (EO3 : ew Ex 244%nat = Z_to_bv 64 (pa_val (A_OBJ 3)))
    by (subst Ex; apply (Eimg_img _ 244%nat); unfold A_TEXT, A_LIM; lia).
  assert (SHOK2 : sh_ok SEGS (SLit SB) [] Ex (mrestrict (w_H W3) mem2)) by constructor.
  paj_run_tok RUNX HS2 HJgx2 SHOK2 (0, 0); [ apply awr_ok_x_nil |].
  (* at the call of pcap_source_open, 0x8099c: the run wrote nothing *)
  assert (HFm2 : ms_mem ms2 = mem2) by exact (frame_of_nil _ _ _ HF2).
  pmkst HS2.
  prreg HS2 (1%bv : bv 5) P1. prreg HS2 (2%bv : bv 5) P2. prreg HS2 (3%bv : bv 5) P3. prreg HS2 (4%bv : bv 5) P4.
  prreg HS2 (8%bv : bv 5) P8. prreg HS2 (10%bv : bv 5) P10. prreg HS2 (11%bv : bv 5) P11.
  prreg HS2 (9%bv : bv 5) P9. prreg HS2 (27%bv : bv 5) P27.
  prreg HS2 (19%bv : bv 5) P19. prreg HS2 (20%bv : bv 5) P20.
  prreg HS2 (23%bv : bv 5) P23. prreg HS2 (25%bv : bv 5) P25.
  (* the registers at the call, as values *)
  assert (PP : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r))
    by exact HP2.
  assert (XR : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew Ex n = getr regs2 r)
    by (intros n r Hn Hr; rewrite ELx by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  assert (Y2 : getr (ms_regs ms2) 2 = w64 (c_sp1 cx)).
  { rewrite P2, (XR 2%nat 2%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 2); [exact (PP 2 ltac:(unfold acallee_saved; lia)) | rewrite T2; exact EC2]. }
  assert (Y3 : getr (ms_regs ms2) 3 = getr (c_regs cx) 3).
  { rewrite P3, (XR 3%nat 3%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 3); [exact (PP 3 ltac:(unfold acallee_saved; lia)) | rewrite T3; exact EC3]. }
  assert (Y4 : getr (ms_regs ms2) 4 = getr (c_regs cx) 4).
  { rewrite P4, (XR 4%nat 4%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 4); [exact (PP 4 ltac:(unfold acallee_saved; lia)) | rewrite T4; exact EC4]. }
  assert (Y8 : getr (ms_regs ms2) 8 = w64 (spZ (c_regs cx))).
  { rewrite P8, (XR 8%nat 8%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 8); [exact (PP 8 ltac:(unfold acallee_saved; lia)) | rewrite T8; exact EC8]. }
  assert (Y10 : getr (ms_regs ms2) 10 = w64 (pF cx fp + 32)).
  { rewrite P10, (XR 18%nat 18%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 18); [exact (PP 18 ltac:(unfold acallee_saved; lia)) |].
    rewrite T18, EC23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Y11 : getr (ms_regs ms2) 11 = Z_to_bv 64 (pa_val (A_OBJ 3))) by (rewrite P11; exact EO3).
  assert (Hsp : spZ (ms_regs ms2) = c_sp1 cx) by (unfold spZ; rewrite Y2; unfold w64; apply unsigned_lit_small; lia).
  (* the copy b and the input block, against the frame and the image *)
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 bb (p_nF cx) HAR Hbin) as HBo.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HBo.
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hpin) as HPo.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HPo.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hbin Hfin) as NBf.
  unfold zdisjoint in NBf. cbn [fst snd] in NBf. rewrite Efa in NBf. change (fs_frame_bytes PE_CID) with 128 in NBf.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as NPf.
  unfold zdisjoint in NPf. cbn [fst snd] in NPf. rewrite Efa in NPf. change (fs_frame_bytes PE_CID) with 128 in NPf.
  (* what the phase wrote: the runs wrote the PS_PSP slot, g_file and three shadow bytes; __asan_memcpy wrote b and
     its scratch window below sp, __asan_memset ps and the same window; the last run wrote nothing. Every other
     byte is as at PP_K1. *)
  pose (PW := fun a => (c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/
                      (pSH cx fp + 4 <= a < pSH cx fp + 7)).
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ PW a ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms) PW HFr).
    intros bw wlo whi a Hwn Ha. vm_compute in Hwn.
    repeat (destruct Hwn as [Hq | Hwn];
      [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U9, ?U18, ?U25 in Ha; cbv [PW]; lia |]).
    destruct Hwn. }
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ PW a ->
    aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms) (ms_mem ms0) PW HFr0).
    intros bw wlo whi a Hwn Ha. vm_compute in Hwn.
    repeat (destruct Hwn as [Hq | Hwn];
      [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U9, ?U18, ?U25 in Ha; cbv [PW]; lia |]).
    destruct Hwn. }
  assert (KRC : forall a, 0 <= a < 2 ^ 64 -> ~ PW a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) memC a).
  { apply (kept_of_frame (segs := SEGS) EC _ (w_H W3) memC (ms_mem ms1) PW HFr1).
    intros bw wlo whi a Hwn Ha. vm_compute in Hwn.
    repeat (destruct Hwn as [Hq | Hwn];
      [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?UC9, ?UC18, ?UC25 in Ha; cbv [PW]; lia |]).
    destruct Hwn. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/
       (pSH cx fp + 4 <= a < pSH cx fp + 7)) ->
    ~ (pF cx fp + 32 <= a < pF cx fp + 56) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
    ~ (bb <= a < bb + p_nF cx) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2 H3 H4. rewrite HFm2, (Hkeep a Ha ltac:(lia) ltac:(unfold ESTACK; lia)).
    rewrite (KRC a Ha H1), (HkeepC a Ha ltac:(lia) ltac:(unfold ESTACK; lia)), (KR2 a Ha H1).
    exact (KR1 a Ha H1). }
  assert (ELC0 : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  (* the copy: b's bytes at the call are the input's from its second byte on *)
  assert (KCP : forall j, 0 <= j < p_nF cx ->
    aview SEGS (w_H W3) (ms_mem ms2) (bb + j) = aview SEGS (w_H W3) (ms_mem ms3) (p_src cx + j)).
  { intros j Hj.
    assert (Hnb : ~ PW (bb + j)) by (cbv [PW]; pa_dlia2 Hbapp HBo).
    assert (Hnp : ~ PW (p_src cx + j)) by (rewrite Esrc; cbv [PW]; pa_dlia2 Hpapp HPo).
    rewrite HFm2, (Hkeep (bb + j) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
    rewrite (KRC (bb + j) ltac:(lia) Hnb), (HcpyC j Hj).
    rewrite (KR2 (p_src cx + j) ltac:(rewrite Esrc; lia) Hnp).
    exact (KR1 (p_src cx + j) ltac:(rewrite Esrc; lia) Hnp). }
  assert (GCP2 : garr8 SEGS (rdW W3 (ms_mem ms2)) bb (p_C cx)).
  { intros j Hj.
    assert (Hj1 : (S j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
      by (rewrite length_map, Epl; cbn [length]; unfold p_C, p_F in Hj; rewrite length_map, Epl in Hj;
          cbn [tl] in Hj; lia).
    destruct (Hin (S j) Hj1) as [Hv Hr].
    assert (En : nth (S j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0 = nth j (p_C cx) 0)
      by (unfold p_C, p_F; rewrite Epl; reflexivity).
    rewrite En in Hv, Hr. split; [|exact Hr].
    assert (HA3 : aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + Z.of_nat (S j)) = Some (nth j (p_C cx) 0))
      by (apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [exact Hv | lia]).
    assert (HA2 : aview SEGS (w_H W3) (ms_mem ms2) (bb + Z.of_nat j) = Some (nth j (p_C cx) 0)).
    { rewrite (KCP (Z.of_nat j)) by (rewrite <- ELC0; lia). rewrite <- HA3. f_equal. rewrite Esrc. lia. }
    exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms2) _ _ HA2)). }
  assert (BOK : bytes_ok (p_C cx)).
  { apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx. destruct Hx as (j & Hj & <-).
    exact (proj2 (GCP2 j Hj)). }
  (* 0x8099c jal pcap_source_open(&ps, "<fuzz-input>") *)
  rewrite pa_sigma_pcap_source_open.
  edestruct gx_open as (memS3 & HJ3 & Hag3); [exact HJgx2|].
  pose proof HJ3 as (HAR1 & _).
  (* the facts the call reads, at the call memory *)
  pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as HFo.
  rewrite Efa in HFo. change (fs_frame_bytes PE_CID) with 128 in HFo.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo.
  assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms2))); [exact (proj1 Hsaved)|].
    intros i Hi. apply KALL; unfold PW; pa_dlia1 HSHr. }
  assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (proj2 Hsaved 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms2))); [exact H0|].
    intros i Hi. apply KALL; unfold PW; pa_dlia1 HSHr. }
  assert (HARO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms2)))
    by (eapply aro_now; eassumption).
  assert (EBB : blocks_bytes S3 = blocks_bytes (c_S cx) + p_nF cx).
  { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
    rewrite (bsum_perm _ _ Hperm), bsum_app. cbn [bsum fold_right snd]. lia. }
  eapply SRr_bind.
  { eapply (OPENS LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS3 (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms2) _ k (ms_regs ms2) (pch cx) (pPS cx fp) (p_nF cx) bb (c_M cx)
      (p_C cx) PE_CID fp HJ3).
    - exact HARO.
    - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite P1, unsigned_lit_small by lia. lia.
    - rewrite Y3. exact Hgp0.
    - rewrite Y4. exact Htp0.
    - rewrite Y10. reflexivity.
    - rewrite Y11. reflexivity.
    - rewrite Hsp. unfold s0Z at 1. rewrite Y8. unfold w64. rewrite unsigned_lit_small by lia.
      eapply pch_achain; [exact HB | exact HJ3 | exact Hag3 | exact Hs8 | exact Hs16].
    - unfold raZ. rewrite P1, unsigned_lit_small by lia.
      unfold pch, spine. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
      + cbn [map]. rewrite HraL. exact (proj1 HCTX).
      + cbn [map]. exact (proj2 HCTX).
    - rewrite Hsp. pose proof Hs1m as Hm. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq].
      apply Z.mod_divide; [lia|]. exists (2 * q). lia.
    - rewrite Hsp, TPCAP_SOURCE_OPEN_STK_val. unfold LLVMF_STK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, Etop. lia.
    - rewrite Hfrs. cbn [length Z.of_nat]. lia.
    - left. reflexivity.
    - rewrite Efa. unfold pPS, PO_PS. lia.
    - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS. exact (h_mod64_add (pF cx fp) 32 Hfa64 eq_refl).
    - unfold pPS, PO_PS.
      apply (h_ra_frame (w_H W3) (ms_mem ms2) (pF cx fp) (pSH cx fp) 32 24 ESH Hfa64); [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      rewrite HFm2, (Hkeep (pSH cx fp + 4 + j) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(unfold ESTACK; lia)).
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      apply SHz. lia.
    - exists sink_token. split; [left; reflexivity|]. unfold sink_token. cbn [fst snd]. lia.
    - apply HROI. exact HARO.
    - exact (proj1 (HPATH ly3 S3 W3 (ms_mem ms2) _ HAR1)).
    - exact (proj2 (HPATH ly3 S3 W3 (ms_mem ms2) _ HAR1)).
    - eapply (val_mem_frame SEGS); [|exact (proj2 Hglob)]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply KALL; [lia | lia | lia | lia | lia].
    - eapply (val_mem_frame SEGS); [|exact GF0]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). rewrite HFm2. apply Hkeep; [lia | lia | unfold ESTACK; lia].
    - lia.
    - apply (OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceCloseSpec.asource_none_frame_segs
        SEGS KS (rdW W3 (ms_mem ms3))); [|exact Hsrcnone].
      intros a Ha. apply (mbyte_of_aview SEGS).
      destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He).
      pose proof (pa_img_range a Hi) as Hr1. unfold pcap_img_end, IMG_TOP in Hr1.
      apply KALL; [lia | | lia | lia | lia].
      unfold PW. intros [Hp | [Hp | Hp]]; [lia | | lia].
      apply (HGENV a); [| exact Ha]. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    - symmetry. exact ELC0.
    - lia.
    - intros _. split; [exact Hbin|]. split; [exact GCP2 | exact BOK].
    - eapply meta_now; eassumption.
    - unfold EV_OPEN, EV_FUZZ_FOPEN, EV_LIB in *. lia.
    - rewrite EBB. unfold SRC_FILE_BLOCK, LIVE_LIB in *. lia.
    - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT SRC_FILE_BLOCK) MLAWS Hmok Hmo
        (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia))).
      pose proof (PA_K12_need MT MLAWS cx) as Hn. pose proof (mo_free_nonneg MT MLAWS).
      pose proof (mo_malloc_nonneg MT MLAWS (p_bn cx) ltac:(lia)).
      pose proof (mo_malloc_nonneg MT MLAWS SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)).
      unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in *. lia.
    - exact (proj1 HFMU).
    - exact (proj2 HFMU). }
  (* back from pcap_source_open at PP_K2 0x809a0 *)
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HP4 & Hfr4 & Hfd4 & Hfs4 & HK4 & Hmle4 &
    Hz12 & Hz16 & Hz20 & Harm).
  rewrite P1.
  destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
  (* the body bytes outside the slots and the shadow, from PP_K1 to the call and then across the call *)
  assert (Hns1 : forall a, hfoot_ns cx fp a ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. unfold hfoot_ns in Ha. apply KALL; [lia | pa_dlia2 Hfapp Hpapp | lia | lia | lia]. }
  destruct (tail_kept_ns cx fp W3 ms3 W3 ms2 Hns1 Hsaved Hhdr Hin) as (Hsaved1 & Hhdr1 & Hin1).
  assert (Hfoot : forall a, hfoot cx fp a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms2) a).
  { intros a Ha.
    refine (foot_kept B MT KS cx fp ly3 S3 W3 (ms_mem ms2) W4 mem4 _ _
      (fun a => pPS cx fp <= a < pPS cx fp + 22) HB
      (fun a Ha1 Ha2 _ => K1 a Ha1 Ha2) K2 K4 _ Hfin Efa (input_block B MT KS cx ly3 S3 _ HB Hperm) _ a Ha);
      [rewrite Hsp; lia|].
    intros x Hx Hw.
    exact (frame_off_hfoot B MT KS LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 22 HB HAR Hperm Hfin Efa
      ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS; lia) x Hx Hw). }
  destruct (tail_kept_ns cx fp W3 ms2 W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS))
    ltac:(intros a Ha; cbn [ms_mem mkst]; apply Hfoot; unfold hfoot, hfoot_ns in *; tauto)
    Hsaved1 Hhdr1 Hin1) as (T1' & T2' & T3').
  assert (PK : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms2) (Z_to_bv 5 r))
    by exact HP4.
  (* the frame's shadow at PP_K2 is PSH_entry with ps in scope, which is PSH_ps *)
  assert (Hnth : forall j, (j < 16)%nat -> (j < 4 \/ 7 <= j)%nat -> nth j PSH_ps 0 = nth j PSH_entry 0).
  { intros j Hj Hj2.
    do 16 (destruct j as [|j]; [solve [vm_compute; reflexivity | exfalso; lia] |]).
    exfalso. lia. }
  assert (TSH : pshadow cx fp W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) PSH_ps).
  { intros i Hi. cbn [ms_mem mkst]. vm_compute in Hi.
    rewrite Hfoot by (unfold hfoot; right; right; right; left; lia).
    destruct (Nat.ltb_spec i 4) as [H4|H4]; [|destruct (Nat.leb_spec 7 i) as [H7|H7]].
    - rewrite (KALL (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(lia)
        ltac:(pa_dlia1 Hbapp)).
      rewrite (Hsh i ltac:(vm_compute; lia)), (Hnth i ltac:(lia) ltac:(lia)). reflexivity.
    - rewrite (KALL (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(pa_dlia1 Hfapp) ltac:(lia)
        ltac:(pa_dlia1 Hbapp)).
      rewrite (Hsh i ltac:(vm_compute; lia)), (Hnth i ltac:(lia) ltac:(lia)). reflexivity.
    - rewrite HFm2, (Hkeep (pSH cx fp + Z.of_nat i) ltac:(lia) ltac:(pa_dlia1 Hfapp)
        ltac:(unfold ESTACK; lia)).
      rewrite (SHz i ltac:(lia)).
      assert (Hq : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia.
      destruct Hq as [Hq|[Hq|Hq]]; subst i; vm_compute; reflexivity. }
  (* the registers of the body at PP_K2, from the call's callee-saved post *)
  assert (PRG : pregs cx (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS))).
  { unfold pregs. cbn [ms_regs mkst].
    split; [transitivity (getr (ms_regs ms2) 2); [exact (PK 2 ltac:(unfold acallee_saved; lia)) | exact Y2]|].
    split; [transitivity (getr (ms_regs ms2) 8); [exact (PK 8 ltac:(unfold acallee_saved; lia)) | exact Y8]|].
    split; [transitivity (getr (ms_regs ms2) 9); [exact (PK 9 ltac:(unfold acallee_saved; lia)) |
              rewrite P9, (XR 9%nat 9%bv) by first [unfold A_TEXT; lia | reflexivity];
              transitivity (getr (ms_regs ms1) 9); [exact (PP 9 ltac:(unfold acallee_saved; lia)) |
                rewrite T9; exact EC9]]|].
    split; [transitivity (getr (ms_regs ms2) 27); [exact (PK 27 ltac:(unfold acallee_saved; lia)) |
              rewrite P27, (XR 27%nat 27%bv) by first [unfold A_TEXT; lia | reflexivity];
              transitivity (getr (ms_regs ms1) 27); [exact (PP 27 ltac:(unfold acallee_saved; lia)) |
                rewrite T27, EC27; exact Rs11]]|].
    split; [transitivity (getr (ms_regs ms2) 3); [exact (PK 3 ltac:(unfold acallee_saved; lia)) | exact Y3]|].
    transitivity (getr (ms_regs ms2) 4); [exact (PK 4 ltac:(unfold acallee_saved; lia)) | exact Y4]. }
  (* the cut's callee-saved registers, through the three calls *)
  assert (RK19 : getr regs4 19 = w64 bb).
  { transitivity (getr (ms_regs ms2) 19); [exact (PK 19 ltac:(unfold acallee_saved; lia))|].
    rewrite P19, (XR 19%nat 19%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 19); [exact (PP 19 ltac:(unfold acallee_saved; lia))|].
    rewrite T19. exact EC19. }
  assert (RK20 : getr regs4 20 = w64 (pF cx fp)).
  { transitivity (getr (ms_regs ms2) 20); [exact (PK 20 ltac:(unfold acallee_saved; lia))|].
    rewrite P20, (XR 20%nat 20%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 20); [exact (PP 20 ltac:(unfold acallee_saved; lia))|].
    rewrite T20. exact EC20. }
  assert (RK23 : getr regs4 23 = w64 (pF cx fp)).
  { transitivity (getr (ms_regs ms2) 23); [exact (PK 23 ltac:(unfold acallee_saved; lia))|].
    rewrite P23, (XR 23%nat 23%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 23); [exact (PP 23 ltac:(unfold acallee_saved; lia))|].
    rewrite T23. exact EC23. }
  assert (RK25 : getr regs4 25 = w64 (pSH cx fp)).
  { transitivity (getr (ms_regs ms2) 25); [exact (PK 25 ltac:(unfold acallee_saved; lia))|].
    rewrite P25, (XR 25%nat 25%bv) by first [unfold A_TEXT; lia | reflexivity].
    transitivity (getr (ms_regs ms1) 25); [exact (PP 25 ltac:(unfold acallee_saved; lia))|].
    rewrite T25. exact EC25. }
  assert (EFDS : m_fds md4 = m_fds (c_md cx)).
  { rewrite Hfd4.
    repeat first [ rewrite (proj1 (fs_wvb _ _)) | rewrite (proj1 (sbm_fds _ _ Hsame))
                 | rewrite (proj1 (sbm_fds _ _ HsameC)) ].
    exact Hfds. }
  assert (EFS : m_fs md4 = m_fs (c_md cx)).
  { rewrite Hfs4.
    repeat first [ rewrite (proj2 (fs_wvb _ _)) | rewrite (proj2 (sbm_fds _ _ Hsame))
                 | rewrite (proj2 (sbm_fds _ _ HsameC)) ].
    exact Hfs. }
  (* the spill slots the cut states: two from PP_K1, PS_PSP written by the run at 0x80954 *)
  assert (SD1 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (c_sp1 cx + PS_D) = Some (p_d cx)).
  { rewrite <- SD. apply rdword_ext. intros i Hi.
    apply KALL; [unfold PS_D; lia | unfold PS_D; lia | unfold PS_D; pa_dlia1 Hfapp | unfold PS_D; lia
                | unfold PS_D; lia]. }
  assert (SG1 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (c_sp1 cx + PS_GLEN) = Some (pa_val (A_HI 8))).
  { rewrite <- SGLEN. apply rdword_ext. intros i Hi.
    apply KALL; [unfold PS_GLEN; lia | unfold PS_GLEN; lia | unfold PS_GLEN; pa_dlia1 Hfapp
                | unfold PS_GLEN; lia | unfold PS_GLEN; lia]. }
  assert (SP1 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (c_sp1 cx + PS_PSP) = Some (pPS cx fp)).
  { unfold PS_PSP, pPS, PO_PS.
    rewrite <- (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms1) (c_sp1 cx + 88) (pF cx fp + 32) SPm ltac:(lia)).
    apply rdword_ext. intros i Hi. rewrite HFm2.
    apply Hkeep; [lia | pa_dlia1 Hfapp | unfold ESTACK; lia]. }
  assert (SLOT : forall off v, 8 <= off /\ off + 8 <= 120 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms2)) (c_sp1 cx + off) = Some v ->
    rdword (aview SEGS (w_H W4) mem4) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hv.
    rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms2)) (aview SEGS (w_H W4) mem4)); [exact Hv|].
    intros i Hi. apply Hfoot. unfold hfoot. lia. }
  (* the harness's globals: image bytes, kept by the call's image clause *)
  assert (GIMG : forall a, inG pe_G a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms2) a).
  { intros a Ha. apply K3.
    - exact (proj1 (HGX a Ha)).
    - exact (proj2 (HGX a Ha)).
    - exact (proj1 (proj2 (proj2 (HGD a Ha)))).
    - exact (proj1 (proj2 (proj2 (proj2 (HGD a Ha))))). }
  (* the two globals at the call memory, then across the call *)
  assert (GF1 : val_mem SEGS (rdW W3 (ms_mem ms2)) (pa_val (A_OBJ 2)) 8 bb).
  { eapply (val_mem_frame SEGS); [|exact GF0]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). rewrite HFm2. apply Hkeep; [lia | lia | unfold ESTACK; lia]. }
  assert (GLEN1 : val_mem SEGS (rdW W3 (ms_mem ms2)) (pa_val (A_OBJ 4)) 8 (p_nF cx)).
  { eapply (val_mem_frame SEGS); [|exact (proj2 Hglob)]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). apply KALL; [lia | lia | lia | lia | lia]. }
  assert (GLOB4 : p_glob cx W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) bb).
  { split; cbn [ms_mem mkst].
    - eapply (val_mem_frame SEGS); [|exact GF1]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply GIMG. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. lia.
    - eapply (val_mem_frame SEGS); [|exact GLEN1]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
      apply (mbyte_of_aview SEGS). apply GIMG. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. lia. }
  (* the copy at PP_K2: b is a block of the caller of the call, outside ps *)
  assert (GCP4 : p_copy cx W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) bb).
  { unfold p_copy. intros j Hj. destruct (GCP2 j Hj) as [Hv Hr]. split; [|exact Hr].
    assert (Hj' : 0 <= Z.of_nat j < p_nF cx) by (rewrite <- ELC0; lia).
    assert (HA : aview SEGS (w_H W4) mem4 (bb + Z.of_nat j) = Some (nth j (p_C cx) 0)).
    { rewrite (K2 bb (p_nF cx) (Z.of_nat j) Hbin ltac:(lia) ltac:(cbv beta; unfold pPS, PO_PS; lia)).
      apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms2)); [exact Hv | lia]. }
    exact (proj1 (val_mem1_of_aview SEGS (w_H W4) mem4 _ _ HA)). }
  (* the body at PP_K2 *)
  assert (PB2 : pe_body cx fp PP_K2 W4 (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) PSH_ps).
  { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact PRG|]. split; [exact T1'|]. split; [exact T2'|]. split; [exact TSH|].
    split; [vm_compute; reflexivity | exact T3']. }
  destruct Harm as [(HJ4 & Ha0 & Hgood & hh & Hh4096 & Hh16 & Hbl4 & Hpsf & Hpsw & Hsrc4 & Hmle2)
                   |(HJ4 & Ha0 & Hbad & Hps0 & Hps812 & Hbl4 & Hsrc4)].
  - (* the file was accepted *)
    eapply (NEXT cx fp (k + EV_FUZZ_FOPEN) (acc + mo_malloc MT SRC_FILE_BLOCK) ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) md4 HB).
    + eapply gx_pack0; [exact HJ4 | exact Hag3].
    + rewrite Hfr4. exact Hfrs.
    + exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle2).
    + unfold GI_K2. exists bb.
      split; [exact PB2|]. split; [exact Hn26|]. split; [exact EFDS|]. split; [exact EFS|].
      split; [exact RK19|]. split; [exact RK20|]. split; [exact RK23|]. split; [exact RK25|].
      split; [exact (SLOT PS_D (p_d cx) ltac:(unfold PS_D; lia) SD1)|].
      split; [exact (SLOT PS_GLEN (pa_val (A_HI 8)) ltac:(unfold PS_GLEN; lia) SG1)|].
      split; [exact (SLOT PS_PSP (pPS cx fp) ltac:(unfold PS_PSP; lia) SP1)|].
      split; [exact GLOB4|].
      split; [exact GCP4|].
      left. split; [rewrite <- goodZ_good; exact Hgood|].
      split; [cbn [ms_regs mkst]; exact Ha0|].
      split; [unfold EV_FUZZ_FOPEN; lia|].
      split; [unfold PA_K2g, PA_K1 in *; lia|].
      exists hh.
      split; [rewrite Hbl4; eapply Permutation_trans;
              [apply (Permutation_app_tail [(hh, SRC_FILE_BLOCK)] Hperm)|];
              rewrite <- app_assoc; cbn [app]; apply Permutation_refl|].
      split; [unfold p_psopen, pval; cbn [ms_mem mkst]; split; [exact Hpsf|];
              rewrite <- swZ_sw; exact Hpsw|].
      split; [|cbn [ms_mem mkst]; exact Hsrc4].
      unfold p_psfresh, pval. cbn [ms_mem mkst].
      split; [exact Hz12|]. split; [exact Hz16|]. split; [exact Hz20|].
      unfold p_pspad. cbn [ms_mem mkst].
      intros j Hj. cbn [length] in Hj.
      assert (Hj2 : (j = 0 \/ j = 1)%nat) by lia.
      assert (HA : aview SEGS (w_H W4) mem4 (pPS cx fp + 22 + Z.of_nat j) = Some (nth j [165; 165] 0)).
      { rewrite (K4 PE_CID fp (pPS cx fp + 22 + Z.of_nat j) Hfin
          ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa;
                change (fs_frame_bytes PE_CID) with 128; unfold pPS, PO_PS; lia)
          ltac:(cbv beta; unfold pPS, PO_PS; lia)).
        rewrite HFm2.
        replace (pPS cx fp + 22 + Z.of_nat j) with (pF cx fp + 32 + (22 + Z.of_nat j))
          by (unfold pPS, PO_PS; lia).
        rewrite (Hset (22 + Z.of_nat j) ltac:(lia)).
        destruct Hj2 as [Hq|Hq]; subst j; cbn [nth]; reflexivity. }
      split; [exact (proj1 (val_mem1_of_aview SEGS (w_H W4) mem4 _ _ HA))
             | destruct Hj2 as [Hq|Hq]; subst j; cbn [nth]; lia].
  - (* the file was refused *)
    rewrite goodZ_good in Hbad.
    eapply (NEXT cx fp (k + EV_OPEN) (acc + OPEN_METER MT) ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 (BASE + PP_K2)) mem4 (seg_rom SEGS)) md4 HB).
    + eapply gx_pack0; [exact HJ4 | exact Hag3].
    + rewrite Hfr4. exact Hfrs.
    + exact (mle_station MT _ _ _ _ _ MLAWS Hmo Hmle4).
    + unfold GI_K2. exists bb.
      split; [exact PB2|]. split; [exact Hn26|]. split; [exact EFDS|]. split; [exact EFS|].
      split; [exact RK19|]. split; [exact RK20|]. split; [exact RK23|]. split; [exact RK25|].
      split; [exact (SLOT PS_D (p_d cx) ltac:(unfold PS_D; lia) SD1)|].
      split; [exact (SLOT PS_GLEN (pa_val (A_HI 8)) ltac:(unfold PS_GLEN; lia) SG1)|].
      split; [exact (SLOT PS_PSP (pPS cx fp) ltac:(unfold PS_PSP; lia) SP1)|].
      split; [exact GLOB4|].
      split; [exact GCP4|].
      right. split; [exact Hbad|].
      split; [cbn [ms_regs mkst]; exact Ha0|].
      split; [unfold EV_OPEN, EV_FUZZ_FOPEN; lia|].
      split; [unfold PA_K2r, PA_K1, OPEN_METER; unfold PA_K1 in Hacc; lia|].
      split; [eapply Permutation_trans; [exact Hbl4 | exact Hperm]|].
      split; [unfold p_psnull, pval; cbn [ms_mem mkst]; exact Hps0|].
      cbn [ms_mem mkst]. exact Hsrc4. }
Qed.

End c.
End b.
End a.
