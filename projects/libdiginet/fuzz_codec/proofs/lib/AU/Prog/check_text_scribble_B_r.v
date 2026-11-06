(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 277 of its 306 lines of code are new or changed and 731 lines of the source are left out. *)
(* Segment R of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_R of
   check_text_scribble_B_inv.v, from 0x8403c to `ret` and the contract's post:
     0x8403c-0x84040  want's shadow byte := 0xf8
     0x84044-0x8404c  F[0] := 0x45e0360e (the frame header retired)
     0x84050          beqz s2: not taken, s2 = F >= 4096 (the real-stack exit 0x840d0-0x840ec is not reached)
     0x84054-0x84074  the frame's 8 shadow bytes := 0xf5
     0x84078-0x8407c  ld a0,56(s2); sb zero,0(a0): the flag byte cleared, the frame released (aj_flag_store)
     0x840f0-0x84128  sp = s0 - 128, ra and s0-s10 back from the save area, sp += 128, ret.
   The state at 0x8403c is built over the entry registers (atoms 0..31 the call's entry registers, so the leaf compares
   the callee-saved registers with them): s0 = the entry sp (atom 2), x3, x4, s11 the entry's; every other register r
   in the extra atom 33 + r holding its value at the boundary (s8 = s2 = F shares s2's atom 51); the flag address in
   atom 65. Its regions: the flag byte, the frame's shadow (atom 58 = s9), the frame (atom 51, the flag address at
   F + 56), the save area of the twelve registers below the entry sp (atom 2). The run writes the flag byte, the
   frame's shadow and the frame (fresh for the call state: cw_fresh_frame_j), so the walk's kept invariant and the
   record's 24 bytes carry to the return. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm YF0r.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the extras: register r's value in atom 33 + r, the flag address in atom 65 *)
Definition bsr_xs (regs2 : bvmap 5 word) (FL : Z) : list Z := map (fun r => bv_unsigned (getr regs2 r)) all_regs ++ [FL].
Definition bsr_regs : list sv :=
  [SOff 33 0; SOff 34 0; SOff 35 0; SOff 3 0; SOff 4 0; SOff 38 0; SOff 39 0; SOff 40 0;
   SOff 2 0; SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0;
   SOff 49 0; SOff 50 0; SOff 51 0; SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0; SOff 56 0;
   SOff 51 0; SOff 58 0; SOff 59 0; SOff 27 0; SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0].
Definition bsr_saves : list YP09.chunk :=
  [ YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition bsr_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 0 0 bsr_saves.
Definition bsr_fsh : YP09.region := YP09.mkRegion (Some 58%nat) 0 8 0 8 [].
Definition bsr_rs : smem := [cw_flag_region 65; bsr_fsh; cw_frame_region 51 65 0; bsr_stack].
Definition bsr_G : facts :=
  mkFacts [(51%nat, HPTR 6); (65%nat, HPTR 0); (58%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

Lemma bsr_ew_x : forall regs xs k, (33 <= k)%nat ->
  ew (Ereg regs (cw_extra xs)) k = Z_to_bv 64 (nth (k - 33) xs 0).
Proof.
intros regs xs k Hk. replace k with (33 + (k - 33))%nat at 1 by lia. apply cw_ew_x.
Qed.
Lemma bsr_agree : forall regs xs, env_agree 32 (Ereg regs (cw_extra [])) (Ereg regs (cw_extra xs)).
Proof.
intros regs xs. change (cw_extra xs) with (cw_extra [] ++ map (Z_to_bv 64) xs).
apply env_agree_Ereg_app. cbn. lia.
Qed.
(* the register of the boundary in its extra atom *)
Ltac bsr_x := rewrite bsr_ew_x by lia; unfold bsr_xs; cbn [Nat.sub nth app map all_regs];
  first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned].
Lemma bsr_regs_ok : forall (regs0 regs2 : bvmap 5 word) FL,
  getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 -> getr regs2 8 = getr regs0 2 ->
  getr regs2 24 = getr regs2 18 -> getr regs2 27 = getr regs0 27 ->
  regs_ok (Ereg regs0 (cw_extra (bsr_xs regs2 FL))) bsr_regs regs2.
Proof.
intros regs0 regs2 FL H3 H4 H8 H24 H27.
assert (A3 : ew (Ereg regs0 (cw_extra (bsr_xs regs2 FL))) 3 = getr regs0 3) by exact (ew_Ereg_nat regs0 _ 3 3%bv eq_refl).
assert (A4 : ew (Ereg regs0 (cw_extra (bsr_xs regs2 FL))) 4 = getr regs0 4) by exact (ew_Ereg_nat regs0 _ 4 4%bv eq_refl).
assert (A2 : ew (Ereg regs0 (cw_extra (bsr_xs regs2 FL))) 2 = getr regs0 2) by exact (ew_Ereg_nat regs0 _ 2 2%bv eq_refl).
assert (A27 : ew (Ereg regs0 (cw_extra (bsr_xs regs2 FL))) 27 = getr regs0 27)
  by exact (ew_Ereg_nat regs0 _ 27 27%bv eq_refl).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [idtac|]).
all: try (destruct Hr).
all: lazymatch goal with |- _ = sv_denot ?Ev ?e => let e' := eval vm_compute in e in change e with e' end;
  try rewrite sv_denot_SOff0.
all: first [ reflexivity | rewrite A3; exact H3 | rewrite A4; exact H4 | rewrite A2; exact H8 | rewrite A27; exact H27
           | bsr_x | rewrite H24; bsr_x ].
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

Theorem bs_r_holds : bs_seg_R B MT.
Proof.
unfold bs_seg_R. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HRES).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & V1 & V8 & V9 & V18 & V19 &
  V20 & V21 & V22 & V23 & V24 & V25 & V26 & Hfl & Hsh).
pose proof Hpre as (HE & _ & _ & _ & _ & _ & (Hch0 & Hchn & Hchtd & _) & _ & _ & _ & Hn & _).
pose proof HE as (HJc & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
destruct (bs_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _).
pose proof (proj1 HJc) as HARc.
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin) as (_ & _ & HFb & HFs).
destruct (FFL _ _ _ _ _ 0 pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL0 & _ & HFLc)).
rewrite Efa in HFb, HFs. rewrite Efl in HFLp, HFLo, HFL0, HFLc.
change (fs_frame_bytes 0) with 64 in HFb, HFs. change (64 / 8) with 8 in HFs.
fold (bs_F g pos) in HFb, HFs. fold (bs_FL g pos) in HFLp, HFLo, HFL0, HFLc.
assert (HSB : shadow_addr (bs_F g pos) = SB + bs_F g pos / 8) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
rewrite HSB in HFs.
assert (HF8 : 0 <= bs_F g pos / 8 <= bs_F g pos) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold TB_check_text_scribble, ESTACK in Hceil, Hwin, H46.
assert (R8' : getr regs2 8 = getr (bs_regs g) 2)
  by (rewrite R8; unfold w64, bs_sp, spZ; apply Z_to_bv_bv_unsigned).
assert (R24' : getr regs2 24 = getr regs2 18) by (rewrite R24, R18; reflexivity).
(* the state at 0x8403c *)
assert (E51 : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 51 = Z_to_bv 64 (bs_F g pos))
  by (rewrite (eq_trans (ltac:(bsr_x) : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 51 = getr regs2 18) R18);
      reflexivity).
assert (E58 : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 58 = Z_to_bv 64 (SB + bs_F g pos / 8))
  by (rewrite (eq_trans (ltac:(bsr_x) : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 58 = getr regs2 25) R25);
      reflexivity).
assert (E65 : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 65 = Z_to_bv 64 (bs_FL g pos))
  by (rewrite bsr_ew_x by lia; reflexivity).
assert (E2 : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 2 = Z_to_bv 64 (bs_sp g))
  by (rewrite (ew_Ereg_nat (bs_regs g) _ 2 2%bv eq_refl); unfold bs_sp, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (HS : st_ok tfibsegs (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos))))
  (mkSS PC_R bsr_regs bsr_rs None bsr_G) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_R) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply cw_st_ok_at.
  - exact (bsr_regs_ok (bs_regs g) regs2 (bs_FL g pos) R3 R4 R8' R24' R27).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (cw_flag_region_ok B FFL _ 65 ly2 S2 W2 mem2 md2 0 pos HAR2 Hin). rewrite E65, Efl. reflexivity.
    + unfold region_ok, bsr_fsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E58, unsigned_lit_small by (unfold SB; lia).
      split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable tfibsegs). exact (proj1 (HFs oo ltac:(lia))).
    + apply (cw_frame_region_ok B LAWS FFL _ 51 65 ly2 S2 W2 mem2 md2 0 pos HAR2 Hin);
        [rewrite E51, Efa; reflexivity | rewrite E65, Efl; reflexivity |].
      rewrite Efa, Efl. change (fs_frame_bytes 0) with 64.
      replace (frame_addr (bs_lyc g) 0 pos + 64 - 8) with (bs_F g pos + 56) by (unfold bs_F; lia). exact Hfl.
    + unfold region_ok, bsr_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      unfold bsr_saves.
      repeat (apply Forall_cons; [|]); [..|apply Forall_nil].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-96) 8 (SOff 26 0) (bv_unsigned (getr (bs_regs g) 26%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 26 26%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 26%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -96) with (bs_sp g - 96) by lia; exact V26 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-88) 8 (SOff 25 0) (bv_unsigned (getr (bs_regs g) 25%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 25 25%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 25%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -88) with (bs_sp g - 88) by lia; exact V25 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-80) 8 (SOff 24 0) (bv_unsigned (getr (bs_regs g) 24%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 24 24%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 24%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -80) with (bs_sp g - 80) by lia; exact V24 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-72) 8 (SOff 23 0) (bv_unsigned (getr (bs_regs g) 23%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 23 23%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 23%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -72) with (bs_sp g - 72) by lia; exact V23 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-64) 8 (SOff 22 0) (bv_unsigned (getr (bs_regs g) 22%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 22 22%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 22%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -64) with (bs_sp g - 64) by lia; exact V22 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-56) 8 (SOff 21 0) (bv_unsigned (getr (bs_regs g) 21%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 21 21%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 21%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -56) with (bs_sp g - 56) by lia; exact V21 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-48) 8 (SOff 20 0) (bv_unsigned (getr (bs_regs g) 20%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 20 20%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 20%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -48) with (bs_sp g - 48) by lia; exact V20 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-40) 8 (SOff 19 0) (bv_unsigned (getr (bs_regs g) 19%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 19 19%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 19%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -40) with (bs_sp g - 40) by lia; exact V19 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-32) 8 (SOff 18 0) (bv_unsigned (getr (bs_regs g) 18%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 18 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 18%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -32) with (bs_sp g - 32) by lia; exact V18 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-24) 8 (SOff 9 0) (bv_unsigned (getr (bs_regs g) 9%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 9%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -24) with (bs_sp g - 24) by lia; exact V9 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-16) 8 (SOff 8 0) (bv_unsigned (getr (bs_regs g) 8%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 8 8%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 8%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -16) with (bs_sp g - 16) by lia; exact V8 ].
      * apply (chunk_ok_val tfibsegs _ _ (bs_sp g) (-8) 8 (SOff 1 0) (bv_unsigned (getr (bs_regs g) 1%bv)));
        [ rewrite sv_denot_SOff0, (ew_Ereg_nat (bs_regs g) _ 1 1%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (bv_unsigned_in_range _ (getr (bs_regs g) 1%bv)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          cbn; lia
        | cbn; lia
        | replace (bs_sp g + -8) with (bs_sp g - 8) by lia; exact V1 ].
  - pose proof (Z.mul_div_le (bs_F g pos) 8 ltac:(lia)) as HFd.
    pose proof (cw_flag_apart B _ _ (bs_FL g pos) (SB + bs_F g pos / 8) (SB + bs_F g pos / 8 + 8) HFLo
      ltac:(intros a Ha; replace a with (SB + bs_F g pos / 8 + (a - (SB + bs_F g pos / 8))) by lia;
            exact (proj2 (HFs (a - (SB + bs_F g pos / 8)) ltac:(lia))))) as D1.
    pose proof (cw_flag_apart B _ _ (bs_FL g pos) (bs_F g pos) (bs_F g pos + 64) HFLo
      ltac:(intros a Ha; exact (proj2 (HFb a Ha)))) as D2.
    apply pairwise_disjoint_of_extents. unfold bsr_rs, cw_flag_region, bsr_fsh, cw_frame_region, bsr_stack, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 0) with 64.
    rewrite E65, E58, E51, E2, !unsigned_lit_small by (unfold SB in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SB in *. repeat split; lia.
  - split; [|split; exact I].
    destruct (cw_frame_afacts B LAWS _ 51 65 58 ly2 S2 W2 mem2 md2 0 pos FFL HAR2 Hin
      ltac:(rewrite E51, Efa; reflexivity) ltac:(rewrite E65, Efl; reflexivity)
      ltac:(rewrite E58, Efa; fold (bs_F g pos); rewrite HSB; reflexivity)) as (A51 & A65 & A58).
    cbn [f_atoms atoms_ok bsr_G]. split; [exact A51|]. split; [exact A65|]. split; [exact A58|].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia]. }
assert (HAE : env_agree 32 (Ereg (bs_regs g) (cw_extra [])) (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))))
  by apply bsr_agree.
assert (E1 : ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 1 = getr (bs_regs g) 1)
  by exact (ew_Ereg_nat (bs_regs g) _ 1 1%bv eq_refl).
assert (U65 : bv_unsigned (ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 65) = flag_addr ly2 0 pos)
  by (rewrite E65, unsigned_lit_small by lia; rewrite Efl; reflexivity).
assert (U58 : bv_unsigned (ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 58) =
  shadow_addr (frame_addr ly2 0 pos))
  by (rewrite E58, unsigned_lit_small by (unfold SB; lia); rewrite Efa; fold (bs_F g pos); rewrite HSB; reflexivity).
assert (U51 : bv_unsigned (ew (Ereg (bs_regs g) (cw_extra (bsr_xs regs2 (bs_FL g pos)))) 51) = frame_addr ly2 0 pos)
  by (rewrite E51, unsigned_lit_small by lia; rewrite Efa; reflexivity).
unfold bs_post, cfg_at. change (w64 PC_R) with (Z_to_bv 64 PC_R).
pose proof HJ as HJ3p.
pose proof (ffl_U_of_A B FFL) as FFLU.
aj_run_flag_sh tfibtbl_lib_ok HS HJ;
[ lia
| eapply (cw_awrf_flag_front _ _ _ _ _ _ _ _ _ _ 65%nat); [reflexivity | exact U65 | cbn; lia | cbn; lia |];
  cw_awrA;
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 pos 58%nat);
    [reflexivity | exact U58 | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0 / 8) with 8; lia |];
  eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 pos 51%nat);
    [reflexivity | exact U51 | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0) with 64; lia |];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil
| flag0 E65 (Efl 0 pos)
| ].
clear FFLU. cw_ajA HJ. cw_norm_model.
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ mem2) (mrestrict _ ?m2) |- _ =>
  assert (HXc : forall a, in_wrange Ev rs a -> cw_fresh B (bs_lyc g) (bs_Sc g) a) end.
{ (* every byte the release run wrote: the flag byte, the frame's shadow, the frame (all fresh) *)
  intros y (r & Hr & Hb).
  lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U65, ?U58, ?U51 in Hb;
    rewrite ?Efa, ?Efl in Hb; [| | | lia];
    (eapply (cw_fresh_frame_j B LAWS FFL); [exact HJc | exact HJ3p | exact HP |]);
    unfold frame_rng, in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64.
  - right; right; lia.
  - right; left; lia.
  - left; lia. }
(* the kept invariant at the return *)
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ mem2) (mrestrict _ ?m2) |- _ =>
  assert (KK : tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 m2 (bs_sp g)
    (bs_wr g)) end.
{ lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ mem2) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  apply (cw_kept_step B LAWS TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) W2 mem2 m2
    (bs_sp g) (bs_wr g) (in_wrange Ev rs));
  [ unfold TB_check_text_scribble, ESTACK; lia | exact HARc | exact HK
  | intros y Hy Hyx; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 y)); [reflexivity|];
    rewrite unsigned_lit_small by exact Hy; exact Hyx
  | intros y Hyx; right; right; exact (HXc y Hyx)
  | intros y Hp; eapply apresent_grows; [exact HG | exact Hp] ] end. }
(* the record's 24 bytes are not written by the run *)
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ mem2) (mrestrict _ ?m2) |- _ =>
  assert (HRES2 : garr8 tfibsegs (mrestrict (w_H W2) m2) (bs_ch g) (scribble_bytes (bs_tb g) (bs_n g))) end.
{ lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ mem2) (mrestrict _ ?m2) |- _ =>
  intros j Hj; destruct (HRES j Hj) as (Hv & Hb); split; [|exact Hb];
  apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 m2 _ 1 _); [|exact Hv];
  intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
  assert (Hxo : bs_ch g <= x < bs_ch g + 24)
    by (unfold scribble_bytes, owed_scribble_text_spec in Hj; rewrite length_app, repeat_length, bsf_owe_len in Hj; lia);
  pose proof (cj_dst_byte tfibsegs B LAWS (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) (bs_ch g) 24 x HARc Hchtd
    Hxo) as Hcx;
  unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 x)); [reflexivity|];
  rewrite unsigned_lit_small by lia;
  intros Hw; destruct (HXc x Hw) as (_ & _ & Hfb & Hff);
  destruct (Hchtd x Hxo) as [(bb & m & Hinb & Hrb) | (cid & ps & Hinf & Hrf)];
  [ exact (Hfb bb m (x - bb) Hinb ltac:(lia) ltac:(lia)) | exact (proj1 (Hff cid ps Hinf) Hrf) ] end. }
cw_frame_leaf ltac:(idtac; exact KK) ltac:(idtac; exact HRES2).
Qed.
End s.
