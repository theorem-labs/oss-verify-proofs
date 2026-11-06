(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfg.v, with its module paths and module names changed; 398 of its 428 lines of code are new or changed and 260 lines of the source are left out. *)
(* diginet_counter_text in image A (fuzz_codec.asan, 0x86120): the segment X of
   lib/A/Prog/diginet_counter_text_A_inv.v -- from the exit 0x864c0 to the `ret` at 0x865bc and on to the
   contract's post (ct_seg_X).

   The code (listing 0x864c0 .. 0x865bc):
     0x864c0-0x864d4  li a1,-8; sb a1 into the shadow bytes 11, 4, 8, 9, 10 of the frame (0xf8);
     0x864d8-0x864e4  a1 := 0x45e0360e; a2 := 24(s1) = F; sd a1,0(a2): F[0];
     0x864e8-0x864ec  a2 := 16(s1) = F; beqz a2: decided (4096 <= F), so 0x86540..0x8657c is not reached;
     0x864f0-0x86530  li a1,-11; the sixteen shadow bytes of the frame := 0xf5;
     0x86534-0x86538  a1 := 120(a2) = FL; sb zero,0(a1): the flag byte, which releases the frame;
     0x8653c          j 0x86580;
     0x86580-0x865bc  sp := s0 - 160; the thirteen restores from entry sp - 8 .. entry sp - 104; sp += 160; ret.

   One run through ACem's aj_run_flag_sh (the flag-byte store takes the journal from own (1, pos) :: own to own
   and the state to stack_free_state 1 pos), then CPgWalkFrame's cw_frame_leaf.

   The symbolic state at 0x864c0 is built over the ENTRY registers (atoms 0..31 = cg_regs g), so that the
   epilogue's restores give the leaf's register clause: atom 33 = F, atom 34 = FL, atom 35 + i = the boundary
   value of register i. Registers 3, 4 and 8 keep the entry atoms 3, 4 and 2 (gp and tp are never written, s0 is
   the entry sp), so every callee-saved register ends at its entry atom. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_text_A_inv.
(* DgnLib has another `st_ok`: take YP0l's back. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the spec's second loop writes all eight digits unless it returns E_RANGE ---- *)
Lemma ctx_ct2_len : forall k n s dot i seg d,
  fst (fst (ct2_go n s dot i k seg d)) = 0 ->
  length (snd (fst (ct2_go n s dot i k seg d))) = (length seg + k)%nat.
Proof.
induction k as [|k IH]; intros n s dot i seg d H; cbn [ct2_go] in H |- *.
- rewrite Nat.add_0_r. reflexivity.
- destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0))%bool.
  + destruct (i =? 7).
    * cbn [fst] in H. unfold E_RANGE in H. lia.
    * rewrite (IH n s dot (i + 1) (seg ++ [if i - (8 - n) <? 0 then 0 else nth (Z.to_nat (i - (8 - n))) s 0])
        (Z.lor d (2 ^ i)) H). rewrite length_app. cbn [length]. lia.
  + rewrite (IH n s dot (i + 1) (seg ++ [if i - (8 - n) <? 0 then 0 else nth (Z.to_nat (i - (8 - n))) s 0]) d H).
    rewrite length_app. cbn [length]. lia.
Qed.
Lemma ctx_spec_len : forall t res seg d, counter_text_spec t = (res, seg, d) -> res = 0 -> length seg = 8%nat.
Proof.
intros t res seg d H Hr. unfold counter_text_spec in H.
destruct (ct1_lib t 0 [] (repeat 0 8)) as [[[n s] dot]|].
- unfold ct2 in H. pose proof (ctx_ct2_len 8 n s dot 0 [] 0) as Hl. rewrite H in Hl.
  cbn [fst snd length] in Hl. exact (Hl Hr).
- injection H as H1 H2 _. subst res seg. unfold E_RANGE in Hr. lia.
Qed.

(* ---- the symbolic state at 0x864c0 --------------------------------------------------------------------------- *)
(* The boundary values of the 32 registers; the atoms 35 .. 66 hold them. *)
Definition ctx_regs32 (rg : bvmap 5 word) : list Z :=
[bv_unsigned (getr rg (0%bv)); bv_unsigned (getr rg (1%bv)); bv_unsigned (getr rg (2%bv));
 bv_unsigned (getr rg (3%bv)); bv_unsigned (getr rg (4%bv)); bv_unsigned (getr rg (5%bv));
 bv_unsigned (getr rg (6%bv)); bv_unsigned (getr rg (7%bv)); bv_unsigned (getr rg (8%bv));
 bv_unsigned (getr rg (9%bv)); bv_unsigned (getr rg (10%bv)); bv_unsigned (getr rg (11%bv));
 bv_unsigned (getr rg (12%bv)); bv_unsigned (getr rg (13%bv)); bv_unsigned (getr rg (14%bv));
 bv_unsigned (getr rg (15%bv)); bv_unsigned (getr rg (16%bv)); bv_unsigned (getr rg (17%bv));
 bv_unsigned (getr rg (18%bv)); bv_unsigned (getr rg (19%bv)); bv_unsigned (getr rg (20%bv));
 bv_unsigned (getr rg (21%bv)); bv_unsigned (getr rg (22%bv)); bv_unsigned (getr rg (23%bv));
 bv_unsigned (getr rg (24%bv)); bv_unsigned (getr rg (25%bv)); bv_unsigned (getr rg (26%bv));
 bv_unsigned (getr rg (27%bv)); bv_unsigned (getr rg (28%bv)); bv_unsigned (getr rg (29%bv));
 bv_unsigned (getr rg (30%bv)); bv_unsigned (getr rg (31%bv))].
Definition ctx_xs (F FL : Z) (rg : bvmap 5 word) : list Z := F :: FL :: ctx_regs32 rg.
(* x0; x3 / x4 the entry gp / tp (atoms 3 / 4); x8 = s0 the entry sp (atom 2); every other register its own
   atom 35 + i. s1 = x9 is atom 44 (the spills), s7 = x23 is atom 58 (the frame's shadow). *)
Definition ctx_sr : list sv :=
[SLit 0; SOff 36 0; SOff 37 0; SOff 3 0; SOff 4 0; SOff 40 0; SOff 41 0; SOff 42 0;
 SOff 2 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0;
 SOff 51 0; SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0; SOff 56 0; SOff 57 0; SOff 58 0;
 SOff 59 0; SOff 60 0; SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0; SOff 65 0; SOff 66 0].
(* The frame's 16 shadow bytes at s7; the two spills of F at 16(s1) and 24(s1); the thirteen saves at the entry sp. *)
Definition ctx_rshadow : YP09.region := YP09.mkRegion (Some 58%nat) 0 16 0 16 [].
Definition ctx_rspill : YP09.region := YP09.mkRegion (Some 44%nat) 16 32 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition ctx_rsave : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 0 0
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
(* The flag byte comes first: the release run's write premise reads it off the head (cw_awrf_flag_front). *)
Definition ctx_rs : smem := [cw_flag_region 34; cw_frame_region 33 34 1; ctx_rshadow; ctx_rspill; ctx_rsave].
Definition ctx_AF : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (33%nat, HPTR 6); (34%nat, HPTR 0);
 (44%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (58%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3)].
Definition ctx_ss0 : sstate := mkSS PC_X ctx_sr ctx_rs None (mkFacts ctx_AF [] []).

(* Where the run may write: the flag byte, the frame, the frame's shadow (the spills and the saves are read-only). *)
Lemma ctx_wrange : forall E a, in_wrange E ctx_rs a ->
  bv_unsigned (ew E 34) <= a < bv_unsigned (ew E 34) + 1 \/
  bv_unsigned (ew E 33) <= a < bv_unsigned (ew E 33) + 128 \/
  bv_unsigned (ew E 58) <= a < bv_unsigned (ew E 58) + 16.
Proof.
intros E a (r & Hr & Ha).
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.
Lemma ctx_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma ctx_mbyte_kept : forall E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma ctx_val_mem_kept : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hk Hv k Hkn. rewrite (Hk k Hkn). exact (Hv k Hkn). Qed.

(* one case of regs_ok at the start state; rg0 is the entry register file *)
Ltac ctx_reg_case rg0 :=
lazymatch goal with |- _ = sv_denot _ (sr_get ?sr ?r2) =>
  let v := eval vm_compute in (sr_get sr r2) in change (sr_get sr r2) with v end;
first
[ cbn [sv_denot]; rewrite getr_zero; reflexivity
| rewrite sv_denot_SOff0;
  first
  [ lazymatch goal with |- _ = ew _ ?n =>
      let j := eval vm_compute in (n - 33)%nat in change n with (33 + j)%nat end;
    rewrite cw_ew_x; cbn [nth ctx_xs ctx_regs32]; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite (cw_ew_reg rg0 _ 3%nat (3%bv) eq_refl); assumption
  | rewrite (cw_ew_reg rg0 _ 4%nat (4%bv) eq_refl); assumption
  | rewrite (cw_ew_reg rg0 _ 2%nat (2%bv) eq_refl);
    lazymatch goal with H8 : getr _ (8%bv) = _ |- _ => rewrite H8 end;
    unfold w64, cg_sp, spZ; apply Z_to_bv_bv_unsigned ] ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.

Theorem ct_x_holds : ct_seg_X B MT RLO RHI SEG7TBL.
Proof.
unfold ct_seg_X. intros g pos W2 c2 Hpre Hnow Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ & HK & HP3 & Hnin & Hio & HM3 & HC & HPX).
destruct HC as (R8 & R2 & R9 & R3 & R4 & R23 & R25 & Vra & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 &
  V25 & V26 & V27 & Vdt & VF16 & VF24 & Hflagw & Hfsh).
destruct Hpre as (HE & _ & _ & _ & Hsgdst & _ & _ & _ & Hdtdst & _).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
unfold T_counter_text in *.
pose proof (cw_entry_stack B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
  (cg_own g) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) (cg_k g) (cg_regs g) (192 + ESTACK) HE
  ltac:(unfold ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hprs).
assert (Hes : ESTACK = 4096) by reflexivity.
change (spZ (cg_regs g)) with (cg_sp g) in Hceil, H47, H46, Hprs, Hal16, Hwin, Hwhi.
(* the layouts agree on the side stack *)
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
pose proof HJ0 as (HARc & Hlyc & _ & _ & _ & Hfrsc & _).
assert (EFA : forall c p, frame_addr ly2 c p = frame_addr (cg_lyc g) c p).
{ intros c p. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & Ex1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ex2 & _).
  rewrite Ex1, Ex2. reflexivity. }
assert (EFL : forall c p, flag_addr ly2 c p = flag_addr (cg_lyc g) c p).
{ intros c p. unfold flag_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & Ex1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ex2 & _).
  rewrite Ex1, Ex2. reflexivity. }
assert (Hin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
(* the frame, its shadow and its flag byte *)
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin2) as (HF0 & HFc & HFapp).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 1 pos HAR2 Hin2) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin2) as (_ & _ & HFp & HSp).
destruct (FFL ly2 S2 W2 mem2 md2 1 pos HAR2 Hin2) as (HLp & HLo & (HLapp & HLimg) & (HL0 & _ & HLc)).
change (fs_frame_bytes 1) with 128 in HFc, HFapp, HFp, HSp.
change (128 / 8) with 16 in HSp.
set (F := frame_addr ly2 1 pos) in *. set (FL := flag_addr ly2 1 pos) in *.
assert (EFg : F = cg_F g pos) by (unfold F, cg_F; apply EFA).
assert (ELg : FL = cg_FL g pos) by (unfold FL, cg_FL; apply EFL).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite (Z.div_mod F 64) at 1 by lia. rewrite HF64, Z.add_0_r.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; lia).
(* the realigned sp *)
destruct (sp1_facts (cg_sp g - 160) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & _).
change (32 * ((cg_sp g - 160) / 32)) with (cg_sp1 g) in Hsp1r, Hsp1al.
(* ---- the start state ---- *)
assert (E2 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 2 = getr (cg_regs g) (2%bv))
  by (apply (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 2%nat (2%bv)); reflexivity).
assert (E33 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 33 = Z_to_bv 64 F)
  by (exact (cw_ew_x (cg_regs g) (ctx_xs F FL regs2) 0%nat)).
assert (E34 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 34 = Z_to_bv 64 FL)
  by (exact (cw_ew_x (cg_regs g) (ctx_xs F FL regs2) 1%nat)).
assert (E44 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 44 = Z_to_bv 64 (cg_sp1 g)).
{ change 44%nat with (33 + 11)%nat. rewrite (cw_ew_x (cg_regs g) (ctx_xs F FL regs2) 11%nat).
  cbn [nth ctx_xs ctx_regs32]. rewrite R9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (E58 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 58 = Z_to_bv 64 (shadow_addr F)).
{ change 58%nat with (33 + 25)%nat. rewrite (cw_ew_x (cg_regs g) (ctx_xs F FL regs2) 25%nat).
  cbn [nth ctx_xs ctx_regs32]. rewrite R23, <- EFg. unfold w64.
  rewrite unsigned_lit_small by (unfold SB; lia).
  unfold shadow_addr. rewrite SB_SHADOW_OFF. reflexivity. }
assert (U2 : bv_unsigned (ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 2) = cg_sp g)
  by (rewrite E2; reflexivity).
assert (U33 : bv_unsigned (ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 33) = F)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 34) = FL)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 44) = cg_sp1 g)
  by (rewrite E44; apply unsigned_lit_small; lia).
assert (U58 : bv_unsigned (ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 58) = shadow_addr F)
  by (rewrite E58; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B ly2 S2 a)
  by (intros a Ha; exact (proj2 (HFp a Ha))).
assert (HnoS : forall a, shadow_addr F <= a < shadow_addr F + 16 -> ~ aowned B ly2 S2 a).
{ intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
  exact (proj2 (HSp (a - shadow_addr F) ltac:(lia))). }
assert (HS : st_ok tfibsegs (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) ctx_ss0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_X) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ctx_ss0. apply cw_st_ok_at.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [ctx_reg_case (cg_regs g) | ]). destruct Hr.
  - vm_compute. reflexivity.
  - unfold ctx_rs. repeat apply Forall_cons; try apply Forall_nil.
    + (* the flag byte *) eapply cw_flag_region_ok; eassumption.
    + (* the frame *)
      eapply cw_frame_region_ok; try eassumption.
      change (fs_frame_bytes 1) with 128.
      change (frame_addr ly2 1 pos) with F. change (flag_addr ly2 1 pos) with FL.
      replace (F + 128 - 8) with (F + 120) by lia.
      rewrite EFg, ELg. exact Hflagw.
    + (* the frame's shadow *)
      unfold region_ok, ctx_rshadow.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U58. split; [unfold shadow_addr, SHADOW_OFF; lia|].
      split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (HSp o ltac:(lia))).
    + (* the two spills of F *)
      unfold region_ok, ctx_rspill.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U44. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp1 g) 16 8 (SOff 33 0) F);
        [rewrite sv_denot_SOff0, E33; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
        rewrite EFg. exact VF16.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp1 g) 24 8 (SOff 33 0) F);
        [rewrite sv_denot_SOff0, E33; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
        rewrite EFg. exact VF24.
    + (* the thirteen saves *)
      unfold region_ok, ctx_rsave.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat (apply Forall_cons); [ | | | | | | | | | | | | | apply Forall_nil ].
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-8) 8 (SOff 1 0) (raZ (cg_regs g)));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 1%nat (1%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -8) with (cg_sp g - 8) by lia. exact Vra.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-16) 8 (SOff 8 0) (bv_unsigned (getr (cg_regs g) (8%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 8%nat (8%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -16) with (cg_sp g - 16) by lia. exact V8.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-24) 8 (SOff 9 0) (bv_unsigned (getr (cg_regs g) (9%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 9%nat (9%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -24) with (cg_sp g - 24) by lia. exact V9.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-32) 8 (SOff 18 0) (bv_unsigned (getr (cg_regs g) (18%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 18%nat (18%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -32) with (cg_sp g - 32) by lia. exact V18.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-40) 8 (SOff 19 0) (bv_unsigned (getr (cg_regs g) (19%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 19%nat (19%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -40) with (cg_sp g - 40) by lia. exact V19.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-48) 8 (SOff 20 0) (bv_unsigned (getr (cg_regs g) (20%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 20%nat (20%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -48) with (cg_sp g - 48) by lia. exact V20.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-56) 8 (SOff 21 0) (bv_unsigned (getr (cg_regs g) (21%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 21%nat (21%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -56) with (cg_sp g - 56) by lia. exact V21.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-64) 8 (SOff 22 0) (bv_unsigned (getr (cg_regs g) (22%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 22%nat (22%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -64) with (cg_sp g - 64) by lia. exact V22.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-72) 8 (SOff 23 0) (bv_unsigned (getr (cg_regs g) (23%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 23%nat (23%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -72) with (cg_sp g - 72) by lia. exact V23.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-80) 8 (SOff 24 0) (bv_unsigned (getr (cg_regs g) (24%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 24%nat (24%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -80) with (cg_sp g - 80) by lia. exact V24.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-88) 8 (SOff 25 0) (bv_unsigned (getr (cg_regs g) (25%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 25%nat (25%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -88) with (cg_sp g - 88) by lia. exact V25.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-96) 8 (SOff 26 0) (bv_unsigned (getr (cg_regs g) (26%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 26%nat (26%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -96) with (cg_sp g - 96) by lia. exact V26.
      * apply (chunk_ok_val tfibsegs _ _ (cg_sp g) (-104) 8 (SOff 27 0) (bv_unsigned (getr (cg_regs g) (27%bv))));
        [rewrite sv_denot_SOff0, (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 27%nat (27%bv) eq_refl);
         symmetry; apply Z_to_bv_bv_unsigned
        | change (8 * Z.of_N 8) with 64; apply ctx_u64 | cbn; lia |].
        replace (cg_sp g + -104) with (cg_sp g - 104) by lia. exact V27.
  - apply pairwise_disjoint_of_extents.
    unfold ctx_rs, cw_flag_region, cw_frame_region, ctx_rshadow, ctx_rspill, ctx_rsave, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128.
    rewrite U2, U33, U34, U44, U58.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (HFS : F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F).
    { unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *.
      destruct HFapp as (_ & [Hlo | (Hhi & _)]); [left; lia | right; lia]. }
    assert (HFLf : F + 128 <= FL \/ FL + 1 <= F)
      by (destruct (cw_flag_apart B ly2 S2 FL F (F + 128) HLo HnoF) as [Hx | Hx]; [left | right]; lia).
    assert (HFLs : shadow_addr F + 16 <= FL \/ FL + 1 <= shadow_addr F)
      by (destruct (cw_flag_apart B ly2 S2 FL (shadow_addr F) (shadow_addr F + 16) HLo HnoS) as [Hx | Hx];
          [left | right]; lia).
    unfold shadow_addr, SHADOW_OFF in *.
    repeat split; lia.
  - split; [|split; exact I]. unfold ctx_AF. cbn [f_atoms atoms_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U33, U34, U44, U58.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
    rewrite Z.pow_0_r, Z.mod_1_r.
    assert (HS8 : shadow_addr F mod 8 = 0).
    { unfold shadow_addr, SHADOW_OFF. rewrite HF8.
      replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z_mod_mult. }
    unfold shadow_addr, SHADOW_OFF, SB in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try lia. }
assert (HAE : env_agree 32 (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2)))
  (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2)))) by apply env_agree_refl.
assert (E1 : ew (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) 1 = getr (cg_regs g) (1%bv))
  by (apply (cw_ew_reg (cg_regs g) (ctx_xs F FL regs2) 1%nat (1%bv)); reflexivity).
(* the run tactic renames HJ in place: keep the boundary journal as HJB *)
pose proof HJ as HJB.
(* ---- the run: the release and the epilogue, up to the ret ---- *)
subst c2. unfold cfg_at, w64.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_X) mem2 (seg_rom tfibsegs))) in HJ.
aj_run_flag_sh tfibtbl_lib_ok HS HJ.
- lia.
- (* every writable byte is the walk's frame, its shadow, or the flag byte *)
  change (ss_mem ctx_ss0) with ctx_rs. unfold ctx_rs.
  eapply (cw_awrf_flag_front _ _ _ _ _ _ _ _ _ _ 34%nat FL);
  [reflexivity | exact U34 | cbn; lia | cbn; lia |].
  eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 1 pos 33%nat);
  [reflexivity | exact U33 | left; reflexivity | cbn; lia
  | cbn; change (fs_frame_bytes 1) with 128; lia |].
  eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 1 pos 58%nat);
  [reflexivity | exact U58 | left; reflexivity | cbn; lia
  | cbn; change (fs_frame_bytes 1 / 8) with 16; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
- (* the flag byte is 0 in the state the run reaches *)
  intros msr HSr. rewrite EFL.
  pose proof (st_ok_region_nth (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) _ msr 0%nat _ HSr eq_refl) as HR.
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) (ms_mem msr) n
      (flag_addr (cg_lyc g) 1 pos) cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
      ltac:(rewrite U34; exact ELg) ltac:(left; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0.
  cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0.
- (* the leaf *)
  (* every byte the run wrote is fresh for the call state *)
  assert (HFRESH : forall a, in_wrange (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) (ss_mem ctx_ss0) a ->
    cw_fresh B (cg_lyc g) (cg_Sc g) a).
  { intros a Ha. change (ss_mem ctx_ss0) with ctx_rs in Ha.
    destruct (ctx_wrange _ a Ha) as [Hx | [Hx | Hx]];
    [ rewrite U34 in Hx | rewrite U33 in Hx | rewrite U58 in Hx ];
    (eapply (cw_fresh_frame_j B LAWS FFL); [exact HJ0 | exact HJB | exact HP3 |]).
    - right; right. rewrite <- EFL. unfold FL in Hx. lia.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EFA.
      change (fs_frame_bytes 1) with 128. unfold F in Hx. lia.
    - right; left. unfold in_zr. cbn [fst snd]. rewrite <- EFA.
      change (fs_frame_bytes 1 / 8) with 16. unfold F, shadow_addr in Hx. unfold shadow_addr. lia. }
  (* a byte of an object the call may write is not one of them *)
  assert (HNOTW : forall q n a, tdst_ok B (cg_lyc g) (cg_Sc g) q n -> q <= a < q + n ->
    ~ in_wrange (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) (ss_mem ctx_ss0) a).
  { intros q n a Hd Hq Hw. destruct (HFRESH a Hw) as (_ & _ & Hb & Hfr).
    destruct (Hd a Hq) as [(b & m & Hin & Hr) | (cid & p & Hin & Hr)].
    - apply (Hb b m (a - b) Hin ltac:(lia)). lia.
    - exact (proj1 (Hfr cid p Hin) Hr). }
  assert (KK : tcj_kept tfibsegs B (192 + ESTACK) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 (ms_mem ms)
    (cg_sp g) (ct_wr g)).
  { apply (cw_kept_step B LAWS (192 + ESTACK) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) W2 mem2
      (ms_mem ms) (cg_sp g) (ct_wr g)
      (in_wrange (Ereg (cg_regs g) (cw_extra (ctx_xs F FL regs2))) (ss_mem ctx_ss0)));
    [ lia | exact HARc | exact HK | | | ].
    - intros a Ha Hx. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by exact Ha. exact Hx.
    - intros a Ha. right; right. exact (HFRESH a Ha).
    - intros a Hp. eapply apresent_grows; [exact HG | exact Hp]. }
  cw_frame_leaf ltac:(idtac; exact KK) ltac:(idtac).
  (* the result: a0, and the bytes of seg and dt, which the run did not touch *)
  cbv beta. unfold P_X in HPX. cbv beta in HPX. unfold ct_res in HPX |- *.
  destruct (counter_text_spec (cg_tb g)) as [[res sres] dres] eqn:Espec.
  destruct HPX as (Hr10 & Hzero & Hnz).
  assert (HSEGK : forall a, cg_sg g <= a < cg_sg g + 8 ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a).
  { intros a Ha. apply (ctx_mbyte_kept _ (ss_mem ctx_ss0) _ _ a HFr).
    - destruct Hsgdst as (Hq0 & Hq63 & _). lia.
    - apply (HNOTW (cg_sg g) 8 a); [exact (proj1 (proj2 (proj2 Hsgdst))) | lia]. }
  assert (HDTK : forall a, cg_dt g <= a < cg_dt g + 1 ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a).
  { intros a Ha. apply (ctx_mbyte_kept _ (ss_mem ctx_ss0) _ _ a HFr).
    - destruct Hdtdst as (Hq0 & Hq63 & _). lia.
    - apply (HNOTW (cg_dt g) 1 a); [exact (proj1 (proj2 (proj2 Hdtdst))) | lia]. }
  split.
  { rewrite R10.
    rewrite sv_denot_SOff0. change 45%nat with (33 + 12)%nat.
    rewrite (cw_ew_x (cg_regs g) (ctx_xs F FL regs2) 12%nat).
    cbn [nth ctx_xs ctx_regs32]. rewrite Z_to_bv_bv_unsigned. exact Hr10. }
  split.
  { intros Hz0. destruct (Hzero Hz0) as (Hsg & Hdt).
    pose proof (ctx_spec_len (cg_tb g) res sres dres Espec Hz0) as Hlen. split.
    - apply (garr8_frame tfibsegs (mrestrict (w_H W2) mem2)); [exact Hsg|].
      intros a Ha. rewrite Hlen in Ha. cbn [Z.of_nat] in Ha. apply HSEGK. lia.
    - apply (ctx_val_mem_kept (mrestrict (w_H W2) mem2)); [|exact Hdt].
      intros k Hk. apply HDTK. lia. }
  { intros Hnz0. destruct (Hnz Hnz0) as (s' & d' & Hsg & Hlen & Hdt).
    exists s', d'. split.
    - apply (garr8_frame tfibsegs (mrestrict (w_H W2) mem2)); [exact Hsg|].
      intros a Ha. rewrite Hlen in Ha. cbn [Z.of_nat] in Ha. apply HSEGK. lia.
    - split; [exact Hlen|].
      apply (ctx_val_mem_kept (mrestrict (w_H W2) mem2)); [|exact Hdt].
      intros k Hk. apply HDTK. lia. }
Time Qed.
End h.
End d.
