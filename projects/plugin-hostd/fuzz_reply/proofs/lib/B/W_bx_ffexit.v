(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image B's lx_ffexit (lib/B/W_bx_defs.v lx_ffexit_S), the fake frame's release
   and the epilogue of fuzz_reply.asan-ubsan's LLVMFuzzerTestOneInput, 0x85014 .. the ret 0x850f8; the port of the A
   donor b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v :99-125 (ss_ffexit) and
   :7421-7645 (lx_ffexit).  B's block, read from the objdump of fuzz_reply.asan-ubsan (sha256
   10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c):
     85014 lui a0,0x45e03; 85018 addiw a0,a0,1550     the retired-frame magic 0x45e0360e
     8501c ld a1,104(s1); 85020 sd a0,0(a1)           THE ONE DIFFERENCE FROM A: B stores the magic through FF read
                                                      back from the frame cell F+104 (A: `sd a0,0(s7)`, FF in s7)
     85024 beqz s4,85078                              decided: s4 = FF >= 4096
     85028 li a0,-11; 8502c..85068 16 x sb a0,k(s8)   the 0xf5 poison of the 16 shadow bytes at SB + FF/8
     8506c ld a0,120(s4); 85070 sb zero,0(a0)         the flag clear through the flag pointer at FF+120
     85074 j 850b8; 850b8 li a0,0; 850bc addi sp,s0,-320; 13 x ld from sp+312 .. sp+216; addi sp,sp,320; ret
   So the entry state has one more region than the donor's, F+104 (base s1 = atom 9) whose chunk is FF (atom 20), and
   FF's header word and flag pointer word are ONE region based at s4 (atom 20): [0,128) with the write window [0,8)
   and the chunk FL at 120 (the donor had them at two atoms, s7 and s4).  Everything after the magic store is the
   donor's code instruction for instruction (B's saved-register slots below s0 are the cut's saved_regs, as A's). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites W_bx_defs.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the entry symbolic state at 0x85014
   One flag run walks the whole block.  Regions: the flag byte (atom 32 = FL; first, where the flag run's last
   obligation reads it), the fake frame FF (s4 = atom 20: the header word written, the flag pointer word read), the
   frame cell F+104 (s1 = atom 9, read: it holds FF), the 16 shadow bytes (s8 = atom 24, written) and the saved
   registers below s0 (atom 8, read; their values are the extra atoms 33..45 = c_regs cx's ra, s0, s1, s2..s11). *)
Definition bfx_PTR : afact := mkAF 4096 140737488355328 0.       (* [4096, 2^47] *)
Definition bfx_saved : list YP09.chunk :=
  [ YP09.mkChunk (-8)   (CVal 8 (SOff 33 0)); YP09.mkChunk (-16)  (CVal 8 (SOff 34 0));
    YP09.mkChunk (-24)  (CVal 8 (SOff 35 0)); YP09.mkChunk (-32)  (CVal 8 (SOff 36 0));
    YP09.mkChunk (-40)  (CVal 8 (SOff 37 0)); YP09.mkChunk (-48)  (CVal 8 (SOff 38 0));
    YP09.mkChunk (-56)  (CVal 8 (SOff 39 0)); YP09.mkChunk (-64)  (CVal 8 (SOff 40 0));
    YP09.mkChunk (-72)  (CVal 8 (SOff 41 0)); YP09.mkChunk (-80)  (CVal 8 (SOff 42 0));
    YP09.mkChunk (-88)  (CVal 8 (SOff 43 0)); YP09.mkChunk (-96)  (CVal 8 (SOff 44 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45 0)) ].
Definition bfx_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 20%nat) 0 128 0 8 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 104 112 0 0 [YP09.mkChunk 104 (CVal 8 (SOff 20 0))];
    YP09.mkRegion (Some 24%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 bfx_saved ].
Definition bfx_facts : facts :=
  mkFacts [ (20%nat, bfx_PTR); (24%nat, mkAF SB (SB + 17592186044416) 0); (32%nat, bfx_PTR) ] [] [].
Definition ss_bffexit : sstate := mkSS AX_ffexit sr_atoms bfx_regions None bfx_facts.
(* the entry environment's extra atoms: 32 = FL, 33..45 = the caller's ra, s0, s1, s2..s11 *)
Definition bfx_extra (cr : bvmap 5 word) (FL : Z) : list word :=
  [ Z_to_bv 64 FL; getr cr 1; getr cr 8; getr cr 9; getr cr 18; getr cr 19; getr cr 20; getr cr 21; getr cr 22;
    getr cr 23; getr cr 24; getr cr 25; getr cr 26; getr cr 27 ].

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.

Lemma lx_ffexit : lx_ffexit_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Proof.
  unfold lx_ffexit_S.
  intros cx W regs mem md ly3 S3 k fpos FF _ HFFeq HJ HFR HFLw Hs0 Hs9 Hs4 Hs8 Hgp Htp HRA.
  pose (RUNF := aj_flag_store_pi (PL := PL_fr) (PI := PB_fr) B LAWS ML ASF FFL).
  pose (RET := paj_ret_at (PL := PL_fr) (PI := PB_fr)).
  pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & _ & _ & _ & _).
  assert (KSB : SB = 2147450880) by reflexivity.
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (KHM : kHighMemBeg = 17594333495296) by reflexivity.
  (* unpack the gx journal to the bare ajournal over memS *)
  destruct HJ as (HSTK & HXO & (memS & HJbare & Hag) & Hout).
  rewrite !Z.add_0_r in HJbare.
  pose proof (proj1 HJbare) as HAR.
  pose proof HJbare as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* the fake frame, its shadow and its flag *)
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin) as (HF4096 & HFceil & HFinapp).
  destruct (al_frames _ _ LAWS ly3 S3 W mem md 1 fpos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
  destruct (FFL ly3 S3 W mem md 1 fpos HAR Hin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  rewrite <- HFFeq in *.
  destruct HFR as (HSV & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF104 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSw).
  (* the entry sp's bounds *)
  pose proof HJbare as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  destruct Hastk as (Hsp16 & _ & Hstklo & Hstklo2 & Hsphi & Hstkhi2 & _ & _ & _).
  unfold LLVMF_STK in Hstklo2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FL := flag_addr ly3 1 fpos) in *.
  assert (Hsp0lo : alloc_ceiling + 32768 <= sp0) by lia.
  assert (Hsp0hi : sp0 <= 2 ^ 47) by lia.
  (* the frame base F = s1: 320 to 351 below sp0 *)
  set (F := lf_F cx) in *.
  assert (HFb : sp0 - 352 < F <= sp0 - 320).
  { unfold F, lf_F. fold sp0. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)). lia. }
  unfold in_app, ASAN_CEIL in HFapp. unfold app_addr, ASAN_CEIL in HFLapp.
  assert (HFLnf : ~ (FF <= FL < FF + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLown)).
  assert (HFLnsh : ~ (SB + FF / 8 <= FL < SB + FF / 8 + 16)).
  { intros Hx. apply (proj2 (HFSpres (FL - (SB + FF / 8)) ltac:(lia))).
    unfold shadow_addr. rewrite <- SB_SHADOW_OFF. replace (SB + FF / 8 + (FL - (SB + FF / 8))) with FL by lia.
    exact HFLown. }
  assert (HF8 : 512 <= FF / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  pose proof (Z.mul_div_le FF 8 ltac:(lia)) as HF8a.   (* lia here sees FF / 8 as an atom *)
  (* the entry environment: the registers, FL at 32, the saved values at 33..45 *)
  remember (Eimg (Ereg regs (bfx_extra (c_regs cx) FL))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (EXj : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (bfx_extra (c_regs cx) FL) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E32 : ew E 32 = Z_to_bv 64 FL) by exact (EXj 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = getr (c_regs cx) 1) by exact (EXj 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (c_regs cx) 8) by exact (EXj 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = getr (c_regs cx) 9) by exact (EXj 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = getr (c_regs cx) 18) by exact (EXj 4%nat ltac:(lia)).
  assert (E37 : ew E 37 = getr (c_regs cx) 19) by exact (EXj 5%nat ltac:(lia)).
  assert (E38 : ew E 38 = getr (c_regs cx) 20) by exact (EXj 6%nat ltac:(lia)).
  assert (E39 : ew E 39 = getr (c_regs cx) 21) by exact (EXj 7%nat ltac:(lia)).
  assert (E40 : ew E 40 = getr (c_regs cx) 22) by exact (EXj 8%nat ltac:(lia)).
  assert (E41 : ew E 41 = getr (c_regs cx) 23) by exact (EXj 9%nat ltac:(lia)).
  assert (E42 : ew E 42 = getr (c_regs cx) 24) by exact (EXj 10%nat ltac:(lia)).
  assert (E43 : ew E 43 = getr (c_regs cx) 25) by exact (EXj 11%nat ltac:(lia)).
  assert (E44 : ew E 44 = getr (c_regs cx) 26) by exact (EXj 12%nat ltac:(lia)).
  assert (E45 : ew E 45 = getr (c_regs cx) 27) by exact (EXj 13%nat ltac:(lia)).
  assert (U8 : bv_unsigned (ew E 8) = sp0)
    by (rewrite (EEo 8%nat 8%bv eq_refl), Hs0; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F)
    by (rewrite (EEo 9%nat 9%bv eq_refl), Hs9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = FF)
    by (rewrite (EEo 20%nat 20%bv eq_refl), Hs4; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = SB + FF / 8)
    by (rewrite (EEo 24%nat 24%bv eq_refl), Hs8; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
  (* a saved register's chunk below s0 *)
  assert (SVC : forall (n : nat) (r : bv 5) o, ew E n = getr (c_regs cx) r -> In (o, bv_unsigned r) saved_regs ->
    YP09.chunk_ok segs E (mrestrict (w_H W) mem) sp0 (YP09.mkChunk (- o) (CVal 8 (SOff n 0)))).
  { intros n r o En Hor.
    apply (chunk_ok_val segs E _ sp0 (- o) 8 (SOff n 0) (bv_unsigned (getr (c_regs cx) r))).
    - cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia.
    - pose proof (HSV o (bv_unsigned r) Hor) as X. rewrite Z_to_bv_bv_unsigned in X.
      replace (sp0 + - o) with (sp0 - o) by lia. exact X. }
  (* the entry st_ok_pi *)
  unfold cfg_at. change (w64 (BASE + AX_ffexit)) with (Z_to_bv 64 (BASE + AX_ffexit)).
  assert (HS : st_ok_pi segs VAL E ss_bffexit
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_ffexit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_bffexit. apply pa_entry_st_ok_full.
    - subst E; apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - unfold bfx_regions, bfx_saved. repeat apply Forall_cons; try apply Forall_nil;
        unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + (* the flag byte *)
        rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HFLpres.
      + (* FF: the header word written, the flag pointer word read *)
        rewrite U20. split; [lia|]. split; [lia|]. split.
        * intros o Ho. apply (apresent_writable segs). exact (proj1 (HFpres (FF + o) ltac:(lia))).
        * constructor; [|constructor].
          apply (chunk_ok_val segs E _ FF 120 8 (SOff 32 0) FL).
          -- cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
          -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
          -- cbn. lia.
          -- exact HFLw.
      + (* the frame cell F+104, which holds FF *)
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 104 8 (SOff 20 0) FF).
        * cbn [sv_denot]. rewrite U20, Z.add_0_r. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * exact HF104.
      + (* the frame's 16 shadow bytes *)
        rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HFSw o Ho).
      + (* the saved registers below s0 *)
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        all: lazymatch goal with
             | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
               lazymatch goal with En : ew _ n = getr _ ?r |- _ =>
                 exact (SVC n r (- off) En ltac:(cbn [In saved_regs]; repeat first [left; reflexivity | right]))
               end
             end.
    - apply pairwise_disjoint_of_extents.
      unfold bfx_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U8, U9, U20, U24, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok bfx_facts]. unfold afact_ok, bfx_PTR. cbn [af_lo af_hi af_al2].
      rewrite U20, U24, U32, !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia. }
  clear HE.
  (* the whole block: one flag run, 0x85014 .. the ret *)
  paj_run_flag_sh RUNF HS HJbare.
  { lia. }
  { intros a (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr. try change (flag_addr ly3 1 fpos) with FL.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U9, ?U20, ?U24, ?U32 in Hr;
        first [ exfalso; lia
              | right; lia
              | left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
                rewrite <- HFFeq; change (fs_frame_bytes 1) with 128;
                first [ left; unfold in_zr; cbn [fst snd]; lia
                      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd];
                        change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hinr. }
  { intros msr HSr. try change (flag_addr ly3 1 fpos) with FL. ff_flag0_tac HSr U32. }
  (* at the ret: ra = the caller's ra (atom 33), sp = s0, s0..s11 = atoms 34..45, a0 = 0 *)
  prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
  prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (10%bv : bv 5) Rr10.
  prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19. prreg HS (20%bv : bv 5) Rr20.
  prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
  prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26.
  prreg HS (27%bv : bv 5) Rr27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split.
  { unfold cfg_at. rewrite Rr1, E33, HRA. reflexivity. }
  split.
  { eapply (ajournal_gx_pack segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [] ly3 (stack_free_state 1 fpos S3) W _ _ k memS).
    - exact HSTK.
    - lia.
    - rewrite !Z.add_0_r. apply (ajournal_materialize segs B LAWS Hsegs). exact HJbare.
    - exact Hag.
    - intros a Ha. lia. }
  split.
  { apply aregs_preserved_eqs.
    - rewrite Rr2, (EEo 8%nat 8%bv eq_refl), Hs0. apply Z_to_bv_bv_unsigned.
    - rewrite Rr3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rr4, (EEo 4%nat 4%bv eq_refl). exact Htp.
    - rewrite Rr8. exact E34.
    - rewrite Rr9. exact E35.
    - rewrite Rr18. exact E36.
    - rewrite Rr19. exact E37.
    - rewrite Rr20. exact E38.
    - rewrite Rr21. exact E39.
    - rewrite Rr22. exact E40.
    - rewrite Rr23. exact E41.
    - rewrite Rr24. exact E42.
    - rewrite Rr25. exact E43.
    - rewrite Rr26. exact E44.
    - rewrite Rr27. exact E45. }
  split.
  { rewrite Rr10. reflexivity. }
  split.
  { (* the run wrote only its windows: FF's header word, the 16 shadow bytes, the flag byte *)
    intros a Ha Hn1 Hn2 Hn3. change (flag_addr ly3 1 fpos) with FL in Hn3.
    lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (aview_kept_out _ _ _ _ _ HFx a Ha) end.
    intros (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U9, ?U20, ?U24, ?U32 in Hr; lia | ]).
    destruct Hinr. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => exact Hg end.
Qed.
End lx.
