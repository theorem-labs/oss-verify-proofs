(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 470 of its 496 lines of code are new or changed and 223 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_head_mid.v, with its module names changed; 160 of its 202 lines of code are new or changed and 454 lines of the source are left out. *)
(* LATCH 0x82df4-0x82e5c of the image-B walk of LLVMFuzzerTestOneInput, 27 instructions, no call: k's 23 shadow
   bytes (shadow offsets 24 .. 46 of the frame) are set to 0xf8 (marked unusable) through s2 = shadow_addr F and
   s11 = -8, ops + 1 (0x82e44 addiw s4,s4,1) and the pass test (0x82e58 beq s4,256): to EXIT at 0x83530 after 256
   passes, else back to HEAD at 0x80c30 (0x82e5c j). This is lib/AU/Prog/codec_bmain_inv.v's seg_latch, proved
   end to end with the entry and exit bridges of lib/AU/Prog/codec_bmain_st.v (bm_entry, bm_exit, bm_mcut): it
   adds one region (the frame's 60 shadow bytes, writable over k's 23) and one atom fact (s4 = ops in [0, 255]),
   runs the shadow-store engine once, splits the pass test, and reads the new shadow bytes back out of the region.
   No call, so no callee or runtime contract is a premise. No UBSan trap edge lies in 0x82df4-0x82e5c: none of
   codec_bmain_inv.v's lists bm_trap_taken / bm_trap_inpp / bm_trap_other has a pc in the range, and
   bm_trap_complete shows no other branch or jump of the function reaches the trap. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkFrameU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the one region the segment adds: the frame's 60 shadow bytes as the cut leaves them (k's 23 at 0), writable
   over k's 23; the one atom fact: s4 = ops in [0, 255] *)
Definition bl_regs : smem := [bm_shadow_region 24 47 bm_shm0].
Definition bl_AF : list (nat * afact) := [(20%nat, mkAF 0 255 0)].

(* the write premise of a run: every base region read-only but the cursor (the walk's stack window), and k's
   shadow bytes (the frame's own) *)
Ltac bl_awr sp1v posv U2 U34 EFA :=
idtac; cw_awrA; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1v - sp0));
  [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U2; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 posv 34%nat);
  [reflexivity | rewrite EFA; rewrite ?ew_ewset_other by lia; rewrite U34; reflexivity | left; reflexivity
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |] ] end.
(* the zone of those windows: the cursor and k's 23 shadow bytes *)
Ltac bl_kwr U2 U34 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
    rewrite ?U2, ?U34 in Hb; first [left; lia | right; lia | lia] | ]);
destruct Hr.
(* the stopped state as the configuration of a cut *)
Ltac bl_shape W2 HS pc :=
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
  assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
  rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
(* one 8-byte field of the cursor (the region at index 4), at offset od of the window, as the atom at_ plus kk *)
Ltac bl_cur W2 HS sp1v U2 od at_ kk v ewl :=
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 4 r HS ltac:(vm_compute; reflexivity)) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    apply (field_of_region Ev (mrestrict (w_H W2) (ms_mem msx)) n sp1v cs lo hi wlo whi od 8 (SOff at_ kk) v HR);
    [ rewrite ?ew_ewset_other by lia; rewrite U2; reflexivity
    | cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite (bm_den_off Ev at_ _ kk ltac:(rewrite ?ew_ewset_other by lia; exact ewl))
        by (unfold BM_HI in *; lia); f_equal; lia
    | unfold BM_HI in *; cbn; lia
    | cbn; lia ] end end.
(* a register of the stopped state, by its expression *)
Ltac bl_reg HS r W2 :=
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  etransitivity; [exact (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx r HS)|];
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end.
(* the frame's 60 shadow bytes, read back out of the region the run wrote (index 5: after bm_regs' five) *)
Ltac bl_shadow W2 HS g pos U34 :=
intros i Hi; rewrite <- bm_shm8_eq;
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
  apply (bm_sh_read_all Ev W2 (ms_mem msx) r (shadow_addr (FA g pos)) bm_shm8);
  [ exact (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 5 r HS ltac:(vm_compute; reflexivity))
  | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; rewrite U34; reflexivity
  | vm_compute; reflexivity
  | vm_compute (Z.of_nat (length bm_shm8)); lia ] end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Theorem seg_latch_holds : seg_latch B MT K XM_LIB.
Proof using TL LAWS ML.
unfold seg_latch. intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur)).
assert (Ek : k = 0) by (unfold EV_LIB in Hk; lia). subst k.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold BM_HI in Hchi, Hpng.
destruct Hops as (Hops1 & Hops2). pose proof Hcur as (Hc & C184 & C192).
pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & _).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
assert (D2 : 512 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : FA g pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (D3 : 8 * (FA g pos / 8) <= FA g pos) by (apply Z.mul_div_le; lia).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, SB; lia).
(* the frame and its shadow bytes do not meet: the frame lies in one of the two application bands *)
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (HE33 : ew (bm_env g pos c regs2 []) 33 = Z_to_bv 64 (FA g pos)) by exact (bm_ew_F g pos c regs2 []).
assert (HE34 : ew (bm_env g pos c regs2 []) 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by exact (bm_ew_SH g pos c regs2 []).
assert (HE35 : ew (bm_env g pos c regs2 []) 35 = Z_to_bv 64 (e_p g + c)) by exact (bm_ew_CP g pos c regs2 []).
assert (HE36 : ew (bm_env g pos c regs2 []) 36 = Z_to_bv 64 (e_n g - c)) by exact (bm_ew_CN g pos c regs2 []).
assert (HE2 : ew (bm_env g pos c regs2 []) 2 = getr regs2 2) by exact (bm_ew_reg g pos c regs2 [] 2 2%bv eq_refl).
assert (HE20 : ew (bm_env g pos c regs2 []) 20 = Z_to_bv 64 ops)
  by (rewrite (bm_ew_reg g pos c regs2 [] 20 20%bv eq_refl), Hops2; reflexivity).
assert (U2 : bv_unsigned (ew (bm_env g pos c regs2 []) 2) = sp1)
  by (rewrite HE2; pose proof HC as (_ & _ & R2 & _); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (bm_env g pos c regs2 []) 34) = shadow_addr (FA g pos))
  by (rewrite HE34; apply unsigned_lit_small; unfold SB in Hsh; lia).
assert (HAF : atoms_ok (bm_env g pos c regs2 []) bl_AF).
{ unfold bl_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite HE20. rewrite unsigned_lit_small by lia. rewrite ?Z.pow_0_r, ?Z.mod_1_r. repeat split; lia. }
assert (HRS : Forall (region_ok tfibsegs (bm_env g pos c regs2 []) (mrestrict (w_H W2) mem2)) bl_regs).
{ unfold bl_regs. constructor; [|constructor]. rewrite bm_shm0_eq.
  exact (bm_shadow_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c [] 24 47
           HJ Hfr HC ltac:(lia) ltac:(lia)). }
assert (HAP : Forall (fun r => all_disjoint (bm_env g pos c regs2 []) r bm_regs) bl_regs).
{ unfold bl_regs, bm_regs, bm_regs0, cw_regs, bm_shadow_region, bm_spill_region, bm_cur_region,
         stack_region, got_region, bcell_region.
  constructor; [|constructor].
  cbn [app all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U34.
  unfold A_GOT_shadow, A_shadow_glob, SB in *. repeat split; lia. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c PC_LATCH []
  bl_regs bl_AF HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) HRS
  ltac:(cbn; repeat split; exact I) HAP HAF) as HS.
pose proof HJ as HJR.
assert (HAE0 : env_agree 35 (bm_env g pos c regs2 []) (bm_env g pos c regs2 [])) by apply env_agree_refl.
(* what the segment may write: the cursor's window (it writes none of it) and k's 23 shadow bytes *)
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((sp1 + 184 <= a < sp1 + 200) \/ (shadow_addr (FA g pos) + 24 <= a < shadow_addr (FA g pos) + 47)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 PC_LATCH) with (Z_to_bv 64 PC_LATCH).
(* 0x82df4-0x82e54: the 23 shadow stores, ops + 1, li a0,256; the engine stops at the pass test *)
aj_run_sh tfibtbl_lib_ok HS HJR. { bl_awr sp1 pos U2 U34 EFA. }
cw_ajA HJR.
cw_keep ltac:(bl_kwr U2 U34).
(* 0x82e58 beq s4,a0: the pass test on ops + 1 = 256 *)
srr_branch_sh tfibtbl_lib_ok HS.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hcond end.
all: rewrite branch_eq_U in Hcond.
all: rewrite (U_atom_off _ 20%nat ops 1 ltac:(rewrite ?ew_ewset_other by lia; exact HE20) ltac:(lia) ltac:(lia)) in Hcond.
all: rewrite U_lit in Hcond by lia.
- (* taken: ops + 1 = 256, to EXIT at 0x83530 *)
  apply Z.eqb_eq in Hcond.
  aj_run_to_sh tfibtbl_lib_ok HS HJR PC_EXIT. { bl_awr sp1 pos U2 U34 EFA. }
  cw_ajA HJR.
  cw_keep ltac:(bl_kwr U2 U34).
  bl_shape W2 HS PC_EXIT.
  apply SRr_ret. left. split; [lia|].
  unfold inv_exit.
  eapply bm_mcut; [exact HJR | exact Hfr | lia | exact Hmo | | exact I].
  eapply (bm_exit B MT K XM_LIB LAWS);
  [ exact HC | exact HJR | idtac | exact HS | vm_compute; reflexivity
  | intros a Ha; unfold bm_keepzone in Ha; apply KE;
    [unfold shadow_addr, SHADOW_OFF, SB in *; lia
    | intros [Hz | Hz]; unfold shadow_addr, SHADOW_OFF, SB in *; lia]
  | bl_shadow W2 HS g pos U34
  | exact HPerm0 ].
  env_agree_chain HAE0.
- (* not taken: ops + 1 <> 256, the jump back to HEAD at 0x80c30 *)
  apply Z.eqb_neq in Hcond.
  aj_run_to_sh tfibtbl_lib_ok HS HJR PC_HEAD. { bl_awr sp1 pos U2 U34 EFA. }
  cw_ajA HJR.
  cw_keep ltac:(bl_kwr U2 U34).
  bl_shape W2 HS PC_HEAD.
  apply SRr_ret. right. split; [lia|].
  unfold inv_head.
  eapply bm_mcut; [exact HJR | exact Hfr | lia | exact Hmo | |].
  + eapply (bm_exit B MT K XM_LIB LAWS);
    [ exact HC | exact HJR | idtac | exact HS | vm_compute; reflexivity
    | intros a Ha; unfold bm_keepzone in Ha; apply KE;
      [unfold shadow_addr, SHADOW_OFF, SB in *; lia
      | intros [Hz | Hz]; unfold shadow_addr, SHADOW_OFF, SB in *; lia]
    | bl_shadow W2 HS g pos U34
    | exact HPerm0 ].
    env_agree_chain HAE0.
  + split.
    * split; [lia|].
      bl_reg HS (20%bv : bv 5) W2.
      rewrite (bm_den_off _ 20 ops 1 ltac:(rewrite ?ew_ewset_other by lia; exact HE20)) by lia.
      reflexivity.
    * exists c. unfold cur_at. split; [exact Hc|]. split.
      -- bl_cur W2 HS sp1 U2 184 35%nat 0 (e_p g + c) HE35.
      -- bl_cur W2 HS sp1 U2 192 36%nat 0 (e_n g - c) HE36.
Qed.
End d.
End b.
