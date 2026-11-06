(* LATCH 0x8275c-0x827c4, 27 instructions, no call: k's 23 shadow bytes are set to 0xf8 (marked unusable) through
   s2 = shadow_addr F, ops + 1 (0x827ac addiw s10,s10,1) and the pass test (0x827c0 beq s10,256): to EXIT at
   0x82f94 after 256 passes, else back to HEAD at 0x80abc. This is lib/A/Prog/codec_amain_inv.v's seg_latch,
   proved end to end with the entry and exit bridges of lib/A/Prog/codec_amain_st.v: it adds one region (the
   frame's 56 shadow bytes, writable over k's 23), runs the shadow-store engine once, splits the pass test, and
   reads the new shadow bytes back out of the region. No call, so no callee contract is a premise. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the one region the segment adds: the frame's shadow bytes, writable over k's 23 of them *)
Definition lt_regs : smem := [am_shadow_region 22 45 am_shm0].
Definition lt_AF : list (nat * afact) := [(26%nat, mkAF 0 255 0)].

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


(* the write premise of a run: the base regions are read-only, the cursor is the walk's stack window and k's
   shadow bytes are the frame's own *)
Ltac lt_awr sp1 pos EFA U2 U34 :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1 - sp0)) end;
  [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |];
  eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 pos 34%nat);
  [reflexivity | rewrite EFA, U34; reflexivity | left; reflexivity
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |];
  apply awr_ok_nil.
(* the zone of those windows *)
Ltac lt_kwr U2 U34 :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2, ?U34 in Hb;
      first [left; lia | right; lia | lia] | ]);
  destruct Hr.
(* the stopped state as a configuration of the cut *)
Ltac lt_shape W2 HS pc :=
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
    assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
    rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
Ltac lt_cut HJ Hfr Hmo := eapply am_mcut; [exact HJ | exact Hfr | lia | exact Hmo | | ].
(* the frame's 56 shadow bytes, read back out of the region the run wrote *)
Ltac lt_shadow W2 HS g pos U34 :=
  intros i Hi; rewrite <- am_shm8_eq;
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
    apply (am_sh_read_all Ev W2 (ms_mem msx) r (shadow_addr (FA g pos)) am_shm8);
    [ exact (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 5 r HS ltac:(vm_compute; reflexivity))
    | cbn [YP09.r_base base_val]; rewrite U34; reflexivity
    | vm_compute; reflexivity
    | vm_compute (Z.of_nat (length am_shm8)); lia ] end.
(* one 8-byte field of the cursor *)
Ltac lt_cur W2 HS sp1 U2 od at_ v ewl inl :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 4 r HS ltac:(vm_compute; reflexivity)) as HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      apply (field_of_region Ev (mrestrict (w_H W2) (ms_mem msx)) n sp1 cs lo hi wlo whi od 8 (SOff at_ 0) v HR);
      [ rewrite U2; reflexivity
      | cbn [In]; inl
      | cbn [sv_denot]; rewrite ewl, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold AM_HI in *; cbn; lia
      | cbn; lia ] end end.
(* mcommon at the end cut *)
Ltac lt_mcommon B MT K XM_LIB LAWS HC HJ HS KE W2 g pos U34 HPerm0 :=
  eapply (am_exit B MT K XM_LIB LAWS);
  [ exact HC | exact HJ | apply env_agree_refl | exact HS | vm_compute; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; unfold am_keepzone in Ha; apply KE;
    [ unfold SB in *; lia | let Hz := fresh "Hz" in intros [Hz | Hz]; unfold SB in *; lia ]
  | lt_shadow W2 HS g pos U34
  | exact HPerm0 ].

Theorem seg_latch_holds : seg_latch B MT K XM_LIB.
Proof using TL LAWS ML.
unfold seg_latch. intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C152 & C160).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
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
assert (HE33 : ew (am_env g pos c regs2 []) 33 = Z_to_bv 64 (FA g pos)) by exact (am_ew_F g pos c regs2 []).
assert (HE34 : ew (am_env g pos c regs2 []) 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by exact (am_ew_SH g pos c regs2 []).
assert (HE2 : ew (am_env g pos c regs2 []) 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = Z_to_bv 64 ops)
  by (rewrite (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl), Hops2; reflexivity).
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite HE2; pose proof HC as (_ & _ & R2 & _); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (am_env g pos c regs2 []) 34) = shadow_addr (FA g pos))
  by (rewrite HE34; apply unsigned_lit_small; unfold SB in Hsh; lia).
assert (HAF : atoms_ok (am_env g pos c regs2 []) lt_AF).
{ unfold lt_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite HE26. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (HRS : Forall (region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2)) lt_regs).
{ unfold lt_regs. constructor; [|constructor]. rewrite am_shm0_eq.
  exact (am_shadow_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c [] 22 45
           HJ Hfr HC ltac:(lia) ltac:(lia)). }
assert (HAP : Forall (fun r => all_disjoint (am_env g pos c regs2 []) r am_regs) lt_regs).
{ unfold lt_regs, am_regs, am_regs0, cw_regs, am_shadow_region, am_spill_region, am_cur_region,
         stack_region, got_region, bcell_region.
  constructor; [|constructor].
  cbn [app all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U34.
  unfold A_GOT_shadow, A_shadow_glob, SB in *.
  repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c PC_LATCH [] lt_regs lt_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) HRS ltac:(cbn; repeat split; exact I) HAP HAF) as HS.
unfold cfg_at. change (w64 PC_LATCH) with (Z_to_bv 64 PC_LATCH).
(* what the segment writes: the cursor's window (it writes none of it) and k's 23 shadow bytes *)
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((sp1 + 152 <= a < sp1 + 168) \/ (shadow_addr (FA g pos) + 22 <= a < shadow_addr (FA g pos) + 45)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
(* 0x8275c-0x827bc: the 23 shadow stores, ops + 1, li a0,256; stop at the pass test *)
aj_run_sh tfibtbl_lib_ok HS HJ.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - e_sp0 g));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 pos 34%nat);
    [reflexivity | rewrite EFA, U34; reflexivity | left; reflexivity
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |].
  apply awr_ok_nil. }
cw_keep ltac:(idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2, ?U34 in Hb;
      first [left; lia | right; lia | lia] | ]);
  destruct Hr).
(* 0x827c0 beq s10,a0: the pass test *)
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => idtac | _ => idtac end.
srr_branch_sh tfibtbl_lib_ok HS.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hcond end.
all: rewrite branch_eq_U in Hcond.
all: rewrite (U_atom_off _ 26%nat ops 1 HE26 ltac:(lia) ltac:(lia)) in Hcond.
all: rewrite U_lit in Hcond by lia.
- (* taken: ops + 1 = 256, to EXIT at 0x82f94 *)
  apply Z.eqb_eq in Hcond.
  aj_run_to_sh tfibtbl_lib_ok HS HJ PC_EXIT. { lt_awr sp1 pos EFA U2 U34. }
  cw_keep ltac:(lt_kwr U2 U34).
  lt_shape W2 HS PC_EXIT.
  apply SRr_ret. left. split; [lia|].
  unfold inv_exit. lt_cut HJ Hfr Hmo.
  + lt_mcommon B MT K XM_LIB LAWS HC HJ HS KE W2 g pos U34 HPerm0.
  + exact I.
- (* not taken: ops + 1 <> 256, the jump back to HEAD at 0x80abc *)
  apply Z.eqb_neq in Hcond.
  aj_run_to_sh tfibtbl_lib_ok HS HJ PC_HEAD. { lt_awr sp1 pos EFA U2 U34. }
  cw_keep ltac:(lt_kwr U2 U34).
  lt_shape W2 HS PC_HEAD.
  apply SRr_ret. right. split; [lia|].
  unfold inv_head. lt_cut HJ Hfr Hmo.
  + lt_mcommon B MT K XM_LIB LAWS HC HJ HS KE W2 g pos U34 HPerm0.
  + split.
    * split; [lia|].
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (26%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (26%bv : bv 5)) with (SOff 26 1).
      rewrite (am_den_off _ 26%nat ops 1 HE26 ltac:(lia) ltac:(lia)). reflexivity.
    * exists c. unfold cur_at. split; [exact Hc|]. split.
      -- lt_cur W2 HS sp1 U2 152 35%nat (e_p g + c) (am_ew_CP g pos c regs2 []) ltac:(left; reflexivity).
      -- lt_cur W2 HS sp1 U2 160 36%nat (e_n g - c) (am_ew_CN g pos c regs2 []) ltac:(right; left; reflexivity).
Qed.
End d.
End b.
